import AcceleratedLogConcave.Numerics.SmoothConditionalMeanBudget

/-! A finite original-data bound for the exact common-seed initializer. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.MeanCollocationLp
open Numerics.AffineGraph Numerics.AffineGraph.MeanGeometry
open Numerics.SmoothReferenceDisplacement Numerics.SmoothConditionalMeanBudget
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.SmoothInitialDisplacementBound
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def centerMove (d : Data ι m) (j : Fin m) : ℝ :=
  |centerNode j| * ((d.sigma / 2)⁻¹ *
    CenteringFlowLp.alpha (kernelData d) * backwardEnd d.G.R *
    Real.sqrt (Module.finrank ℝ E))

def backwardMove (d : Data ι m) (j : Fin m) (a : ℝ) : ℝ :=
  centerMove d j + d.r * |a - backwardEnd d.G.R| *
    (meanBudget d + Real.exp 1 * (d.r * d.ell) *
      Real.sqrt (Module.finrank ℝ E))

def scoreMove (d : Data ι m) (j : Fin m) : ℝ :=
  |centerNode j| * ((d.sigma / 2)⁻¹ *
    CenteringFlowLp.alpha (kernelData d) *
    Real.sqrt (Module.finrank ℝ E))

def forwardMove (d : Data ι m) (j : Fin m) (ρ : d.G.Kernel)
    (z : Fin m) (a : ℝ) : ℝ :=
  backwardMove d j (d.G.rho ρ) + d.G.angleNode z * scoreMove d j +
    d.G.seedRot ρ (d.G.angleNode z) *
      ((d.r * Real.sqrt (d.G.variance ρ)) *
        (|conditionalEnd| * conditionalMeanBudget d j ρ)) +
    d.r * |a - d.G.rho ρ| *
      (meanBudget d + Real.exp 1 * (d.r * d.ell) *
        Real.sqrt (Module.finrank ℝ E))

/-- Each finite graph node carries an explicit coefficient of the original
physical radius. No term contains the reference graph or its error. -/
def rowCoefficient (d : Data ι m) : d.G.MeanNode → ℝ
  | .base _ => 0
  | .center _ j => backwardEnd d.G.R * centerMove d j
  | .backward _ j i => d.G.backward.location m i *
      backwardMove d j (d.G.backward.location m i)
  | .conditional _ j ρ i =>
      d.G.rho ρ * backwardMove d j (d.G.rho ρ) +
      (Real.sqrt (d.G.variance ρ) * (d.G.conditional ρ).location m i) *
        ((d.r * Real.sqrt (d.G.variance ρ)) *
          |(d.G.conditional ρ).location m i| * conditionalMeanBudget d j ρ)
  | .forward _ j ρ z i =>
      (d.G.forward ρ).location m i *
        forwardMove d j ρ z ((d.G.forward ρ).location m i)

/-- Every exact reference row lies within `r` times its original-data
coefficient of the literal direct seed. -/
theorem row_displacement_le (d : Data ι m) (i : d.G.MeanNode) :
    ‖reference d i - (lpGraph d).direct i‖ ≤ d.r * rowCoefficient d i := by
  rcases i with u | j | ⟨j,k⟩ | ⟨j,ρ,k⟩ | ⟨j,ρ,z,k⟩
  · cases u
    change ‖reference d (.base d.G) - (lpGraph d).direct (.base d.G)‖ ≤
      d.r * rowCoefficient d (.base d.G)
    rw [base_eq_direct]
    simp [rowCoefficient, MeanNode.base]
  · have h := norm_center_sub_direct_le d j
    calc
      _ ≤ _ := h
      _ = _ := by dsimp [rowCoefficient, centerMove]; ring
  · have h := norm_backward_sub_direct_le_data d j k
    calc
      _ ≤ _ := h
      _ = _ := by dsimp [rowCoefficient, backwardMove, centerMove]; ring
  · have h := norm_conditional_sub_direct_le_data d j ρ k
    calc
      _ ≤ _ := h
      _ = _ := by dsimp [rowCoefficient, backwardMove, centerMove]; ring
  · have h := norm_forward_sub_direct_le_data d j ρ z k
    calc
      _ ≤ _ := h
      _ = _ := by
        dsimp [rowCoefficient, forwardMove, backwardMove, centerMove, scoreMove]
        ring

/-- The full exact initializer displacement is bounded by a finite explicit
original-data coefficient, with its physical radius still outside. -/
theorem norm_reference_sub_direct_le (d : Data ι m) :
    ‖reference d - (lpGraph d).direct‖ ≤ d.r * ‖rowCoefficient d‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg d.hr.le (norm_nonneg _))).mpr
  intro i
  have hi := row_displacement_le d i
  have hcoef : rowCoefficient d i ≤ ‖rowCoefficient d‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (rowCoefficient d) i))
  have hmul := mul_le_mul_of_nonneg_left hcoef d.hr.le
  simpa only [Pi.sub_apply] using hi.trans hmul

/-- The initializer in the actual finite iteration theorem is paid directly
by the exact-flow displacement, with the original physical factor `r`. -/
theorem initialError_le_data (d : Data ι m) :
    initialError d ≤ d.r * ‖rowCoefficient d‖ := by
  change ‖(lpGraph d).direct - reference d‖ ≤ _
  rw [norm_sub_rev]
  exact norm_reference_sub_direct_le d

end AcceleratedLogConcave.Numerics.SmoothInitialDisplacementBound
