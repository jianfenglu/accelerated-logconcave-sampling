import AcceleratedLogConcave.Numerics.CenterMeanPhaseOriginalDataReceiver
import AcceleratedLogConcave.Tensor.MaterialSmoothBranchesReceiver
import AcceleratedLogConcave.Numerics.SmoothConditionalForwardBudget
import AcceleratedLogConcave.Numerics.MeanSmoothCollocationLp

/-!
# Explicit quantitative assembly for the same-sample smooth receiver

Only the actual velocity and physical angle estimates remain analytic premises.
All other fields are supplied from original data. No ordinary endpoint
regularity of the legacy clipped receiver is asserted. The auxiliary primitive
constant is 128; the angle moment envelope uses its doubled value 256.
-/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SmoothQuantitativeAssembly
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph AffineGraph.MeanGeometry
open Analysis.PositiveVarianceSlab
variable {D m : ℕ}

/-- Fixed primitive budget constant, not a user-supplied derivative envelope. -/
def auxiliaryConstant : ℝ := 128

/-- Candidate velocity envelope on the actual common seed. Its analytic bound
is exactly the explicit `VelocityBounds` interface below. -/
def velocityBudget (d : Data (Fin D) m) : ℝ :=
  (d.r * d.ell / (d.sigma / 2)) ^ (m + 1) *
    Real.sqrt ((D + D : ℕ) * Tensor.AdjointReduction.PhaseBudget.Q auxiliaryConstant
      (5 * (m + 1) + 1)) / d.G.R ^ (2 * m + 1)

/-- Physical-angle envelope at positive collocation order. The factor 256 is
`2 * auxiliaryConstant`, as in the original-data angle supplier's bound. -/
def angleBudget (d : Data (Fin D) m) : ℝ :=
  2 * (d.r ^ 2 * d.ell) * d.G.R *
    Real.sqrt ((D + D : ℕ) * Tensor.AdjointReduction.PhaseBudget.Q
      (2 * auxiliaryConstant) (5 * m + 1)) * (2 / d.G.R ^ 2) ^ m

/-- Seven concrete components, including the original-data center envelope. -/
def budget (d : Data (Fin D) m) : AffineResidual.Mean.DerivativeBudget d.G where
  velocity := velocityBudget d
  center := centerSourceBudget d ((kernelData d).r * (kernelData d).ell)
    ((kernelData d).r * (kernelData d).ell) auxiliaryConstant d.G.R (m - 1)
  backward := fun _ => materialBackwardCellBudget d
  conditional := fun _ ρ => conditionalCellBudget d ρ
  forward := fun _ ρ _ => forwardCellBudget d ρ
  angle := fun _ _ => angleBudget d
  kernel := fun _ => materialKernelDerivativeBudget d (m + 2)

/-- The only unpaid velocity input: smoothness and a fixed explicit derivative
bound on `velocityLp d`, not on an unspecified receiver or alternate sample. -/
structure VelocityBounds (d : Data (Fin D) m) : Prop where
  smooth : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ m (velocityLp d) t
  bound : ∀ t ∈ Icc (0 : ℝ) 1,
    ‖iteratedDeriv m (velocityLp d) t‖ ≤ velocityBudget d

/-- The only unpaid angle input, on the actual common-seed physical action. -/
structure AngleBounds (d : Data (Fin D) m) : Prop where
  smooth : ∀ j k, ∀ z ∈ Icc (0 : ℝ) d.G.psi,
    ContDiffAt ℝ m (actionLp d j k) z
  bound : ∀ j k, ∀ z ∈ Icc (0 : ℝ) d.G.psi,
    ‖iteratedDeriv m (actionLp d j k) z‖ ≤ angleBudget d

theorem velocityBudget_nonneg (d : Data (Fin D) m) : 0 ≤ velocityBudget d := by
  have hr := d.hr.le
  have he := d.hell
  have hs := d.hsigma.le
  have hR := d.G.R_pos.le
  unfold velocityBudget
  positivity

theorem angleBudget_nonneg (d : Data (Fin D) m) : 0 ≤ angleBudget d := by
  have he := d.hell
  have hR := d.G.R_pos.le
  unfold angleBudget
  positivity

/-- The enlarged kernel slab has strict endpoint margins without an extra input. -/
theorem left_margin (d : Data (Fin D) m) : left (backwardEnd d.G.R) < 0 := by
  have hb := d.G.backwardEnd_lt_one
  unfold left
  linarith

theorem right_margin (d : Data (Fin D) m) : backwardEnd d.G.R < right (backwardEnd d.G.R) := by
  have hb := d.G.backwardEnd_lt_one
  unfold right
  linarith

/-- Whole-function center identity; no derivative is transferred merely from
closed-slab agreement. The smooth replacement leaves this field unchanged. -/
theorem center_function_eq (d : Data (Fin D) m) :
    (curvesWithSmoothBranches d).centerMean d.G (operator d) 0 d.r = centerMeanLp d := by
  funext t
  exact centerMean_eq d (operator d) (primitiveLp_spec _ _) t

/-- The physical-angle identity is also a whole-function identity. -/
theorem angle_function_eq (d : Data (Fin D) m) (j : Fin m) (k : d.G.Kernel) :
    (curvesWithSmoothBranches d).forwardAction d.G (operator d) 0 d.r j k =
      actionLp d j k := by
  funext z
  exact (smoothBranches_forwardAction_eq d (operator d) j k z).trans
    (forwardAction_eq d (operator d) (primitiveLp_spec _ _) j k z)

/-- Full smooth-receiver regularity assembled from five proved suppliers and
precisely the two advertised analytic interfaces. Includes D=0 and ell=0. -/
theorem regularity (d : Data (Fin D) m) (hm : 1 ≤ m)
    (hvelocity : VelocityBounds d) (hangle : AngleBounds d) :
    AffineResidual.Mean.Regularity d.G (curvesWithSmoothBranches d) (operator d) 0 d.r
      (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R)) (budget d) := by
  have hc := centerMeanLp_center_fields_original_data d hm (c := auxiliaryConstant)
    (by norm_num [auxiliaryConstant])
  refine {
    velocity_nonneg := velocityBudget_nonneg d
    center_nonneg := hc.1
    velocity_smooth := hvelocity.smooth
    velocity_bound := hvelocity.bound
    center_smooth := ?_
    center_bound := ?_
    backward := ?_
    conditional := ?_
    forward := ?_
    angle_nonneg := fun _ _ => angleBudget_nonneg d
    angle_smooth := ?_
    angle_bound := ?_
    kernel_nonneg := fun _ => smoothBranches_kernel_budget_nonneg d
    kernel_smooth := fun j => smoothBranches_kernel_contDiffOn d j (m + 2)
    kernel_zero_deriv := smoothBranches_kernel_deriv_zero d
    kernel_terminal := smoothBranches_kernel_terminal_zero d
    kernel_bound := smoothBranches_kernel_bound d }
  · rw [center_function_eq]
    exact hc.2.1
  · rw [center_function_eq]
    exact hc.2.2
  · exact smoothBranches_backward_cellRegularity d
  · exact smoothBranches_conditionalMean_cellRegularity_explicit d _ (primitiveLp_spec _ _)
  · intro j ρ z
    exact smoothBranches_forwardMean_cellRegularity_explicit d _ (primitiveLp_spec _ _)
      j ρ (d.G.angleNode z)
  · intro j k z hz
    rw [angle_function_eq]
    exact hangle.smooth j k z hz
  · intro j k z hz
    rw [angle_function_eq]
    exact hangle.bound j k z hz

section Consumers
variable (d : Data (Fin D) m) (h₀ : ℝ) (hmesh : MeshConditions d h₀)
  (hvelocity : VelocityBounds d) (hangle : AngleBounds d)
include hmesh hvelocity hangle

/-- Row-wise error for the original graph, with the complete explicit budget. -/
theorem row_residual_bound (i : d.G.MeanNode) :
    ‖(lpGraph d).step (operator d) (reference d) i - reference d i‖ ≤
      (budget d).rowError d.G d.r d.sigma h₀ i :=
  MeanSmoothCollocationLp.row_residual_bound d h₀ hmesh _ _ (left_margin d) (right_margin d)
    (budget d) (regularity d (by have := hmesh.order; omega) hvelocity hangle) i

/-- Finite iteration of the unchanged sampler on the same seed. -/
theorem finite_iteration_bound (N : ℕ) :
    ‖iterate d N - reference d‖ ≤ finiteError d h₀ (budget d) N :=
  MeanSmoothCollocationLp.finite_bound d h₀ hmesh _ _ (left_margin d) (right_margin d)
    (budget d) (regularity d (by have := hmesh.order; omega) hvelocity hangle) N

theorem raw_finite_bound (N : ℕ) (i : d.G.MeanNode) :
    ∃ he : MemLp (fun ω => rawIterate d N i ω - rawReference d i ω) 2 (seedMeasure d),
      ‖he.toLp (fun ω => rawIterate d N i ω - rawReference d i ω)‖ ≤
        finiteError d h₀ (budget d) N :=
  MeanSmoothCollocationLp.raw_finite_bound d h₀ hmesh _ _ (left_margin d) (right_margin d)
    (budget d) (regularity d (by have := hmesh.order; omega) hvelocity hangle) N i

/-- Both actual output realizations, retaining the full centering defect. -/
theorem final_output_bound (N : ℕ) :
    ‖output d N - terminalTarget d‖ ≤
      d.ell * finiteError d h₀ (budget d) N + 2 * (budget d).center / (m.factorial : ℝ) ∧
    ∃ he : MemLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω) 2 (seedMeasure d),
      ‖he.toLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω)‖ ≤
        d.ell * finiteError d h₀ (budget d) N + 2 * (budget d).center / (m.factorial : ℝ) :=
  MeanSmoothCollocationLp.final_output_bound d h₀ hmesh _ _ (left_margin d) (right_margin d)
    (budget d) (regularity d (by have := hmesh.order; omega) hvelocity hangle) N
end Consumers
end AcceleratedLogConcave.Numerics.SmoothQuantitativeAssembly
