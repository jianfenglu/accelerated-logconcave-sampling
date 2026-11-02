import AcceleratedLogConcave.Numerics.SmoothForwardDerivatives
import AcceleratedLogConcave.Numerics.SmoothForwardMaterial
import AcceleratedLogConcave.Numerics.SmoothAllReceiver

/-! Original-Data forward TIME cell regularity at every fixed deterministic
angle. The explicit amplitude is ell*r*sqrt(dim)*(12*m)^(12*m). This does not
supply angle derivatives, a numerical mesh or any other Regularity field. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph ConditionalSmoothing Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- The prescribed AF amplitude, independent of j, kernel and fixed angle. -/
def forwardDerivativeBudget (d : MeanFlowLp.Data ι m) (n : ℕ) : ℝ :=
  d.ell*d.r*Real.sqrt (Fintype.card ι : ℝ)*conditionalOrderEnvelope n

omit [DecidableEq ι] in
theorem forwardDerivativeBudget_nonneg (d : MeanFlowLp.Data ι m) (n : ℕ) :
    0 ≤ forwardDerivativeBudget d n :=
  mul_nonneg (mul_nonneg (mul_nonneg d.hell d.hr.le) (Real.sqrt_nonneg _))
    (conditionalOrderEnvelope_nonneg n)

/-- State order k+2 is material index k and mean order k+1.
The inverse physical radius cancels one of the two state-jet radius factors. -/
theorem forwardMean_derivative_le_explicit (d : MeanFlowLp.Data ι m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (z : ℝ) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖iteratedDeriv (k+1) ((curvesWithForward d).forwardMean d.G U 0 d.r j ρ z) t‖ ≤
      forwardDerivativeBudget d (k+1)/(1-t^2)^(k+1) := by
  have hv : 0 < 1-t^2 := Conditional.conditionalVariance_pos
    (by linarith [ht.1]) (ht.2.trans_lt d.G.backwardEnd_lt_one)
  rw [iteratedDeriv_replacement_forwardMean_source d j ρ z U hu (k+1) ht,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_neg, abs_of_pos d.hr]
  have hh := mul_le_mul_of_nonneg_left (forwardJetLp_norm_le_material d j ρ z k ht)
    (inv_nonneg.mpr d.hr.le)
  have he : d.r⁻¹ * ((d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1)) =
      (d.ell*d.r)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1) := by
    field_simp [d.hr.ne']
  rw [he] at hh
  refine hh.trans ?_
  unfold forwardDerivativeBudget
  apply div_le_div_of_nonneg_right _ (pow_nonneg hv.le _)
  have h := mul_le_mul_of_nonneg_left (materialOrderFactor_le (Fintype.card ι) k)
    (mul_nonneg d.hell d.hr.le)
  simpa only [mul_assoc] using h

/-- Whole-function equality transfers the ordinary derivative identity to
the actual receiver carrying all smooth branch fields, without extra premises. -/
theorem iteratedDeriv_smoothBranches_forwardMean (d : MeanFlowLp.Data ι m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (z : ℝ) (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    iteratedDeriv k ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j ρ z) t =
      (-d.r)⁻¹ • forwardJetLp d j ρ z (k+1) t := by
  rw [smoothBranches_forwardMean_eq]
  exact iteratedDeriv_replacement_forwardMean d j ρ z U hu k ht

theorem smoothBranches_forwardMean_derivative_le_explicit (d : MeanFlowLp.Data ι m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (z : ℝ) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖iteratedDeriv (k+1) ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j ρ z) t‖ ≤
      forwardDerivativeBudget d (k+1)/(1-t^2)^(k+1) := by
  rw [smoothBranches_forwardMean_eq]
  exact forwardMean_derivative_le_explicit d U hu j ρ z k ht

/-- The exact AF cell envelope, before any mesh or schedule estimate. -/
def forwardCellBudget (d : MeanFlowLp.Data ι m) (ρ : d.G.Kernel)
    (c : (d.G.forward ρ).Cell) : ℝ :=
  forwardDerivativeBudget d m/(1-((d.G.forward ρ).right c)^2)^m

/-- Actual all-fields forward-time CellRegularity, uniform over every fixed z.
The j-index makes m positive; no assertion about angle derivatives is made. -/
theorem smoothBranches_forwardMean_cellRegularity_explicit (d : MeanFlowLp.Data ι m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (z : ℝ) :
    AffineResidual.CellRegularity (d.G.forward ρ) m
      ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j ρ z)
      (forwardCellBudget d ρ) := by
  have hm : 1 ≤ m := by have hj := j.isLt; omega
  have hright (c : (d.G.forward ρ).Cell) : 0 < 1-((d.G.forward ρ).right c)^2 := by
    apply Conditional.conditionalVariance_pos
    · have h0 := (d.G.rho_mem ρ).1.trans ((d.G.forward ρ).lo_le_left c)
      have hl := (d.G.forward ρ).length_pos c
      dsimp [IntervalMesh.length] at hl
      linarith
    · exact ((d.G.forward ρ).right_le_hi c).trans_lt d.G.backwardEnd_lt_one
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact div_nonneg (forwardDerivativeBudget_nonneg d m) (pow_nonneg (hright c).le _)
  · intro c t ht
    exact smoothBranches_contDiffAt_forwardMean d U hu j ρ z m
      ⟨((d.G.rho_mem ρ).1.trans ((d.G.forward ρ).lo_le_left c)).trans ht.1,
        ht.2.trans ((d.G.forward ρ).right_le_hi c)⟩
  · intro c t ht
    have hsource : t ∈ Icc 0 (backwardEnd d.G.R) :=
      ⟨((d.G.rho_mem ρ).1.trans ((d.G.forward ρ).lo_le_left c)).trans ht.1,
        ht.2.trans ((d.G.forward ρ).right_le_hi c)⟩
    have hb := smoothBranches_forwardMean_derivative_le_explicit d U hu j ρ z (m-1) hsource
    rw [Nat.sub_add_cancel hm] at hb
    refine hb.trans ?_
    unfold forwardCellBudget
    apply div_le_div_of_nonneg_left (forwardDerivativeBudget_nonneg d m) (pow_pos (hright c) m)
    apply pow_le_pow_left₀ (hright c).le
    nlinarith [hsource.1, ht.2]

end AcceleratedLogConcave.Numerics.MeanResidualBridge
