import AcceleratedLogConcave.Probability.Warmness
import AcceleratedLogConcave.Analysis.Poisson.Centered

/-! The centered density of the supplied joint warm law. The input may have
arbitrary dependence between coordinates; no product-law assumption is used. -/
noncomputable section
open MeasureTheory
set_option autoImplicit false
namespace AcceleratedLogConcave.Probability
open Analysis.Poisson
variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ}

def L2Warm.centeredDensity (h : L2Warm μ ν B) : centered μ :=
  ⟨h.memLp_centered.toLp (fun x => (ν.rnDeriv μ x).toReal-1), by
    rw [mem_centered]
    rw [integral_congr_ae h.memLp_centered.coeFn_toLp,
      integral_sub Measure.integrable_toReal_rnDeriv (integrable_const 1)]
    simpa using congrArg (fun a : ℝ => a-1) (Measure.integral_toReal_rnDeriv h.absolutelyContinuous)⟩

theorem L2Warm.centeredDensity_coe_ae (h : L2Warm μ ν B) :
    ((h.centeredDensity : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ]
      fun x => (ν.rnDeriv μ x).toReal-1 := h.memLp_centered.coeFn_toLp

theorem L2Warm.norm_centeredDensity_le (h : L2Warm μ ν B) :
    ‖h.centeredDensity‖ ≤ Real.sqrt (B-1) := h.norm_toLp_centered_le

theorem L2Warm.norm_centeredDensity_sq (h : L2Warm μ ν B) :
    ‖h.centeredDensity‖^2 = (∫ x, ((ν.rnDeriv μ x).toReal)^2 ∂μ)-1 :=
  h.norm_toLp_centered_sq

theorem L2Warm.totalVariationDistance_le_centeredDensity (h : L2Warm μ ν B) :
    totalVariationDistance ν μ ≤ ‖h.centeredDensity‖/2 :=
  h.totalVariationDistance_le_half_norm_centered

end AcceleratedLogConcave.Probability
