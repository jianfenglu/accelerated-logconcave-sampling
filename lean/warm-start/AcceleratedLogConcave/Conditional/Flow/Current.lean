import Mathlib.Probability.Moments.Covariance

/-! The excess weighted interpolation flux is its positive covariance current. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace AcceleratedLogConcave.Conditional
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The observable-weighted flux minus the mean times the ordinary flux has
the positive covariance sign. No nonzero-time division is involved: `t` is
the strictly positive Gaussian variance in the eventual application. -/
theorem excessInterpolationFlux_eq_covariance
    {f Z : Ω → ℝ} (hf : MemLp f 2 μ) (hZ : MemLp Z 2 μ) (c t : ℝ) :
    (∫ z, f z * ((Z z - c) / t) ∂μ) -
      (∫ z, f z ∂μ) * (∫ z, (Z z - c) / t ∂μ) =
        cov[f, Z; μ] / t := by
  have hv : MemLp (fun z => (Z z - c) / t) 2 μ := by
    simpa only [Pi.sub_apply, div_eq_mul_inv, mul_comm] using
      (hZ.sub (memLp_const c)).const_mul t⁻¹
  calc
    _ = cov[f, fun z => (Z z - c) / t; μ] := by
      simpa only [Pi.mul_apply] using (covariance_eq_sub hf hv).symm
    _ = _ := by
      rw [covariance_fun_div_right,
        covariance_sub_const_right (hZ.integrable (by norm_num))]

/-- Equivalent flux decomposition, in the form used by the weighted
continuity equation. -/
theorem weightedInterpolationFlux_eq_mean_add_current
    {f Z : Ω → ℝ} (hf : MemLp f 2 μ) (hZ : MemLp Z 2 μ) (c t : ℝ) :
    (∫ z, f z * ((Z z - c) / t) ∂μ) =
      (∫ z, f z ∂μ) * (∫ z, (Z z - c) / t ∂μ) + cov[f, Z; μ] / t := by
  linarith [excessInterpolationFlux_eq_covariance hf hZ c t]

end AcceleratedLogConcave.Conditional
