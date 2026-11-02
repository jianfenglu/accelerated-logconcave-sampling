import AcceleratedLogConcave.Oracle.SamplingExecutableStability

/-! The radicand and exact variance of the literal private final noise. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateSamplingNoiseBudget
open Numerics.AffineGraph SourceExecutableTables
open scoped BigOperators
set_option autoImplicit false
variable {m n : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r : ℝ)

theorem final_sq_mass_le (hm : 0 < m) (hr : 0 < r) :
    (∑ i, samplingFinalWeight S e r i ^ 2) ≤ r ^ 2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => |samplingFinalWeight S e r i|)
    (fun i _ => abs_nonneg _)
  simpa only [sq_abs, FixedTapeSampling.sampling_final_mass S e r hm hr.le] using h

theorem final_designated_mass_le (hm : 0 < m) (hr : 0 < r) :
    (∑ i, samplingFinalWeight S e r i ^ 2 * samplingFinalWidth S r ^ 2) ≤ S.τ^2/8 := by
  rw [← Finset.sum_mul]
  have h := mul_le_mul_of_nonneg_right (final_sq_mass_le S e r hm hr)
    (sq_nonneg (samplingFinalWidth S r))
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have he : r^2 * samplingFinalWidth S r ^ 2 = S.τ^2/8 := by
    unfold samplingFinalWidth
    field_simp
    nlinarith
  exact h.trans_eq he

theorem beta_radicand_ge (hm : 0 < m) (hr : 0 < r) :
    3*S.τ^2/8 ≤ (S.τ/Real.sqrt 2)^2 -
      ∑ i, samplingFinalWeight S e r i ^ 2 * samplingFinalWidth S r ^ 2 := by
  have h := final_designated_mass_le S e r hm hr
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  rw [div_pow, hs]
  linarith

theorem beta_sq (hm : 0 < m) (hr : 0 < r) :
    samplingBeta S e r ^ 2 = (S.τ/Real.sqrt 2)^2 -
      ∑ i, samplingFinalWeight S e r i ^ 2 * samplingFinalWidth S r ^ 2 := by
  apply Real.sq_sqrt
  exact (by positivity : 0 ≤ 3*S.τ^2/8).trans (beta_radicand_ge S e r hm hr)

theorem final_noise_variance (hm : 0 < m) (hr : 0 < r) :
    (∑ i, (samplingFinalWeight S e r i * samplingFinalWidth S r)^2) +
      samplingBeta S e r ^ 2 + (S.τ/2)^2 = 3*S.τ^2/4 := by
  rw [beta_sq S e r hm hr]
  simp_rw [mul_pow]
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  rw [div_pow, hs]
  ring

end AcceleratedLogConcave.Oracle.PrivateSamplingNoiseBudget
