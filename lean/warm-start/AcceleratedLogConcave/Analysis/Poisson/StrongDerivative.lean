import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Integrating a bounded strong operator derivative

The derivative is proved separately on each fixed vector. No differentiability
in the operator norm topology is assumed. This lemma supplies the final
integration step for the moving Poisson gradient once its actual strong
derivative and the gap-free bound have been established.
-/

noncomputable section
open Set MeasureTheory

namespace AcceleratedLogConcave.Analysis.Poisson

variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- A bounded strong derivative gives the corresponding integrated operator
norm difference estimate. Continuity is likewise only required on each vector. -/
theorem norm_sub_le_integral_of_strong_derivative
    (A B : ℝ → H →L[ℝ] K) (C : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hcont : ∀ x, ContinuousOn (fun t => A t x) (Icc a b))
    (hderiv : ∀ x t, t ∈ Ioo a b →
      HasDerivAt (fun s => A s x) (B t x) t)
    (hbound : ∀ t, t ∈ Ioo a b → ‖B t‖ ≤ C t)
    (hC : ∀ t, t ∈ Icc a b → 0 ≤ C t)
    (hCi : IntervalIntegrable C volume a b) :
    ‖A b - A a‖ ≤ ∫ t in a..b, C t := by
  apply ContinuousLinearMap.opNorm_le_bound _ (intervalIntegral.integral_nonneg hab hC)
  intro x
  change ‖A b x - A a x‖ ≤ (∫ t in a..b, C t) * ‖x‖
  have hdiff : DifferentiableOn ℝ (fun t => A t x) (Ioo a b) :=
    fun t ht => (hderiv x t ht).differentiableAt.differentiableWithinAt
  have hspeed : ∀ᵐ t, t ∈ Ioo a b →
      ‖deriv (fun s => A s x) t‖ ≤ C t * ‖x‖ := by
    apply Filter.Eventually.of_forall
    intro t ht
    rw [(hderiv x t ht).deriv]
    exact ((B t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg x))
  simpa only [intervalIntegral.integral_mul_const] using
    norm_sub_le_integral_of_norm_deriv_le_of_le hab (hcont x) hdiff hspeed
      (hCi.mul_const ‖x‖)

end AcceleratedLogConcave.Analysis.Poisson
