import AcceleratedLogConcave.Gibbs.PosteriorPolynomial
import AcceleratedLogConcave.Gibbs.HeatHessian

/-! Polynomial envelopes for the actual normalized posterior measure.
The ratio identity is connected to the existing heatPosterior definition;
integrability is established separately rather than inferred from a totalized
Bochner integral value. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace AcceleratedLogConcave.Gibbs
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every polynomial norm observable is genuinely integrable under the actual
positive-variance posterior, using only C² convexity. -/
theorem integrable_one_add_norm_pow_heatPosterior {F : E → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    {t : ℝ} (ht : 0 < t) (y : E) (n : ℕ) :
    Integrable (fun u : E => (1 + ‖u‖) ^ n) (heatPosterior F t y) := by
  have hH : ∀ z w, (0 : ℝ) * ‖w‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z w w := by
    simpa only [zero_mul] using hlo
  let := heatPosterior_isProbabilityMeasure hF (le_refl 0) ht hH y
  have hn := integrable_norm_pow_heatPosterior hF (le_refl 0) ht hH y n
  apply (((integrable_const (1 : ℝ)).add hn).const_mul (2 ^ (n - 1))).mono'
    (by fun_prop)
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [Pi.add_apply, one_pow] using add_pow_le zero_le_one (norm_nonneg u) n

/-- The uniform polynomial ratio bound is a bound on the literal existing
heatPosterior measure, uniformly over center and compact positive variance. -/
theorem exists_polynomial_heatPosterior_bound
    {F : E → ℝ} {L v₀ v₁ : ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ v₁) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc v₀ v₁, ∀ y : E,
      (∫ u, (1 + ‖u‖) ^ n ∂heatPosterior F t y) ≤ C * (1 + ‖y‖) ^ n := by
  obtain ⟨C, hC, hbound⟩ := exists_polynomial_posterior_ratio_bound hF hlo hhi hv₀ hv n
  refine ⟨C, hC, ?_⟩
  intro t ht y
  rw [integral_heatPosterior hF (le_refl 0) (hv₀.trans_le ht.1)
    (by simpa only [zero_mul] using hlo)]
  simp_rw [smul_eq_mul]
  have he : (∫ u, Real.exp (-(F u + ‖u - y‖ ^ 2 / (2 * t))) * (1 + ‖u‖) ^ n) =
      ∫ u, (1 + ‖u‖) ^ n * Real.exp (-(F u + ‖u - y‖ ^ 2 / (2 * t))) := by
    apply integral_congr_ae
    filter_upwards [] with u
    exact mul_comm _ _
  rw [he]
  simpa only [div_eq_mul_inv, mul_comm] using hbound t ht y

/-- Every fixed continuous polynomial-growth observable inherits a uniform
polynomial bound on its actual normalized expectation. -/
theorem exists_polynomial_heatPosterior_observable_bound
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E → ℝ} {L v₀ v₁ : ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ v₁)
    {g : E → G} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (n : ℕ)
    (hgbound : ∀ u, ‖g u‖ ≤ A * (1 + ‖u‖) ^ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc v₀ v₁, ∀ y : E,
      Integrable g (heatPosterior F t y) ∧
        ‖∫ u, g u ∂heatPosterior F t y‖ ≤ C * (1 + ‖y‖) ^ n := by
  obtain ⟨C, hC, hbound⟩ := exists_polynomial_heatPosterior_bound hF hlo hhi hv₀ hv n
  refine ⟨A * C, mul_nonneg hA hC, ?_⟩
  intro t ht y
  have hp := integrable_one_add_norm_pow_heatPosterior hF hlo (hv₀.trans_le ht.1) y n
  have hi : Integrable g (heatPosterior F t y) :=
    (hp.const_mul A).mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hgbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ u, ‖g u‖ ∂heatPosterior F t y := norm_integral_le_integral_norm _
    _ ≤ ∫ u, A * (1 + ‖u‖) ^ n ∂heatPosterior F t y :=
      integral_mono hi.norm (hp.const_mul A) hgbound
    _ = A * (∫ u, (1 + ‖u‖) ^ n ∂heatPosterior F t y) := integral_const_mul _ _
    _ ≤ A * (C * (1 + ‖y‖) ^ n) := mul_le_mul_of_nonneg_left (hbound t ht y) hA
    _ = _ := (mul_assoc _ _ _).symm

end AcceleratedLogConcave.Gibbs
