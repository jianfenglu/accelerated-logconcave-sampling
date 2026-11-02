import AcceleratedLogConcave.Gibbs.PolynomialRatio
import AcceleratedLogConcave.Gibbs.Posterior

/-! Center-uniform polynomial moments for the actual positive-variance
Gaussian posterior ratio, from the original C² curvature assumptions. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace AcceleratedLogConcave.Gibbs
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Only the original derivative at zero and the linear Gaussian center term
enter the posterior derivative at zero. -/
theorem norm_fderiv_posterior_zero_le {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {t : ℝ} (ht : 0 < t) (y : E) :
    ‖fderiv ℝ (fun u => F u + ‖u - y‖ ^ 2 / (2 * t)) 0‖ ≤
      ‖fderiv ℝ F 0‖ + t⁻¹ * ‖y‖ := by
  have hd := ((hF.differentiable (by norm_num) 0).hasFDerivAt.add
    (hasFDerivAt_gaussian_regularizer t y 0)).fderiv
  change fderiv ℝ (fun u => F u + ‖u - y‖ ^ 2 / (2 * t)) 0 =
    fderiv ℝ F 0 + t⁻¹ • innerSL ℝ ((0 : E) - y) at hd
  rw [hd]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),
    innerSL_apply_norm, zero_sub, norm_neg] using
    norm_add_le (fderiv ℝ F 0) (t⁻¹ • innerSL ℝ ((0 : E) - y))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Uniformity in both variance on a compact positive interval and arbitrary
center. The actual posterior density appears on both sides of the ratio;
there is no input-law replacement and no additional derivative assumption. -/
theorem exists_polynomial_posterior_ratio_bound
    {F : E → ℝ} {L v₀ v₁ : ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ v₁) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc v₀ v₁, ∀ y : E,
      (∫ u, (1 + ‖u‖) ^ n * Real.exp (-(F u + ‖u - y‖ ^ 2 / (2 * t)))) /
        (∫ u, Real.exp (-(F u + ‖u - y‖ ^ 2 / (2 * t)))) ≤
          C * (1 + ‖y‖) ^ n := by
  have hv₁ : 0 < v₁ := hv₀.trans_le hv
  obtain ⟨C, hC, hbound⟩ := exists_polynomial_ratio_bound_of_hessian_sandwich (E := E)
    (inv_pos.mpr hv₁) (by positivity : 0 < max L 0 + v₀⁻¹) n
  let A := 1 + ‖fderiv ℝ F 0‖ + v₀⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C * A ^ n, mul_nonneg hC (pow_nonneg hA n), ?_⟩
  intro t ht y
  have htpos : 0 < t := hv₀.trans_le ht.1
  have hprec_lo : v₁⁻¹ ≤ t⁻¹ := (inv_le_inv₀ hv₁ htpos).mpr ht.2
  have hprec_hi : t⁻¹ ≤ v₀⁻¹ := (inv_le_inv₀ htpos hv₀).mpr ht.1
  let H (u : E) := F u + ‖u - y‖ ^ 2 / (2 * t)
  have hH : ContDiff ℝ 2 H := contDiff_posterior_potential hF t y
  have hHlo (z w : E) : v₁⁻¹ * ‖w‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ H) z w w := by
    rw [posterior_hessian_quadratic hF]
    have h := mul_le_mul_of_nonneg_right hprec_lo (sq_nonneg ‖w‖)
    linarith [hlo z w]
  have hHhi (z w : E) : fderiv ℝ (fderiv ℝ H) z w w ≤
      (max L 0 + v₀⁻¹) * ‖w‖ ^ 2 := by
    rw [posterior_hessian_quadratic hF]
    have hp := mul_le_mul_of_nonneg_right hprec_hi (sq_nonneg ‖w‖)
    have hL := mul_le_mul_of_nonneg_right (le_max_left L 0) (sq_nonneg ‖w‖)
    nlinarith [hhi z w]
  have hnorm : 1 + ‖fderiv ℝ H 0‖ ≤ A * (1 + ‖y‖) := by
    have hd := norm_fderiv_posterior_zero_le hF htpos y
    have hp := mul_le_mul_of_nonneg_right hprec_hi (norm_nonneg y)
    dsimp [A]
    change 1 + ‖fderiv ℝ H 0‖ ≤ _
    change ‖fderiv ℝ H 0‖ ≤ _ at hd
    nlinarith [norm_nonneg y, norm_nonneg (fderiv ℝ F 0), inv_pos.mpr hv₀]
  calc
    _ ≤ C * (1 + ‖fderiv ℝ H 0‖) ^ n := hbound H hH hHlo hHhi
    _ ≤ C * (A * (1 + ‖y‖)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnorm n) hC
    _ = _ := by rw [mul_pow, mul_assoc]

end AcceleratedLogConcave.Gibbs
