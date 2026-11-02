import AcceleratedLogConcave.Conditional.Tilt.HeatIntegral
import AcceleratedLogConcave.Gibbs.PosteriorPolynomialMeasure

/-! Polynomial bounds in the actual natural Gaussian parameters.
Square completion is used through the existing exact heatPosterior identity.
The interval constants are fixed before the unrestricted linear tilt. -/
noncomputable section
namespace AcceleratedLogConcave.Conditional.Tilt

open MeasureTheory Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Gaussian differentiation moments are derived from C² convexity and
the fixed observable's polynomial growth; they are not extra supplier inputs. -/
theorem hasGaussianMoments_of_convex_polynomial_growth
    {G : Type*} [NormedAddCommGroup G] {F : E → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    {g : E → G} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (hgbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k) :
    HasGaussianMoments F g := by
  have hlower (z : E) : F 0 + inner ℝ (gradient F 0) z ≤ F z := by
    have hh := Gibbs.quadratic_lower_bound_of_hessian_lower hF
      (show ∀ z w, (0 : ℝ) * ‖w‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z w w by
        simpa only [zero_mul] using hlo) z
    rw [← inner_gradient_left] at hh
    simpa only [zero_div, zero_mul, add_zero] using hh
  let C : ℝ := A * 2 ^ (k - 1)
  apply hasGaussianMoments_of_polynomial_growth hF.continuous hg
    (F 0) (gradient F 0) hlower C C k
  intro z
  calc
    _ ≤ A * (1 + ‖z‖) ^ k := hgbound z
    _ ≤ A * (2 ^ (k - 1) * (1 + ‖z‖ ^ k)) :=
      mul_le_mul_of_nonneg_left (by simpa only [one_pow] using
        (add_pow_le zero_le_one (norm_nonneg z) k)) hA
    _ = _ := by dsimp [C]; ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Inverse of the existing variance/center parameterization at positive
precision. No change to the underlying posterior law is made. -/
theorem posteriorParameters_inverse (a : ℝ) (b : E) (ha : a ≠ 0) :
    posteriorParameters ((2 * a)⁻¹, (2 * a)⁻¹ • b) = (a, b) := by
  apply Prod.ext
  · simp only [posteriorParameters]
    field_simp
  · simp only [posteriorParameters, inv_inv, smul_smul]
    rw [mul_inv_cancel₀ (mul_ne_zero (by norm_num) ha), one_smul]

/-- The natural Gaussian normalization is the existing heat posterior, with
the completed-square variance and center written explicitly. -/
theorem normalizedGaussianIntegral_eq_heatPosterior
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (g : E → G) {a : ℝ} (ha : 0 < a) (b : E) :
    normalizedGaussianIntegral F g (a, b) =
      ∫ z, g z ∂Gibbs.heatPosterior F ((2 * a)⁻¹) ((2 * a)⁻¹ • b) := by
  rw [integral_heatPosterior_eq_normalizedGaussianIntegral hF (le_refl 0)
    (by positivity) (by simpa only [zero_mul] using hlo)]
  rw [posteriorParameters_inverse a b ha.ne']

/-- Fixed polynomial-growth observables have uniform polynomial normalized
expectations on every compact interval of positive natural precision. -/
theorem exists_polynomial_normalizedGaussianIntegral_bound
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E → ℝ} {L a₀ a₁ : ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (ha₀ : 0 < a₀) (ha : a₀ ≤ a₁)
    {g : E → G} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (n : ℕ)
    (hgbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc a₀ a₁, ∀ b : E,
      ‖normalizedGaussianIntegral F g (a, b)‖ ≤ C * (1 + ‖b‖) ^ n := by
  have ha₁ : 0 < a₁ := ha₀.trans_le ha
  have hv₀ : 0 < (2 * a₁)⁻¹ := by positivity
  have hv : (2 * a₁)⁻¹ ≤ (2 * a₀)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left ha (by norm_num)
  obtain ⟨C, hC, hbound⟩ := Gibbs.exists_polynomial_heatPosterior_observable_bound
    hF hlo hhi hv₀ hv hg hA n hgbound
  let R : ℝ := 1 + (2 * a₀)⁻¹
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨C * R ^ n, mul_nonneg hC (pow_nonneg hR n), ?_⟩
  intro a ha' b
  have hapos : 0 < a := ha₀.trans_le ha'.1
  have ht : (2 * a)⁻¹ ∈ Icc ((2 * a₁)⁻¹) ((2 * a₀)⁻¹) := by
    constructor
    · apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      exact mul_le_mul_of_nonneg_left ha'.2 (by norm_num)
    · apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      exact mul_le_mul_of_nonneg_left ha'.1 (by norm_num)
  have hnorm : 1 + ‖(2 * a)⁻¹ • b‖ ≤ R * (1 + ‖b‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 * a)⁻¹)]
    have hm := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg b)
    dsimp [R]
    nlinarith [norm_nonneg b, inv_pos.mpr (by positivity : 0 < 2 * a₀)]
  rw [normalizedGaussianIntegral_eq_heatPosterior hF hlo g hapos b]
  calc
    _ ≤ C * (1 + ‖(2 * a)⁻¹ • b‖) ^ n := (hbound _ ht _).2
    _ ≤ C * (R * (1 + ‖b‖)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnorm n) hC
    _ = _ := by rw [mul_pow, mul_assoc]

end AcceleratedLogConcave.Conditional.Tilt
