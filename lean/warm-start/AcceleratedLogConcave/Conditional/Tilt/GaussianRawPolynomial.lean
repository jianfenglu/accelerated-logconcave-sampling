import AcceleratedLogConcave.Conditional.Tilt.GaussianJetBound
import AcceleratedLogConcave.Conditional.Tilt.PolynomialBounds

/-! Actual raw Gaussian jets divided by their
actual positive partition have polynomial bounds. The partition is not
estimated separately, and no law is substituted. -/
noncomputable section
namespace AcceleratedLogConcave.Conditional.Tilt
open MeasureTheory Set
open scoped ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem exists_polynomial_normalized_raw_jet_bound
    {F : E → ℝ} {L a₀ a₁ : ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (ha₀ : 0 < a₀) (ha : a₀ ≤ a₁)
    {g : E → G} (hg : Continuous g)
    {A : ℝ} (hA : 0 ≤ A) (k n : ℕ)
    (hgbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc a₀ a₁, ∀ b : E,
      (gaussianIntegral F (fun _ => (1 : ℝ)) (a, b))⁻¹ *
        ‖iteratedFDerivWithin ℝ n (gaussianIntegral F g) gaussianDomain (a, b)‖ ≤
          C * (1 + ‖b‖) ^ (2 * n + k) := by
  have hgm := hasGaussianMoments_of_convex_polynomial_growth hF hlo hg hA k hgbound
  have h1 := hasGaussianMoments_of_convex_polynomial_growth hF hlo
    (continuous_const : Continuous (fun _ : E => (1 : ℝ))) zero_le_one 0
    (by intro z; simp)
  let v (z : E) : ℝ := ‖gaussianStatistic z‖ ^ n * ‖g z‖
  have hstat : Continuous (fun z : E => ‖gaussianStatistic z‖) :=
    (continuous_norm (E := (ℝ × E) →L[ℝ] ℝ)).comp
      (continuous_gaussianStatistic (E := E))
  have hv : Continuous v := (hstat.pow n).mul hg.norm
  have hvbound : ∀ z, ‖v z‖ ≤ A * (1 + ‖z‖) ^ (2 * n + k) :=
    norm_gaussian_statisticNorm_observable_le k n hgbound
  obtain ⟨C, hC, hbound⟩ := exists_polynomial_normalizedGaussianIntegral_bound
    hF hlo hhi ha₀ ha hv hA (2 * n + k) hvbound
  refine ⟨C, hC, ?_⟩
  intro a ha' b
  have hapos : 0 < a := ha₀.trans_le ha'.1
  have hZ : 0 < gaussianIntegral F (fun _ => (1 : ℝ)) (a, b) := by
    have hi := integrable_gaussian_integrand hF.continuous continuous_const h1 (a, b) hapos
    simp only [smul_eq_mul, mul_one] at hi
    simpa only [gaussianIntegral, smul_eq_mul, mul_one] using integral_exp_pos hi
  have hvint : 0 ≤ gaussianIntegral F v (a, b) := by
    apply integral_nonneg
    intro z
    change 0 ≤ Real.exp (-F z + gaussianStatistic z (a, b)) *
      (‖gaussianStatistic z‖ ^ n * ‖g z‖)
    positivity
  have hraw := norm_iteratedFDerivWithin_gaussianIntegral_statistic
    hF.continuous hg hgm n (a, b) hapos
  have hraw' : ‖iteratedFDerivWithin ℝ n (gaussianIntegral F g) gaussianDomain (a, b)‖ ≤
      gaussianIntegral F v (a, b) := by
    simpa only [gaussianIntegral, v, smul_eq_mul, mul_assoc] using hraw
  calc
    _ ≤ (gaussianIntegral F (fun _ => (1 : ℝ)) (a, b))⁻¹ *
        gaussianIntegral F v (a, b) :=
      mul_le_mul_of_nonneg_left hraw' (inv_nonneg.mpr hZ.le)
    _ = ‖normalizedGaussianIntegral F v (a, b)‖ := by
      rw [normalizedGaussianIntegral, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hZ), Real.norm_eq_abs, abs_of_nonneg hvint]
    _ ≤ _ := hbound a ha' b

end AcceleratedLogConcave.Conditional.Tilt
