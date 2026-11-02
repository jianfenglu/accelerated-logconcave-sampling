import AcceleratedLogConcave.Conditional.Tilt.PolynomialBounds

/-! Differentiating the actual posterior center
restricts the natural Gaussian derivative to the linear-tilt coordinate.
The scalar is inverse positive variance, never inverse probability time. -/
noncomputable section
namespace AcceleratedLogConcave.Conditional.Tilt
open MeasureTheory Set
open scoped ContDiff
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem fderiv_heatPosterior_center_eq_natural
    {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    {g : E → G} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k)
    {v : ℝ} (hv : 0 < v) (c : E) :
    fderiv ℝ (fun d => ∫ z, g z ∂Gibbs.heatPosterior F v d) c =
      v⁻¹ • (fderiv ℝ (normalizedGaussianIntegral F g)
        (posteriorParameters (v, c))).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hgm := hasGaussianMoments_of_convex_polynomial_growth hF hlo hg hA k hbound
  have h1 := hasGaussianMoments_of_convex_polynomial_growth hF hlo
    (continuous_const : Continuous (fun _ : E => (1 : ℝ))) zero_le_one 0
    (by intro z; simp)
  have hp : posteriorParameters (v, c) ∈ gaussianDomain := by
    change 0 < (2 * v)⁻¹
    positivity
  have hQ := ((contDiffOn_normalizedGaussianIntegral hF.continuous hg hgm h1).contDiffAt
    (isOpen_gaussianDomain.mem_nhds hp)).differentiableAt (by simp)
  have hparam := (hasFDerivAt_const (𝕜 := ℝ) ((2 * v)⁻¹) c).prodMk
    ((hasFDerivAt_id c).const_smul v⁻¹)
  have hchain := hQ.hasFDerivAt.comp c hparam
  have heq : (fun d => ∫ z, g z ∂Gibbs.heatPosterior F v d) =
      (fun d => normalizedGaussianIntegral F g (posteriorParameters (v, d))) := by
    funext d
    exact integral_heatPosterior_eq_normalizedGaussianIntegral hF (le_refl 0) hv
      (by simpa only [zero_mul] using hlo) g d
  rw [heq]
  change fderiv ℝ (normalizedGaussianIntegral F g ∘
    (fun d : E => ((2 * v)⁻¹, (v⁻¹ • id) d))) c = _
  rw [hchain.fderiv]
  ext w
  change (fderiv ℝ (normalizedGaussianIntegral F g)
      (posteriorParameters (v, c))) (0, v⁻¹ • w) =
    v⁻¹ • (fderiv ℝ (normalizedGaussianIntegral F g)
      (posteriorParameters (v, c))) (0, w)
  simpa only [Prod.smul_mk, smul_zero] using
    (fderiv ℝ (normalizedGaussianIntegral F g)
      (posteriorParameters (v, c))).map_smul v⁻¹ ((0 : ℝ), w)

end AcceleratedLogConcave.Conditional.Tilt
