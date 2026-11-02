import AcceleratedLogConcave.Conditional.Tilt.GaussianRawPolynomial
import AcceleratedLogConcave.Analysis.NormalizedJetBound
import AcceleratedLogConcave.Analysis.PolynomialEnvelope

/-! Actual normalized Gaussian mixed jets have
uniform polynomial growth on compact positive precision intervals. The base
potential is only C². Normalization consumes raw derivative bounds through n only.
The constants and degree here are qualitative, not a sharp source budget. -/
noncomputable section
namespace AcceleratedLogConcave.Conditional.Tilt
open MeasureTheory Set
open scoped ContDiff
open Analysis.NormalizedJetBound Analysis.PolynomialEnvelope

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem exists_polynomial_normalizedGaussian_jet_bound
    {F : E → ℝ} {L a₀ a₁ : ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (ha₀ : 0 < a₀) (ha : a₀ ≤ a₁)
    {g : E → G} (hg : Continuous g)
    {A : ℝ} (hA : 0 ≤ A) (k n : ℕ)
    (hgbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ a ∈ Icc a₀ a₁, ∀ b : E,
      ‖iteratedFDerivWithin ℝ n (normalizedGaussianIntegral F g)
        gaussianDomain (a, b)‖ ≤ C * (1 + ‖b‖) ^ N := by
  let S := gaussianIntegral F (fun _ : E => (1 : ℝ))
  let raw := gaussianIntegral F g
  let slab : Set (ℝ × E) := {p | p.1 ∈ Icc a₀ a₁}
  let R (p : ℝ × E) : ℝ := 1 + ‖p.2‖
  let f : (Fin (n + 1) ⊕ Fin (n + 1)) → (ℝ × E) → ℝ :=
    Sum.elim
      (fun i p => (S p)⁻¹ * ‖iteratedFDerivWithin ℝ i.val S gaussianDomain p‖)
      (fun i p => (S p)⁻¹ * ‖iteratedFDerivWithin ℝ i.val raw gaussianDomain p‖)
  have hR : ∀ p ∈ slab, 1 ≤ R p := by
    intro p _
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hf : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p ∈ slab, f i p ≤ C * R p ^ N := by
    intro i
    rcases i with i | i
    · obtain ⟨C, hC, hbound⟩ := exists_polynomial_normalized_raw_jet_bound
        hF hlo hhi ha₀ ha (continuous_const : Continuous (fun _ : E => (1 : ℝ)))
        zero_le_one 0 i.val (by intro z; simp)
      exact ⟨C, hC, 2 * i.val + 0, fun p hp => hbound p.1 hp p.2⟩
    · obtain ⟨C, hC, hbound⟩ := exists_polynomial_normalized_raw_jet_bound
        hF hlo hhi ha₀ ha hg hA k i.val hgbound
      exact ⟨C, hC, 2 * i.val + k, fun p hp => hbound p.1 hp p.2⟩
  obtain ⟨C, hC, N, hbound⟩ := exists_common_finite_polynomial_bound hR hf
  let K : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * (i.factorial : ℝ) * (n.factorial : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K * C ^ (n + 1), mul_nonneg hK (pow_nonneg (zero_le_one.trans hC) _),
    N * (n + 1), ?_⟩
  have hgm := hasGaussianMoments_of_convex_polynomial_growth hF hlo hg hA k hgbound
  have h1 := hasGaussianMoments_of_convex_polynomial_growth hF hlo
    (continuous_const : Continuous (fun _ : E => (1 : ℝ))) zero_le_one 0
    (by intro z; simp)
  have hS : ContDiffOn ℝ ∞ S gaussianDomain :=
    contDiffOn_gaussianIntegral hF.continuous continuous_const h1
  have hraw : ContDiffOn ℝ ∞ raw gaussianDomain :=
    contDiffOn_gaussianIntegral hF.continuous hg hgm
  have hpositive : ∀ p ∈ gaussianDomain, 0 < S p := by
    intro p hp
    have hi := integrable_gaussian_integrand hF.continuous continuous_const h1 p hp
    simp only [smul_eq_mul, mul_one] at hi
    simpa only [S, gaussianIntegral, smul_eq_mul, mul_one] using integral_exp_pos hi
  intro a ha' b
  have hp : (a, b) ∈ gaussianDomain := ha₀.trans_le ha'.1
  have hslab : (a, b) ∈ slab := ha'
  have hD : 1 ≤ C * R (a, b) ^ N :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (hR _ hslab))
  have hden (i : ℕ) (hi : i ≤ n) :
      (S (a, b))⁻¹ * ‖iteratedFDerivWithin ℝ i S gaussianDomain (a, b)‖ ≤
        C * R (a, b) ^ N :=
    hbound (Sum.inl ⟨i, Nat.lt_succ_of_le hi⟩) (a, b) hslab
  have hnum (i : ℕ) (hi : i ≤ n) :
      (S (a, b))⁻¹ * ‖iteratedFDerivWithin ℝ i raw gaussianDomain (a, b)‖ ≤
        C * R (a, b) ^ N :=
    hbound (Sum.inr ⟨i, Nat.lt_succ_of_le hi⟩) (a, b) hslab
  have hratio := norm_iteratedFDerivWithin_ratio_le
    isOpen_gaussianDomain.uniqueDiffOn hp hS hraw hpositive n hD hden hnum
  have hmono := normalizedJetSum_le n hD
  have hh := hratio.trans hmono
  change ‖iteratedFDerivWithin ℝ n (fun q => (S q)⁻¹ • raw q)
    gaussianDomain (a, b)‖ ≤ _
  simpa only [S, raw, K, R, mul_pow, ← pow_mul,
    mul_assoc] using hh

end AcceleratedLogConcave.Conditional.Tilt
