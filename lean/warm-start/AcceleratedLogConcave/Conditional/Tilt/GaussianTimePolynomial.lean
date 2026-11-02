import AcceleratedLogConcave.Conditional.Tilt.NaturalParameterComposition
import AcceleratedLogConcave.Conditional.Tilt.GaussianNormalizedPolynomial
import AcceleratedLogConcave.Conditional.Tilt.GaussianCenterDerivative
import AcceleratedLogConcave.Analysis.DerivativeRestriction
import AcceleratedLogConcave.Analysis.PolynomialSmul

/-! actual posterior mixed-jet adapters. The base potential stays
C². Natural-parameter regularization supplies smoothness, and the finite
quantitative ladder uses Q through n for the mean and n+1 for its first
center derivative. No inverse probability time occurs. -/
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Conditional.Tilt
open Analysis.PositiveVarianceSlab Analysis.DerivativeRestriction
open Analysis.PolynomialEnvelope NaturalParameterJets

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def heatTimeMean (F : E → ℝ) (g : E → G) (p : ℝ × E) : G :=
  ∫ z, g z ∂Gibbs.heatPosterior F (conditionalVariance p.1) (p.1 • p.2)

def heatTimeCenterDerivative (F : E → ℝ) (g : E → G)
    (p : ℝ × E) : E →L[ℝ] G :=
  fderiv ℝ (fun c => ∫ z, g z ∂Gibbs.heatPosterior F (conditionalVariance p.1) c)
    (p.1 • p.2)

omit [CompleteSpace G] in
theorem heatTimeMean_eq_natural {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (g : E → G) {p : ℝ × E} (hp : p ∈ domain) :
    heatTimeMean F g p = normalizedGaussianIntegral F g (parameters p) := by
  have hh := integral_heatPosterior_eq_normalizedGaussianIntegral hF (le_refl 0)
    (conditionalVariance_pos hp.1 hp.2) (by simpa only [zero_mul] using hlo)
    g (p.1 • p.2)
  simpa only [heatTimeMean, posteriorParameters, parameters, precision, tiltScale,
    smul_smul, div_eq_mul_inv, mul_comm] using hh

theorem heatTimeCenterDerivative_eq_natural {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    {g : E → G} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k)
    {p : ℝ × E} (hp : p ∈ domain) :
    heatTimeCenterDerivative F g p = inverseVariance p.1 •
      (fderivWithin ℝ (normalizedGaussianIntegral F g) gaussianDomain
        (parameters p)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  rw [fderivWithin_of_isOpen isOpen_gaussianDomain
    (parameters_mem_gaussianDomain hp)]
  have hh := fderiv_heatPosterior_center_eq_natural hF hlo hg hA k hbound
    (conditionalVariance_pos hp.1 hp.2) (p.1 • p.2)
  simpa only [heatTimeCenterDerivative, posteriorParameters, parameters, precision,
    tiltScale, inverseVariance, smul_smul, div_eq_mul_inv, mul_comm] using hh

theorem contDiffOn_natural_mean {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    {g : E → G} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k) :
    ContDiffOn ℝ ∞ (normalizedGaussianIntegral F g) gaussianDomain := by
  exact contDiffOn_normalizedGaussianIntegral hF.continuous hg
    (hasGaussianMoments_of_convex_polynomial_growth hF hlo hg hA k hbound)
    (hasGaussianMoments_of_convex_polynomial_growth hF hlo
      (continuous_const : Continuous (fun _ : E => (1 : ℝ))) zero_le_one 0
      (by intro z; simp))

theorem contDiffOn_heatTimeMean {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    {g : E → G} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k) :
    ContDiffOn ℝ ∞ (heatTimeMean F g) domain := by
  have hQ := contDiffOn_natural_mean hF hlo hg hA k hbound
  exact (hQ.comp contDiffOn_parameters (fun p hp => parameters_mem_gaussianDomain hp)).congr
    (fun p hp => heatTimeMean_eq_natural hF hlo g hp)

def restrictedNaturalDerivative (Q : ℝ × E → G) (p : ℝ × E) : E →L[ℝ] G :=
  (fderivWithin ℝ Q gaussianDomain p).comp (ContinuousLinearMap.inr ℝ ℝ E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace G] in
theorem contDiffOn_restrictedNaturalDerivative {Q : ℝ × E → G}
    (hQ : ContDiffOn ℝ ∞ Q gaussianDomain) :
    ContDiffOn ℝ ∞ (restrictedNaturalDerivative Q) gaussianDomain := by
  exact (restrictDerivative (G := G) (ContinuousLinearMap.inr ℝ ℝ E)).contDiff.comp_contDiffOn
    (hQ.fderivWithin isOpen_gaussianDomain.uniqueDiffOn (by simp))

theorem contDiffOn_heatTimeCenterDerivative {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    {g : E → G} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k) :
    ContDiffOn ℝ ∞ (heatTimeCenterDerivative F g) domain := by
  have hD := (contDiffOn_restrictedNaturalDerivative
    (contDiffOn_natural_mean hF hlo hg hA k hbound)).comp contDiffOn_parameters
      (fun p hp => parameters_mem_gaussianDomain hp)
  have hη : ContDiffOn ℝ ∞ (fun p : ℝ × E => inverseVariance p.1) domain :=
    contDiffOn_inverseVariance.comp_continuousLinearMap (ContinuousLinearMap.fst ℝ ℝ E)
  exact (hη.smul hD).congr (fun p hp => heatTimeCenterDerivative_eq_natural hF hlo hg hA k hbound hp)

theorem exists_polynomial_heatTimeMean_jet_bound
    {F : E → ℝ} {L b : ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    {g : E → G} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (k n : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p : ℝ × E, p.1 ∈ Icc (left b) (right b) →
      ‖iteratedFDerivWithin ℝ n (heatTimeMean F g) domain p‖ ≤ C * (1 + ‖p‖) ^ N := by
  have hQ := contDiffOn_natural_mean hF hlo hg hA k hbound
  have hzero : (0 : ℝ) ∈ Icc (left b) (right b) := by
    dsimp [left, right]; constructor <;> linarith
  have ha : (2 : ℝ)⁻¹ ≤ (2 * varianceFloor b)⁻¹ := by
    have hh := precision_mem hb0 hb1 hzero
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one] using hh.2
  obtain ⟨C, hC, N, hb⟩ := exists_polynomial_parameter_comp_bound hb0 hb1 hQ n
    (fun i _ => exists_polynomial_normalizedGaussian_jet_bound hF hlo hhi
      (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) ha hg hA k i hbound)
  refine ⟨C, hC, N, ?_⟩
  intro p hp
  have heq : EqOn (heatTimeMean F g) (normalizedGaussianIntegral F g ∘ parameters)
      domain := fun q hq => heatTimeMean_eq_natural hF hlo g hq
  rw [iteratedFDerivWithin_congr heq (construction_subset hb0 hb1 hp) n]
  exact hb p hp

/-- The first-center derivative uses normalized natural jets through n+1.
The time coefficient is inverse variance and remains smooth at time zero. -/
theorem exists_polynomial_heatTimeCenterDerivative_jet_bound
    {F : E → ℝ} {L b : ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    {g : E → G} (hg : Continuous g) {A : ℝ} (hA : 0 ≤ A) (k n : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p : ℝ × E, p.1 ∈ Icc (left b) (right b) →
      ‖iteratedFDerivWithin ℝ n (heatTimeCenterDerivative F g) domain p‖ ≤
        C * (1 + ‖p‖) ^ N := by
  let Q := normalizedGaussianIntegral F g
  let D := restrictedNaturalDerivative Q
  let S : Set (ℝ × E) := Prod.fst ⁻¹' Icc (left b) (right b)
  have hSU : S ⊆ domain := fun p hp => construction_subset hb0 hb1 hp
  have hR : ∀ p ∈ S, 1 ≤ 1 + ‖p‖ :=
    fun p _ => le_add_of_nonneg_right (norm_nonneg p)
  have hQ := contDiffOn_natural_mean hF hlo hg hA k hbound
  have hD : ContDiffOn ℝ ∞ D gaussianDomain := contDiffOn_restrictedNaturalDerivative hQ
  have hH : ContDiffOn ℝ ∞ (D ∘ parameters) domain :=
    hD.comp contDiffOn_parameters (fun p hp => parameters_mem_gaussianDomain hp)
  have hη : ContDiffOn ℝ ∞ (fun p : ℝ × E => inverseVariance p.1) domain :=
    contDiffOn_inverseVariance.comp_continuousLinearMap (ContinuousLinearMap.fst ℝ ℝ E)
  have hzero : (0 : ℝ) ∈ Icc (left b) (right b) := by
    dsimp [left, right]; constructor <;> linarith
  have ha : (2 : ℝ)⁻¹ ≤ (2 * varianceFloor b)⁻¹ := by
    have hh := precision_mem hb0 hb1 hzero
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one] using hh.2
  have hDbound (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ a ∈ Icc ((2 : ℝ)⁻¹) ((2 * varianceFloor b)⁻¹), ∀ z : E,
      ‖iteratedFDerivWithin ℝ i D gaussianDomain (a, z)‖ ≤ C * (1 + ‖z‖) ^ N := by
    obtain ⟨C, hC, N, hb⟩ := exists_polynomial_normalizedGaussian_jet_bound
      hF hlo hhi (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) ha hg hA k (i + 1) hbound
    refine ⟨C, hC, N, ?_⟩
    intro a ha' z
    have hp : (a, z) ∈ gaussianDomain := (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹).trans_le ha'.1
    have hd := norm_iteratedFDerivWithin_restrict_fderivWithin_le
      isOpen_gaussianDomain.uniqueDiffOn hQ (ContinuousLinearMap.inr ℝ ℝ E) i hp
    have hnorm : ‖ContinuousLinearMap.inr ℝ ℝ E‖ ≤ 1 :=
      ContinuousLinearMap.norm_inr_le_one ℝ ℝ E
    have hd' := hd.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    calc
      _ ≤ ‖iteratedFDerivWithin ℝ (i + 1) Q gaussianDomain (a, z)‖ := by
        change ‖iteratedFDerivWithin ℝ i
          (fun q => (fderivWithin ℝ Q gaussianDomain q).comp
            (ContinuousLinearMap.inr ℝ ℝ E)) gaussianDomain (a, z)‖ ≤ _
        simpa only [Q, one_mul] using hd'
      _ ≤ _ := hb a ha' z
  obtain ⟨C, hC, N, hb⟩ := exists_polynomial_smul_jet_bound isOpen_domain.uniqueDiffOn
    hSU hη hH hR n
    (fun i _ => by
      obtain ⟨C, hC, hc⟩ := Analysis.CompactScalarJets.exists_uniform_jet_comp_linear_bound
        isOpen_Ioo isCompact_Icc (construction_subset hb0 hb1) contDiffOn_inverseVariance
        (ContinuousLinearMap.fst ℝ ℝ E) (ContinuousLinearMap.norm_fst_le ℝ ℝ E) i
      exact ⟨C, hC, 0, fun p hp => by
        simpa only [pow_zero, mul_one, ContinuousLinearMap.coe_fst', Function.comp_def, domain]
          using hc p hp⟩)
    (fun i _ => exists_polynomial_parameter_comp_bound hb0 hb1 hD i (fun j _ => hDbound j))
  refine ⟨C, hC, N, ?_⟩
  intro p hp
  have heq : EqOn (heatTimeCenterDerivative F g)
      (fun q => inverseVariance q.1 • (D ∘ parameters) q) domain :=
    fun q hq => heatTimeCenterDerivative_eq_natural hF hlo hg hA k hbound hq
  rw [iteratedFDerivWithin_congr heq (hSU hp) n]
  exact hb p hp

end AcceleratedLogConcave.Conditional.Tilt
