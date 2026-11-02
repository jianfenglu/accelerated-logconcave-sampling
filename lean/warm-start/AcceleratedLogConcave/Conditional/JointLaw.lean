import AcceleratedLogConcave.Conditional.Joint.Algebra
import AcceleratedLogConcave.Conditional.PrimitivePullback
import AcceleratedLogConcave.Channels.EqualWidthBridge
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The actual interpolation joint and its reverse conditional law

The forward channel draws `ρ z + sqrt (1 - ρ²) n`. Gaussian square completion
identifies its reverse kernel with the normalized ENNReal posterior from
`Conditional.Definitions`. In particular the argument applies at ρ = 0.
-/

noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory ProbabilityTheory Gibbs Channels
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The interpolation channel with the original latent position retained. -/
def interpolationKernel (ρ : ℝ) : Kernel E E :=
  (forwardKernel (conditionalVariance ρ).toNNReal).comap (fun z ↦ ρ • z) (by fun_prop)

instance (ρ : ℝ) : IsMarkovKernel (interpolationKernel (ι := ι) ρ) := by
  unfold interpolationKernel
  infer_instance

/-- The reverse kernel is exactly the posterior used to define conditional means. -/
def conditionalKernel (F : E → ℝ) (x : E) (r ρ : ℝ)
    (hB : Measurable (primitivePotential F x r)) : Kernel E E :=
  normalizedPosteriorKernel (primitivePotential F x r)
    (fun _ : E ↦ conditionalVariance ρ) (fun y ↦ ρ • y)
      hB measurable_const (by fun_prop)

omit [DecidableEq ι] in
@[simp] theorem conditionalKernel_apply (F : E → ℝ) (x : E) (r ρ : ℝ)
    (hB : Measurable (primitivePotential F x r)) (y : E) :
    conditionalKernel F x r ρ hB y = conditionalLaw F x r ρ y := rfl

lemma interpolationKernel_apply (ρ : ℝ) (hv : 0 ≤ conditionalVariance ρ) (z : E) :
    interpolationKernel ρ z = (stdGaussian E).map
      (fun n ↦ ρ • z + Real.sqrt (conditionalVariance ρ) • n) := by
  rw [interpolationKernel, Kernel.comap_apply, forwardKernel_apply,
    noise_eq_scaled_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Real.coe_toNNReal _ hv]
  rfl

lemma interpolationKernel_eq_withDensity (ρ : ℝ) (hv : 0 < conditionalVariance ρ)
    (z : E) :
    interpolationKernel ρ z = volume.withDensity
      (fun y ↦ ENNReal.ofReal
        (Real.exp (-‖y - ρ • z‖ ^ 2 / (2 * conditionalVariance ρ)) /
          ∫ n : E, Real.exp (-‖n‖ ^ 2 / (2 * conditionalVariance ρ)))) := by
  rw [interpolationKernel, Kernel.comap_apply,
    forwardKernel_eq_withDensity _ (Real.toNNReal_pos.mpr hv)]
  simp only [Real.coe_toNNReal _ hv.le]

/-- The channel marginal is the independent-noise interpolation from Definitions. -/
theorem interpolationKernel_comp (F : E → ℝ) (x : E) (r ρ : ℝ)
    (hv : 0 ≤ conditionalVariance ρ) :
    interpolationKernel ρ ∘ₘ baseLaw F x r = interpolationLaw F x r ρ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,
    interpolationLaw, lintegral_map hf (by unfold interpolationMap; fun_prop),
    lintegral_prod _ (by unfold interpolationMap; fun_prop)]
  apply lintegral_congr
  intro z
  rw [interpolationKernel_apply ρ hv z, lintegral_map hf (by fun_prop)]
  rfl

omit [DecidableEq ι] in
/-- An integrable ENNReal-normalized posterior is the usual exponential tilt. -/
lemma heatPosterior_eq_tilted_of_integrable {B : E → ℝ} {t : ℝ} (y : E)
    (hI : Integrable (fun z ↦ Real.exp (-(B z + ‖z - y‖ ^ 2 / (2 * t))))) :
    heatPosterior B t y = volume.tilted
      (fun z ↦ -(B z + ‖z - y‖ ^ 2 / (2 * t))) :=
  ennreal_smul_withDensity_eq_tilted volume _ hI _ rfl

omit [DecidableEq ι] in
lemma baseLaw_eq_tilted_of_integrable {F : E → ℝ} (x : E) (r : ℝ)
    (hI : Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2)))) :
    baseLaw F x r = volume.tilted
      (fun z ↦ -(primitivePotential F x r z + ‖z‖ ^ 2 / 2)) := by
  have hI' : Integrable (fun z ↦ Real.exp
      (-(primitivePotential F x r z + ‖z - 0‖ ^ 2 / (2 * 1)))) := by simpa using hI
  simpa [baseLaw] using heatPosterior_eq_tilted_of_integrable 0 hI'

omit [DecidableEq ι] in
lemma baseLaw_isProbabilityMeasure_of_integrable {F : E → ℝ} (x : E) (r : ℝ)
    (hI : Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2)))) :
    IsProbabilityMeasure (baseLaw F x r) := by
  rw [baseLaw_eq_tilted_of_integrable x r hI]
  exact isProbabilityMeasure_tilted hI

omit [DecidableEq ι] in
/-- Square completion identifies the likelihood tilt, without an assumed Bayes identity. -/
lemma conditionalLaw_eq_likelihood_tilt {F : E → ℝ} (x : E) (r ρ : ℝ)
    (hv : 0 < conditionalVariance ρ)
    (hI : Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2))))
    (y : E)
    (hP : Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z +
      ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ))))) :
    conditionalLaw F x r ρ y = (baseLaw F x r).tilted
      (fun z ↦ -‖y - ρ • z‖ ^ 2 / (2 * conditionalVariance ρ)) := by
  rw [baseLaw_eq_tilted_of_integrable x r hI, tilted_tilted hI]
  have hprob := isProbabilityMeasure_tilted hP
  have hshift := tilted_tilted hP (fun _ ↦ -‖y‖ ^ 2 / 2)
  rw [tilted_const] at hshift
  rw [conditionalLaw, heatPosterior_eq_tilted_of_integrable _ hP, hshift]
  congr 1
  ext z
  exact (conditional_exponent_completion _ ρ hv.ne' z y).symm

/-- The normalized Gaussian likelihood, with respect to Lebesgue measure. -/
def interpolationLikelihood (ρ : ℝ) (z y : E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-‖y - ρ • z‖ ^ 2 / (2 * conditionalVariance ρ)) /
    ∫ n : E, Real.exp (-‖n‖ ^ 2 / (2 * conditionalVariance ρ)))

omit [DecidableEq ι] in
lemma interpolation_weight_integrable (μ : Measure E) [IsFiniteMeasure μ]
    (ρ : ℝ) (hv : 0 < conditionalVariance ρ) (y : E) :
    Integrable (fun z ↦ Real.exp (-‖y - ρ • z‖ ^ 2 / (2 * conditionalVariance ρ))) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall ?_)
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

omit [DecidableEq ι] in
lemma conditionalKernel_isMarkov_of_integrable {F : E → ℝ} (x : E) (r ρ : ℝ)
    (hB : Measurable (primitivePotential F x r))
    (hP : ∀ y : E, Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z +
      ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ))))) :
    IsMarkovKernel (conditionalKernel F x r ρ hB) := by
  constructor
  intro y
  exact normalized_exp_neg_isProbabilityMeasure (hP y)

/-- The actual joint law of latent position and interpolation output. -/
def interpolationJoint (F : E → ℝ) (x : E) (r ρ : ℝ) : Measure (E × E) :=
  baseLaw F x r ⊗ₘ interpolationKernel ρ

/-- The joint retains the latent position alongside its independent Gaussian interpolation. -/
theorem interpolationJoint_eq_map {F : E → ℝ} (x : E) (r ρ : ℝ)
    (hv : 0 ≤ conditionalVariance ρ)
    (hI : Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2)))) :
    interpolationJoint F x r ρ = ((baseLaw F x r).prod (stdGaussian E)).map
      (fun p ↦ (p.1, interpolationMap ρ p)) := by
  have := baseLaw_isProbabilityMeasure_of_integrable x r hI
  apply Measure.ext_of_lintegral
  intro f hf
  rw [interpolationJoint, Measure.lintegral_compProd hf,
    lintegral_map hf (by unfold interpolationMap; fun_prop),
    lintegral_prod _ (by unfold interpolationMap; fun_prop)]
  apply lintegral_congr
  intro z
  rw [interpolationKernel_apply ρ hv z, lintegral_map (by fun_prop) (by fun_prop)]
  rfl

/-- The interpolation density is its Gaussian likelihood averaged against the actual base law. -/
theorem interpolationLaw_eq_withDensity {F : E → ℝ} (x : E) (r ρ : ℝ)
    (hv : 0 < conditionalVariance ρ)
    (hI : Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2)))) :
    interpolationLaw F x r ρ = volume.withDensity
      (fun y ↦ ∫⁻ z, interpolationLikelihood ρ z y ∂baseLaw F x r) := by
  have := baseLaw_isProbabilityMeasure_of_integrable x r hI
  rw [← interpolationKernel_comp F x r ρ hv.le]
  exact marginal_density (by unfold interpolationLikelihood; fun_prop)
    (fun z ↦ interpolationKernel_eq_withDensity ρ hv z)

/-- The conditional posterior is the genuine reverse kernel of the interpolation joint. -/
theorem conditionalKernel_bayes_joint_of_integrable {F : E → ℝ} (x : E) (r ρ : ℝ)
    (hB : Measurable (primitivePotential F x r))
    (hv : 0 < conditionalVariance ρ)
    (hI : Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2))))
    (hP : ∀ y : E, Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z +
      ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ))))) :
    interpolationLaw F x r ρ ⊗ₘ conditionalKernel F x r ρ hB =
      (interpolationJoint F x r ρ).map Prod.swap := by
  have := baseLaw_isProbabilityMeasure_of_integrable x r hI
  have := conditionalKernel_isMarkov_of_integrable x r ρ hB hP
  rw [← interpolationKernel_comp F x r ρ hv.le]
  let C : ℝ := ∫ n : E, Real.exp (-‖n‖ ^ 2 / (2 * conditionalVariance ρ))
  have hC : 0 < C := by
    simpa only [C, Real.coe_toNNReal _ hv.le] using
      gaussian_normalizer_pos (ι := ι) (conditionalVariance ρ).toNNReal
        (Real.toNNReal_pos.mpr hv)
  apply bayes_joint (ν := volume) (f := interpolationLikelihood ρ)
    (by unfold interpolationLikelihood; fun_prop)
    (fun z ↦ interpolationKernel_eq_withDensity ρ hv z)
  · intro y
    rw [conditionalKernel_apply, conditionalLaw_eq_likelihood_tilt x r ρ hv hI y (hP y)]
    exact (normalized_likelihood_eq_tilted _ _
      (interpolation_weight_integrable _ ρ hv y) C hC).symm
  · intro y
    exact (likelihood_lintegral_pos _ _
      (interpolation_weight_integrable _ ρ hv y) C hC).ne'
  · intro y
    exact likelihood_lintegral_ne_top _ _
      (interpolation_weight_integrable _ ρ hv y) C hC

omit [DecidableEq ι] in
lemma conditional_posterior_integrable {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (hv : 0 < conditionalVariance ρ) (y : E) :
    Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z +
      ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ)))) := by
  exact integrable_posterior_of_hessian_lower (contDiff_primitivePotential hF x r)
    (m := 0) le_rfl hv (ρ • y) (by
      simpa using primitivePotential_hessian_nonneg hF hlo x r)

omit [DecidableEq ι] in
lemma base_posterior_integrable {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a) (x : E) (r : ℝ) :
    Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2))) := by
  simpa using conditional_posterior_integrable hF hlo x r 0 (by norm_num) (0 : E)

omit [DecidableEq ι] in
lemma conditionalKernel_isMarkov {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (hv : 0 < conditionalVariance ρ) :
    IsMarkovKernel (conditionalKernel F x r ρ
      (contDiff_primitivePotential hF x r).continuous.measurable) :=
  conditionalKernel_isMarkov_of_integrable x r ρ _
    (conditional_posterior_integrable hF hlo x r ρ hv)

/-- Actual C² convex potentials give the complete interpolation disintegration.
No regularity of the original potential beyond order two is used. -/
theorem conditionalKernel_bayes_joint {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (hv : 0 < conditionalVariance ρ) :
    interpolationLaw F x r ρ ⊗ₘ conditionalKernel F x r ρ
        (contDiff_primitivePotential hF x r).continuous.measurable =
      (interpolationJoint F x r ρ).map Prod.swap :=
  conditionalKernel_bayes_joint_of_integrable x r ρ _ hv
    (base_posterior_integrable hF hlo x r)
    (conditional_posterior_integrable hF hlo x r ρ hv)

omit [DecidableEq ι] in
lemma baseLaw_isProbabilityMeasure {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a) (x : E) (r : ℝ) :
    IsProbabilityMeasure (baseLaw F x r) :=
  baseLaw_isProbabilityMeasure_of_integrable x r (base_posterior_integrable hF hlo x r)

omit [DecidableEq ι] in
lemma interpolationLaw_isProbabilityMeasure {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a) (x : E) (r ρ : ℝ) :
    IsProbabilityMeasure (interpolationLaw F x r ρ) := by
  have := baseLaw_isProbabilityMeasure hF hlo x r
  unfold interpolationLaw
  exact Measure.isProbabilityMeasure_map_iff (by unfold interpolationMap; fun_prop) |>.mpr inferInstance

omit [DecidableEq ι] in
/-- At probability time zero the output is an independent standard Gaussian. -/
theorem interpolationLaw_zero {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a) (x : E) (r : ℝ) :
    interpolationLaw F x r 0 = stdGaussian E := by
  have := baseLaw_isProbabilityMeasure hF hlo x r
  have hm : (interpolationMap 0 : E × E → E) = Prod.snd := by
    ext p
    simp [interpolationMap]
  rw [interpolationLaw, hm, Measure.map_snd_prod, measure_univ, one_smul]

/-- The retained joint at zero is exactly the independent product. -/
theorem interpolationJoint_zero {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a) (x : E) (r : ℝ) :
    interpolationJoint F x r 0 = (baseLaw F x r).prod (stdGaussian E) := by
  rw [interpolationJoint_eq_map x r 0 (by norm_num)
    (base_posterior_integrable hF hlo x r)]
  simp [interpolationMap, conditionalVariance]

/-- The Bayes joint identity as an equality of iterated nonnegative expectations. -/
theorem conditional_disintegration_lintegral {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (hv : 0 < conditionalVariance ρ)
    (g : E × E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, ∫⁻ z, g (y, z) ∂conditionalLaw F x r ρ y ∂interpolationLaw F x r ρ) =
      ∫⁻ z, ∫⁻ n, g (ρ • z + Real.sqrt (conditionalVariance ρ) • n, z)
        ∂stdGaussian E ∂baseLaw F x r := by
  have := baseLaw_isProbabilityMeasure hF hlo x r
  have := conditionalKernel_isMarkov hF hlo x r ρ hv
  have := interpolationLaw_isProbabilityMeasure hF hlo x r ρ
  change (∫⁻ y, ∫⁻ z, g (y, z) ∂conditionalKernel F x r ρ
    (contDiff_primitivePotential hF x r).continuous.measurable y
    ∂interpolationLaw F x r ρ) = _
  rw [← Measure.lintegral_compProd hg, conditionalKernel_bayes_joint hF hlo x r ρ hv,
    lintegral_map hg measurable_swap, interpolationJoint_eq_map x r ρ hv.le
      (base_posterior_integrable hF hlo x r),
    lintegral_map (by fun_prop) (by unfold interpolationMap; fun_prop),
    lintegral_prod _ (by unfold interpolationMap; fun_prop)]
  rfl

/-- The full reverse joint is the swapped independent-noise interpolation. -/
theorem conditional_joint_eq_map {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (hv : 0 < conditionalVariance ρ) :
    interpolationLaw F x r ρ ⊗ₘ conditionalKernel F x r ρ
        (contDiff_primitivePotential hF x r).continuous.measurable =
      ((baseLaw F x r).prod (stdGaussian E)).map
        (fun p ↦ (interpolationMap ρ p, p.1)) := by
  rw [conditionalKernel_bayes_joint hF hlo x r ρ hv,
    interpolationJoint_eq_map x r ρ hv.le (base_posterior_integrable hF hlo x r),
    Measure.map_map measurable_swap (by unfold interpolationMap; fun_prop)]
  rfl

/-- Bochner averaging against the actual conditional law equals averaging the
retained independent Gaussian interpolation. -/
theorem conditional_disintegration_integral {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (hv : 0 < conditionalVariance ρ)
    (g : E × E → H) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun p ↦ g (interpolationMap ρ p, p.1))
      ((baseLaw F x r).prod (stdGaussian E))) :
    (∫ y, ∫ z, g (y, z) ∂conditionalLaw F x r ρ y ∂interpolationLaw F x r ρ) =
      ∫ p, g (interpolationMap ρ p, p.1)
        ∂((baseLaw F x r).prod (stdGaussian E)) := by
  have := baseLaw_isProbabilityMeasure hF hlo x r
  have := conditionalKernel_isMarkov hF hlo x r ρ hv
  have := interpolationLaw_isProbabilityMeasure hF hlo x r ρ
  have hm : Measurable (fun p : E × E ↦ (interpolationMap ρ p, p.1)) := by
    unfold interpolationMap
    fun_prop
  have hInt : Integrable g (interpolationLaw F x r ρ ⊗ₘ
      conditionalKernel F x r ρ (contDiff_primitivePotential hF x r).continuous.measurable) := by
    rw [conditional_joint_eq_map hF hlo x r ρ hv]
    exact (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).mpr hgi
  change (∫ y, ∫ z, g (y, z) ∂conditionalKernel F x r ρ
    (contDiff_primitivePotential hF x r).continuous.measurable y
    ∂interpolationLaw F x r ρ) = _
  rw [← Measure.integral_compProd hInt, conditional_joint_eq_map hF hlo x r ρ hv,
    integral_map_of_stronglyMeasurable hm hg]

end AcceleratedLogConcave.Conditional
