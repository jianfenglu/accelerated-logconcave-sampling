import Mathlib.Analysis.Calculus.ParametricIntegral
import AcceleratedLogConcave.Gibbs.PosteriorKernel
import AcceleratedLogConcave.Gibbs.IntegrationByParts
import AcceleratedLogConcave.Analysis.WeightedGradient.MeasureBridge
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Gaussian heat score dictionary

The score line of `sources/warm-start.tex`, posterior score calculus (lines 273–280).
The local variance-doubling envelope justifies differentiation in the center.
Normalization and moments come from `Gibbs.Posterior` and `Gibbs.PosteriorKernel`;
whole-space integration by parts derives the mean-base-score identity.
The Gaussian prefactor is retained in the heat convolution and removed only by
an explicit constant-log identity. No normalizability of `exp (-F)` is required.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace ENNReal ContDiff Topology Convolution

namespace AcceleratedLogConcave.Gibbs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gaussian tilt, differentiated in its center. -/
theorem hasFDerivAt_posterior_density_center (F : E → ℝ) (t : ℝ) (x y : E) :
    HasFDerivAt (fun z : E ↦ Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t))))
      ((-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (y - x))) y := by
  have h := (((hasFDerivAt_gaussian_regularizer t x y).const_add (F x)).neg).exp
  simpa only [Pi.neg_apply, smul_neg, neg_smul, norm_sub_rev] using h

omit [InnerProductSpace ℝ E] in
/-- A local shift of the center is absorbed by doubling the Gaussian variance. -/
theorem posterior_density_center_le_wider (F : E → ℝ) {t : ℝ} (ht : 0 < t)
    (x y z : E) (hz : ‖z - y‖ ≤ 1) :
    Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t))) ≤
      Real.exp (1 / (2 * t)) *
        Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (2 * t)))) := by
  have htri : ‖x - y‖ ≤ ‖x - z‖ + 1 :=
    (norm_sub_le_norm_sub_add_norm_sub x z y).trans (by linarith)
  have hsq : ‖x - y‖ ^ 2 ≤ 2 * ‖x - z‖ ^ 2 + 2 := by
    nlinarith [norm_nonneg (x - y), norm_nonneg (x - z), sq_nonneg (‖x - z‖ - 1)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd : 0 < 4 * t := by positivity
  have hscaled := (div_le_div_iff_of_pos_right hd).mpr hsq
  have heq : (2 * ‖x - z‖ ^ 2 + 2) / (4 * t) =
      ‖x - z‖ ^ 2 / (2 * t) + 1 / (2 * t) := by field_simp; ring
  rw [heq] at hscaled
  rw [show 2 * (2 * t) = 4 * t by ring]
  linarith

/-- A concrete envelope for center derivatives on the unit ball. -/
theorem norm_posterior_density_center_deriv_le (F : E → ℝ) {t : ℝ} (ht : 0 < t)
    (x y z : E) (hz : ‖z - y‖ ≤ 1) :
    ‖(-Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (z - x))‖ ≤
      (t⁻¹ * Real.exp (1 / (2 * t))) *
        ((‖x‖ + (‖y‖ + 1)) *
          Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (2 * t))))) := by
  have hzx : ‖z - x‖ ≤ ‖x‖ + (‖y‖ + 1) := by
    have hz' : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := norm_le_norm_sub_add z y
    have hzx' := norm_sub_le z x
    linarith
  rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),
    innerSL_apply_norm]
  calc
    _ ≤ (Real.exp (1 / (2 * t)) *
        Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (2 * t))))) *
        (t⁻¹ * (‖x‖ + (‖y‖ + 1))) := by
      gcongr
      exact posterior_density_center_le_wider F ht x y z hz
    _ = _ := by ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The envelope above is integrable from nonnegative base curvature alone. -/
theorem integrable_posterior_density_center_deriv_bound
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (y : E) (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    Integrable (fun x ↦ (t⁻¹ * Real.exp (1 / (2 * t))) *
      ((‖x‖ + (‖y‖ + 1)) *
        Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (2 * t)))))) := by
  have h0 := integrable_posterior_of_hessian_lower hF hm (by positivity : 0 < 2 * t) y hH
  have h1 := integrable_norm_pow_mul_posterior_of_hessian_lower hF hm
    (by positivity : 0 < 2 * t) y hH 1
  convert (h1.add (h0.const_mul (‖y‖ + 1))).const_mul
    (t⁻¹ * Real.exp (1 / (2 * t))) using 1
  ext x
  simp only [Pi.add_apply, pow_one, add_mul]

/-- Differentiation of the prefactor-free Gaussian partition, justified by one
integrable derivative bound on an entire neighborhood of the center. -/
theorem hasFDerivAt_posterior_partition
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (y : E) (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    HasFDerivAt
      (fun z ↦ ∫ x, Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t))))
      (∫ x, (-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (y - x))) y := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball y 1)
    (bound := fun x ↦ (t⁻¹ * Real.exp (1 / (2 * t))) *
      ((‖x‖ + (‖y‖ + 1)) *
        Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (2 * t))))))
    (Metric.ball_mem_nhds y zero_lt_one)
  · exact Eventually.of_forall fun z ↦ (by fun_prop : Continuous
      (fun x ↦ Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t))))).aestronglyMeasurable
  · exact integrable_posterior_of_hessian_lower hF hm ht y hH
  · exact (by fun_prop : Continuous (fun x ↦
      (-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (y - x)))).aestronglyMeasurable
  · filter_upwards [] with x z hz
    apply norm_posterior_density_center_deriv_le F ht x y z
    exact (by simpa only [Metric.mem_ball, dist_eq_norm] using hz : ‖z - y‖ < 1).le
  · exact integrable_posterior_density_center_deriv_bound hF hm ht y hH
  · filter_upwards [] with x z _
    exact hasFDerivAt_posterior_density_center F t x z

omit [MeasurableSpace E] [BorelSpace E] in
/-- The posterior score splits into the base score and the Gaussian score. -/
theorem gradient_posterior_potential {F : E → ℝ} (hF : Differentiable ℝ F)
    (t : ℝ) (y x : E) :
    gradient (fun z ↦ F z + ‖z - y‖ ^ 2 / (2 * t)) x =
      gradient F x + t⁻¹ • (x - y) := by
  apply ext_inner_left ℝ
  intro v
  simp only [inner_add_right, real_inner_smul_right, inner_gradient_right,
    conj_trivial]
  rw [fderiv_fun_add (hF x)
    (hasFDerivAt_gaussian_regularizer t y x).differentiableAt,
    (hasFDerivAt_gaussian_regularizer t y x).fderiv]
  simp only [add_apply, smul_apply,
    smul_eq_mul, innerSL_apply_apply]
  rw [real_inner_comm]

/-- The existing kernel is precisely the normalized exponential tilt. -/
theorem normalizedPosteriorKernel_eq_tilted {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E) :
    normalizedPosteriorKernel F (fun _ : E ↦ t) id hF.continuous.measurable
      measurable_const measurable_id y =
      volume.tilted (fun x ↦ -(F x + ‖x - y‖ ^ 2 / (2 * t))) := by
  exact ennreal_smul_withDensity_eq_tilted volume _
    (integrable_posterior_of_hessian_lower hF hm ht y hlo) _ rfl

/-- Integration by parts identifies the mean base score with the posterior
mean displacement. All integrability hypotheses follow from curvature and
Gaussian regularization, including when the base lower curvature is zero. -/
theorem integral_gradient_normalizedPosteriorKernel_eq {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y : E) :
    (∫ x, gradient F x ∂(normalizedPosteriorKernel F (fun _ : E ↦ t) id
      hF.continuous.measurable measurable_const measurable_id y)) =
      t⁻¹ • (y - ∫ x, x ∂(normalizedPosteriorKernel F (fun _ : E ↦ t) id
        hF.continuous.measurable measurable_const measurable_id y)) := by
  let R := normalizedPosteriorKernel F (fun _ : E ↦ t) id
    hF.continuous.measurable measurable_const measurable_id y
  have hR : R = volume.tilted (fun x ↦ -(F x + ‖x - y‖ ^ 2 / (2 * t))) :=
    normalizedPosteriorKernel_eq_tilted hF hm ht hlo y
  have hprob : IsProbabilityMeasure R :=
    normalized_posterior_isProbabilityMeasure_of_hessian_lower hF hm ht y hlo
  let := hprob
  have hsecond : Integrable (fun x : E ↦ ‖x‖ ^ 2) R :=
    normalizedPosteriorKernel_integrable_norm_pow hF hm hlo measurable_const
      measurable_id (fun _ ↦ ht) y 2
  have hfirst : Integrable (fun x : E ↦ x) R := by
    have hn := normalizedPosteriorKernel_integrable_norm_pow hF hm hlo
      measurable_const measurable_id (fun _ ↦ ht) y 1
    have hn' : Integrable (fun x : E ↦ ‖x‖) R := by
      simpa only [pow_one] using hn
    exact hn'.mono' continuous_id.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ ↦ le_rfl))
  have hp := contDiff_posterior_potential hF t y
  have hl := posterior_hessian_lower hF hlo t y
  have hu := posterior_hessian_upper hF hup t y
  have hpg : Integrable (gradient (fun x ↦ F x + ‖x - y‖ ^ 2 / (2 * t))) R := by
    rw [hR] at hsecond ⊢
    exact integrable_tilted_gradient_of_hessian_bounds hp hl hu hsecond
  have hlinear : Integrable (fun x ↦ t⁻¹ • (x - y)) R :=
    (hfirst.sub (integrable_const y)).smul t⁻¹
  have hbase : Integrable (gradient F) R := by
    convert! hpg.sub hlinear using 1
    ext x
    simp only [Pi.sub_apply, gradient_posterior_potential (hF.differentiable (by norm_num)),
      add_sub_cancel_right]
  have hzero : (∫ x, gradient (fun z ↦ F z + ‖z - y‖ ^ 2 / (2 * t)) x ∂R) = 0 := by
    rw [hR] at hsecond ⊢
    exact integral_tilted_gradient_eq_zero_of_hessian_bounds hp
      (integrable_posterior_of_hessian_lower hF hm ht y hlo) hl hu hsecond
  simp_rw [gradient_posterior_potential (hF.differentiable (by norm_num))] at hzero
  rw [integral_add hbase hlinear, integral_smul,
    integral_sub hfirst (integrable_const y)] at hzero
  simp only [integral_const, probReal_univ, one_smul] at hzero
  change (∫ x, gradient F x ∂R) = t⁻¹ • (y - ∫ x, x ∂R)
  rw [← neg_sub (∫ x, x ∂R) y, smul_neg]
  exact eq_neg_iff_add_eq_zero.mpr hzero

theorem integral_normalized_exp_neg {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {U : E → ℝ} (hU : Measurable U)
    (hI : Integrable (fun x ↦ Real.exp (-U x))) (g : E → G) :
    (∫ x, g x ∂((∫⁻ x, ENNReal.ofReal (Real.exp (-U x)))⁻¹ •
      volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-U x))))) =
      (∫ x, Real.exp (-U x))⁻¹ • ∫ x, Real.exp (-U x) • g x := by
  rw [integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (μ := volume)
      (f := fun x ↦ ENNReal.ofReal (Real.exp (-U x)))
      (by fun_prop) (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) g]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal, (Real.exp_pos _).le]
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)]
  rw [ENNReal.toReal_ofReal (integral_exp_pos hI).le]

/-- The exact Lebesgue-density normalizer for covariance `t I`. -/
def heatGaussianPrefactor (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (t : ℝ) : ℝ :=
  ((2 * Real.pi * t) ^ (Module.finrank ℝ E / 2 : ℝ))⁻¹

/-- Centered Gaussian density at physical variance `t`. -/
def heatGaussianDensity (t : ℝ) (x : E) : ℝ :=
  heatGaussianPrefactor E t * Real.exp (-(‖x‖ ^ 2 / (2 * t)))

omit [MeasurableSpace E] [BorelSpace E] in
theorem heatGaussianPrefactor_pos {t : ℝ} (ht : 0 < t) :
    0 < heatGaussianPrefactor E t := by
  unfold heatGaussianPrefactor
  positivity

theorem integral_heatGaussianDensity {t : ℝ} (ht : 0 < t) :
    ∫ x : E, heatGaussianDensity t x = 1 := by
  have hbase : 0 < 2 * Real.pi * t := by positivity
  have hraw : (∫ x : E, Real.exp (-(‖x‖ ^ 2 / (2 * t)))) =
      (2 * Real.pi * t) ^ (Module.finrank ℝ E / 2 : ℝ) := by
    convert GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := E) (b := 1 / (2 * t)) (by positivity) using 1
    · congr 1
      ext x
      congr 1
      ring
    · congr 1
      field_simp
  simp only [heatGaussianDensity, integral_const_mul, hraw, heatGaussianPrefactor]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hbase _).ne'

/-- This identity is purely algebraic: no base-density integrability is assumed. -/
theorem convolution_heatGaussianDensity (F : E → ℝ) (t : ℝ) (y : E) :
    ((fun x ↦ Real.exp (-F x)) ⋆ (heatGaussianDensity t)) y =
      heatGaussianPrefactor E t *
        ∫ x : E, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))) := by
  change (∫ x : E, Real.exp (-F x) * heatGaussianDensity t (y - x)) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [heatGaussianDensity, norm_sub_rev y x]
  rw [← mul_assoc, mul_comm (Real.exp (-F x)), mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The Gaussian convolution, expressed by its Lebesgue density. -/
def heatConvolution (F : E → ℝ) (t : ℝ) (y : E) : ℝ :=
  ((fun x ↦ Real.exp (-F x)) ⋆ (heatGaussianDensity t)) y

def heatPotential (F : E → ℝ) (t : ℝ) : E → ℝ :=
  fun y ↦ -Real.log (heatConvolution F t y)

theorem heatConvolution_eq_prefactor_mul_partition (F : E → ℝ) (t : ℝ) (y : E) :
    heatConvolution F t y = heatGaussianPrefactor E t *
      ∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))) :=
  convolution_heatGaussianDensity F t y

theorem heatPotential_eq_neg_log_partition {F : E → ℝ} {t : ℝ}
    (ht : 0 < t) (y : E)
    (hI : Integrable (fun x ↦ Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))))) :
    heatPotential F t y =
      -Real.log (∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) -
        Real.log (heatGaussianPrefactor E t) := by
  rw [heatPotential, heatConvolution_eq_prefactor_mul_partition,
    Real.log_mul (heatGaussianPrefactor_pos ht).ne' (integral_exp_pos hI).ne']
  ring

/-- The negative log of the prefactor-free partition has the posterior
mean-displacement gradient. The derivative exchange is proved above. -/
theorem hasGradientAt_neg_log_posterior_partition
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E) :
    HasGradientAt
      (fun z ↦ -Real.log (∫ x, Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t)))))
      (t⁻¹ • (y - ∫ x, x ∂(normalizedPosteriorKernel F (fun _ : E ↦ t) id
        hF.continuous.measurable measurable_const measurable_id y))) y := by
  let R := normalizedPosteriorKernel F (fun _ : E ↦ t) id
    hF.continuous.measurable measurable_const measurable_id y
  let Z := ∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))
  let W := fun x ↦ Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))
  have hI := integrable_posterior_of_hessian_lower hF hm ht y hlo
  have hprob : IsProbabilityMeasure R :=
    normalized_posterior_isProbabilityMeasure_of_hessian_lower hF hm ht y hlo
  let := hprob
  have hfirst : Integrable (fun x : E ↦ x) R := by
    have hn := normalizedPosteriorKernel_integrable_norm_pow hF hm hlo
      measurable_const measurable_id (fun _ ↦ ht) y 1
    exact (by simpa only [pow_one] using hn : Integrable (fun x : E ↦ ‖x‖) R).mono'
      continuous_id.aestronglyMeasurable (Filter.Eventually.of_forall fun _ ↦ le_rfl)
  have hratio : (∫ x, innerSL ℝ (y - x) ∂R) =
      Z⁻¹ • ∫ x, W x • innerSL ℝ (y - x) :=
    integral_normalized_exp_neg (hF.continuous.measurable.add (by fun_prop)) hI _
  have hdual : innerSL ℝ (y - ∫ x, x ∂R) = ∫ x, innerSL ℝ (y - x) ∂R := by
    have he := (innerSL ℝ (E := E)).integral_comp_comm
      ((integrable_const y).sub hfirst)
    simp only [Pi.sub_apply] at he
    rw [integral_sub (integrable_const y) hfirst] at he
    simpa only [integral_const, probReal_univ, one_smul] using he.symm
  have hd := ((hasFDerivAt_posterior_partition hF hm ht y hlo).log
    (integral_exp_pos hI).ne').neg
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hd using 1
  change InnerProductSpace.toDual ℝ E (t⁻¹ • (y - ∫ x, x ∂R)) =
    -(Z⁻¹ • ∫ x, (-W x) • (t⁻¹ • innerSL ℝ (y - x)))
  rw [map_smul]
  change t⁻¹ • innerSL ℝ (y - ∫ x, x ∂R) =
    -(Z⁻¹ • ∫ x, (-W x) • (t⁻¹ • innerSL ℝ (y - x)))
  rw [hdual, hratio]
  have hfun : (fun x ↦ (-W x) • (t⁻¹ • innerSL ℝ (y - x))) =
      fun x ↦ -(t⁻¹ • (W x • innerSL ℝ (y - x))) := by
    funext x
    rw [neg_smul, smul_comm]
  rw [hfun, integral_neg, integral_smul, smul_neg, neg_neg, smul_comm]

/-- The heat potential retains the Gaussian prefactor in its definition;
its center derivative is unaffected by that positive constant. -/
theorem hasGradientAt_heatPotential
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E) :
    HasGradientAt (heatPotential F t)
      (t⁻¹ • (y - ∫ x, x ∂(normalizedPosteriorKernel F (fun _ : E ↦ t) id
        hF.continuous.measurable measurable_const measurable_id y))) y := by
  have heq : heatPotential F t = fun z ↦
      -Real.log (∫ x, Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t)))) -
        Real.log (heatGaussianPrefactor E t) := by
    funext z
    exact heatPotential_eq_neg_log_partition ht z
      (integrable_posterior_of_hessian_lower hF hm ht z hlo)
  rw [heq]
  apply hasGradientAt_iff_hasFDerivAt.mpr
  exact (hasGradientAt_neg_log_posterior_partition hF hm ht hlo y).hasFDerivAt.sub_const _

/-- The score dictionary from the warm-start manuscript, with all analytic
hypotheses derived from C² two-sided curvature and positive Gaussian time.
Zero base curvature is allowed; the base Gibbs density need not be integrable. -/
theorem heat_score_dictionary
    {F : E → ℝ} {m L t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y : E) :
    gradient (heatPotential F t) y =
      (∫ x, gradient F x ∂(normalizedPosteriorKernel F (fun _ : E ↦ t) id
        hF.continuous.measurable measurable_const measurable_id y)) ∧
    gradient (heatPotential F t) y =
      t⁻¹ • (y - ∫ x, x ∂(normalizedPosteriorKernel F (fun _ : E ↦ t) id
        hF.continuous.measurable measurable_const measurable_id y)) := by
  have hscore := (hasGradientAt_heatPotential hF hm ht hlo y).gradient
  exact ⟨hscore.trans (integral_gradient_normalizedPosteriorKernel_eq hF hm ht hlo hup y).symm,
    hscore⟩

end AcceleratedLogConcave.Gibbs
