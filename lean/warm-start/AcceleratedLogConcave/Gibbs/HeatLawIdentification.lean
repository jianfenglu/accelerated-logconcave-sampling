import AcceleratedLogConcave.Gibbs.HeatDensityContinuity
import AcceleratedLogConcave.Kinetic.ReferenceFlow.GaussianDensity

/-!

-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal MeasureTheory
namespace AcceleratedLogConcave.Gibbs
open Kinetic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Exact Jacobian factor in the physical Gaussian density. -/
theorem heatGaussianPrefactor_eq_sqrt {t : ℝ} (ht : 0 < t) :
    heatGaussianPrefactor E t =
      (Real.sqrt t ^ Module.finrank ℝ E)⁻¹ *
        (Real.sqrt (2 * Real.pi))⁻¹ ^ Module.finrank ℝ E := by
  rw [heatGaussianPrefactor, Real.rpow_div_two_eq_sqrt _ (by positivity),
    Real.rpow_natCast, Real.sqrt_mul (by positivity), mul_pow, mul_inv_rev, inv_pow]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The rescaled standard Gaussian density is the exact heat kernel density. -/
theorem scaled_standardGaussianDensity {t : ℝ} (ht : 0 < t) (x : E) :
    (Real.sqrt t ^ Module.finrank ℝ E)⁻¹ *
      standardGaussianDensity ((Real.sqrt t)⁻¹ • x) = heatGaussianDensity t x := by
  rw [standardGaussianDensity, heatGaussianDensity, heatGaussianPrefactor_eq_sqrt ht]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg t)),
    mul_pow, inv_pow]
  rw [Real.sq_sqrt ht.le, ← mul_assoc]
  congr 1
  congr 1
  field_simp

/-- Actual measure pushforward of standard Gaussian scaling, with its full
Lebesgue density, not merely equality of candidate density functions. -/
theorem stdGaussian_map_sqrt_eq_heatDensity {t : ℝ} (ht : 0 < t) :
    (stdGaussian E).map (fun x => Real.sqrt t • x) =
      volume.withDensity (fun x : E => ENNReal.ofReal (heatGaussianDensity t x)) := by
  let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 (Real.sqrt t) (Real.sqrt_pos.mpr ht).ne')).toMeasurableEquiv
  let c : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt t ^ Module.finrank ℝ E)⁻¹)
  have he : MeasurePreserving e volume (c • volume) := by
    refine ⟨e.measurable, ?_⟩
    change volume.map (fun x : E => Real.sqrt t • x) = c • volume
    rw [Measure.map_addHaar_smul volume (Real.sqrt_pos.mpr ht).ne',
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg t) _))]
  rw [stdGaussian_eq_volume_density]
  change (volume.withDensity (fun x : E => ENNReal.ofReal (standardGaussianDensity x))).map e = _
  rw [map_withDensity_of_measurePreserving e volume (c • volume) he,
    withDensity_smul_measure, ← withDensity_smul' c _ (by exact ENNReal.ofReal_ne_top)]
  congr 1
  funext x
  change ENNReal.ofReal ((Real.sqrt t ^ Module.finrank ℝ E)⁻¹) *
    ENNReal.ofReal (standardGaussianDensity ((Real.sqrt t)⁻¹ • x)) = _
  rw [← ENNReal.ofReal_mul (by positivity), scaled_standardGaussianDensity ht]

/-- The independent product-map construction is actual convolution with the
scaled Gaussian measure. -/
theorem gaussian_product_map_eq_conv (μ : Measure E) [SFinite μ] (t : ℝ) :
    (μ.prod (stdGaussian E)).map (fun z => z.1 + Real.sqrt t • z.2) =
      μ ∗ ((stdGaussian E).map (fun x => Real.sqrt t • x)) := by
  rw [Measure.conv]
  have hp := Measure.map_prod_map μ (stdGaussian E) measurable_id
    (show Measurable (fun x : E => Real.sqrt t • x) by fun_prop)
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Pointwise convolution integrability follows from original curvature and
positive variance; this also rules out a totalized integral artifact. -/
theorem integrable_heatConvolution_integrand {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) (x : E) :
    Integrable (fun z => Real.exp (-F z) * heatGaussianDensity t (x - z)) := by
  have h := (integrable_posterior_of_hessian_lower hF hm ht x hlo).const_mul
    (heatGaussianPrefactor E t)
  apply h.congr
  filter_upwards [] with z
  rw [heatGaussianDensity, norm_sub_rev x z]
  rw [neg_add, Real.exp_add]
  ring

/-- The canonical heat Gibbs law equals the actual independent Gaussian
product pushforward. This is an equality of measures, with no law-identification
premise. Its right-hand side is exactly the definition of production heatedLaw. -/
theorem tilted_heatPotential_eq_gaussian_product_map {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hI : Integrable (fun z => Real.exp (-F z))) :
    volume.tilted (fun x => -heatPotential F t x) =
      ((volume.tilted (fun x => -F x)).prod (stdGaussian E)).map
        (fun z => z.1 + Real.sqrt t • z.2) := by
  let := isProbabilityMeasure_tilted hI
  have hFm : Measurable F := hF.continuous.measurable
  rw [gaussian_product_map_eq_conv, stdGaussian_map_sqrt_eq_heatDensity ht,
    Measure.tilted, Measure.tilted,
    conv_withDensity_eq_lconvolution (by fun_prop)
      (by unfold heatGaussianDensity; fun_prop)]
  congr 1
  funext x
  rw [exp_neg_heatPotential_eq_heatConvolution hF hm ht hlo,
    integral_exp_neg_heatPotential hF hm ht hlo hI]
  change ENNReal.ofReal (heatConvolution F t x / ∫ z, Real.exp (-F z)) =
    ∫⁻ z, ENNReal.ofReal (Real.exp (-F z) / ∫ y, Real.exp (-F y)) *
      ENNReal.ofReal (heatGaussianDensity t (-z + x))
  have hpos : 0 ≤ ∫ z, Real.exp (-F z) :=
    integral_nonneg (fun z => (Real.exp_pos _).le)
  have hn (z : E) : 0 ≤ Real.exp (-F z) / ∫ y, Real.exp (-F y) :=
    div_nonneg (Real.exp_pos _).le hpos
  simp_rw [← ENNReal.ofReal_mul (hn _), neg_add_eq_sub]
  have hi := (integrable_heatConvolution_integrand hF hm ht hlo x).div_const
    (∫ y, Real.exp (-F y))
  have hi' : Integrable (fun z => (Real.exp (-F z) / ∫ y, Real.exp (-F y)) *
      heatGaussianDensity t (x - z)) := by
    convert hi using 1
    funext z
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hi' (Filter.Eventually.of_forall (fun z =>
    mul_nonneg (hn z) (mul_nonneg (heatGaussianPrefactor_pos ht).le (Real.exp_pos _).le)))]
  congr 1
  change (∫ z, Real.exp (-F z) * heatGaussianDensity t (x - z)) /
    (∫ y, Real.exp (-F y)) = _
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

/-- Exact law identity on the arbitrary full closed analytic envelope. Strict
original lower curvature supplies base integrability, with no upper bound. -/
theorem tilted_heatPotential_eq_gaussian_product_map_envelope
    {F : E → ℝ} {m A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m) (hA : 0 < A)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    ∀ t ∈ Icc (3 * A / 4) R,
      volume.tilted (fun x => -heatPotential F t x) =
        ((volume.tilted (fun x => -F x)).prod (stdGaussian E)).map
          (fun z => z.1 + Real.sqrt t • z.2) := by
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  exact tilted_heatPotential_eq_gaussian_product_map hF hm.le ht0 hlo
    (integrable_exp_neg_of_hessian_lower hF hm hlo)

end AcceleratedLogConcave.Gibbs
