import AcceleratedLogConcave.Gibbs.HeatDensityVelocity
import AcceleratedLogConcave.Gibbs.HeatJointRegularity
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.OriginalHeatLocal

/-!
# Actual heat-density continuity equation from original data

Dominated natural-parameter differentiation gives the variance derivative of
the raw Gaussian posterior partition. Dominated center differentiation and
orthonormal-basis summation give the opposite flux divergence for the exact
canonical density and scale -1/2. Their cancellation closes the old
OriginalHeatEvolutionData record, not the separate heated-law identification,
VarianceHeatFamily adapter, or downstream sampler theorem.
-/

noncomputable section
open MeasureTheory Set Function InnerProductSpace Filter
open scoped RealInnerProductSpace ContDiff Topology

namespace AcceleratedLogConcave.Gibbs
open Conditional.Tilt Analysis.Poisson Kinetic.Reheating

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Exact raw partition in natural Gaussian parameters, including the totalized
zero-variance algebraic identity. Differentiation below uses positive variance. -/
theorem posteriorPartition_eq_natural (F : E → ℝ) (t : ℝ) (x : E) :
    (∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t)))) =
      Real.exp (-‖x‖ ^ 2 / (2 * t)) *
        gaussianIntegral F (fun _ => (1 : ℝ)) (posteriorParameters (t, x)) := by
  by_cases ht : t = 0
  · simp [ht, gaussianIntegral, posteriorParameters, gaussianStatistic_apply]
  · simp_rw [posterior_density_eq_natural F t x _ ht]
    simp only [gaussianIntegral, smul_eq_mul, mul_one, integral_const_mul]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Actual variance derivative of the physical Gaussian prefactor. -/
theorem hasDerivAt_heatGaussianPrefactor {t : ℝ} (ht : 0 < t) :
    HasDerivAt (heatGaussianPrefactor E)
      (-(Module.finrank ℝ E / (2 * t)) * heatGaussianPrefactor E t) t := by
  have hb : 2 * Real.pi * t ≠ 0 := (show 0 < 2 * Real.pi * t by positivity).ne'
  have hd := (((hasDerivAt_id t).const_mul (2 * Real.pi)).rpow_const
    (p := (Module.finrank ℝ E / 2 : ℝ)) (Or.inl hb)).inv
      (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi * t) _).ne'
  convert hd using 1
  · rfl
  · simp only [heatGaussianPrefactor, id_eq, Real.rpow_sub_one hb]
    field_simp [ht.ne', Real.pi_ne_zero,
      (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi * t)
        (Module.finrank ℝ E / 2 : ℝ)).ne']

/-- Integrable quadratic displacement under the raw posterior weight. -/
theorem integrable_posterior_sq_displacement {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) (x : E) :
    Integrable (fun z => Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t))) * ‖z - x‖ ^ 2) := by
  simpa only [smul_eq_mul] using
    integrable_polynomial_mul_posterior hF hm ht hlo x
      (g := fun z => ‖z - x‖ ^ 2) (by fun_prop) (2 * ‖x‖ ^ 2) 2 2 (by
        intro z
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h := norm_sub_le z x
        nlinarith [norm_nonneg (z - x), norm_nonneg z, norm_nonneg x,
          sq_nonneg (‖z‖ - ‖x‖)])

/-- Genuine time derivative of the raw Gaussian posterior partition. The
existing dominated natural-parameter derivative theorem supplies the exchange. -/
theorem hasDerivAt_posterior_partition_time {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) (x : E) :
    HasDerivAt (fun s => ∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * s))))
      (∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t))) *
        (‖z - x‖ ^ 2 / (2 * t ^ 2))) t := by
  have hlower (z : E) : F 0 + inner ℝ (gradient F 0) z ≤ F z := by
    have hh := quadratic_lower_bound_of_hessian_lower hF hlo z
    rw [← inner_gradient_left] at hh
    have hn : 0 ≤ m / 2 * ‖z‖ ^ 2 := by positivity
    linarith
  have h1 := hasGaussianMoments_of_polynomial_growth hF.continuous
    (continuous_const : Continuous (fun _ : E => (1 : ℝ)))
    (F 0) (gradient F 0) hlower 1 0 0 (by intro z; simp)
  let p := posteriorParameters (t, x)
  have hp : 0 < p.1 := inv_pos.mpr (mul_pos (by norm_num) ht)
  let v : ℝ × E := (-((2 * t ^ 2)⁻¹), (-(t ^ 2)⁻¹) • x)
  have ha : HasDerivAt (fun s : ℝ => (2 * s)⁻¹) (-((2 * t ^ 2)⁻¹)) t := by
    convert ((hasDerivAt_id t).const_mul 2).inv (mul_ne_zero (by norm_num) ht.ne') using 1
    · rfl
    · simp only [id_eq]
      field_simp
  have hb := (hasDerivAt_inv ht.ne').smul_const x
  have hparam : HasDerivAt (fun s => posteriorParameters (s, x)) v t := ha.prodMk hb
  have hn := (hasFDerivAt_gaussianIntegral hF.continuous continuous_const h1 p hp).comp_hasDerivAt t hparam
  have hk : HasDerivAt (fun s : ℝ => Real.exp (-‖x‖ ^ 2 / (2 * s)))
      (Real.exp (-‖x‖ ^ 2 / (2 * t)) * (‖x‖ ^ 2 / (2 * t ^ 2))) t := by
    convert (((hasDerivAt_const t (-‖x‖ ^ 2)).div ((hasDerivAt_id t).const_mul 2)
      (mul_ne_zero (by norm_num) ht.ne')).exp) using 1
    · rfl
    · simp only [id_eq, Pi.div_apply]
      field_simp
      ring
  have hz := integrable_gaussian_integrand hF.continuous continuous_const h1 p hp
  have hc : Continuous (fun z : E => (gaussianStatistic z).smulRight (1 : ℝ)) :=
    isBoundedBilinearMap_smulRight.continuous.comp
      ((continuous_gaussianStatistic (E := E)).prodMk continuous_const)
  have hstat := integrable_gaussian_integrand hF.continuous hc
    (h1.statistic hF.continuous continuous_const) p hp
  have hv := (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp hstat
  change Integrable (fun z => (Real.exp (-F z + gaussianStatistic z p) •
    (gaussianStatistic z).smulRight (1 : ℝ)) v) at hv
  have hd := hk.mul hn
  simp only [posteriorPartition_eq_natural F] at ⊢
  convert hd using 1
  · rfl
  · rw [gaussianIntegral, ContinuousLinearMap.integral_apply hstat v]
    change (∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t))) *
      (‖z - x‖ ^ 2 / (2 * t ^ 2))) =
      (Real.exp (-‖x‖ ^ 2 / (2 * t)) * (‖x‖ ^ 2 / (2 * t ^ 2))) *
        (∫ z, Real.exp (-F z + gaussianStatistic z p) • (1 : ℝ)) +
      Real.exp (-‖x‖ ^ 2 / (2 * t)) *
        (∫ z, (Real.exp (-F z + gaussianStatistic z p) •
          (gaussianStatistic z).smulRight (1 : ℝ)) v)
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hz.const_mul _) (hv.const_mul _)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [posterior_density_eq_natural F t x z ht.ne']
    simp only [smul_eq_mul, mul_one, smul_apply,
      ContinuousLinearMap.smulRight_apply, gaussianStatistic_apply, v,
      inner_smul_right, norm_sub_sq_real, p]
    field_simp
    ring

/-- The actual canonical scalar velocity in terms of its second displacement
moment. Both the time derivative and constant normalization are proved. -/
theorem heatDensityVelocity_eq_secondMoment {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hI : Integrable (fun z => Real.exp (-F z))) (x : E) :
    heatDensityVelocity F t x =
      (heatGaussianPrefactor E t / ∫ z, Real.exp (-F z)) *
        ((∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t))) *
          (‖z - x‖ ^ 2 / (2 * t ^ 2))) -
        (Module.finrank ℝ E / (2 * t)) *
          (∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t))))) := by
  have hd := ((hasDerivAt_heatGaussianPrefactor (E := E) ht).mul
    (hasDerivAt_posterior_partition_time hF hm ht hlo x)).div_const
      (∫ z, Real.exp (-F z))
  have heq : (fun s => Real.exp (-heatPotential F s x) /
      ∫ z, Real.exp (-heatPotential F s z)) =ᶠ[𝓝 t]
      (fun s => heatGaussianPrefactor E s *
        (∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * s))))) /
        (fun _ => ∫ z, Real.exp (-F z)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    change Real.exp (-heatPotential F s x) / _ = _ / _
    rw [exp_neg_heatPotential_eq_heatConvolution hF hm hs hlo,
      integral_exp_neg_heatPotential hF hm hs hlo hI,
      heatConvolution_eq_prefactor_mul_partition]
  have hder := (hd.congr_of_eventuallyEq heq).deriv
  change deriv (fun s => Real.exp (-heatPotential F s x) /
    ∫ z, Real.exp (-heatPotential F s z)) t = _
  rw [hder]
  ring

/-- The actual density-weighted reference current is the raw displacement
integral with its exact physical prefactor and original normalization. -/
theorem heatDensity_current_eq_raw {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hI : Integrable (fun z => Real.exp (-F z))) (y : E) :
    originalHeatDensity F t y •
      referenceDrift (heatPotential F) (fun _ => -(1/2 : ℝ)) t y =
      (heatGaussianPrefactor E t / (2 * t * ∫ z, Real.exp (-F z))) •
        (∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t))) • (y - z)) := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  have hdisp : (∫ z, y - z ∂heatPosterior F t y) = y - ∫ z, z ∂heatPosterior F t y := by
    rw [integral_sub (integrable_const y) (integrable_id_heatPosterior hF hm ht hlo y)]
    simp
  have hs := (hasGradientAt_heatPotential hF hm ht hlo y).gradient
  change gradient (heatPotential F t) y =
    t⁻¹ • (y - ∫ z, z ∂heatPosterior F t y) at hs
  rw [← hdisp, integral_heatPosterior hF hm ht hlo y] at hs
  unfold originalHeatDensity referenceDrift
  rw [exp_neg_heatPotential_eq_heatConvolution hF hm ht hlo,
    integral_exp_neg_heatPotential hF hm ht hlo hI,
    heatConvolution_eq_prefactor_mul_partition, hs]
  simp only [neg_neg, smul_smul]
  congr 1
  have hZ := (integral_exp_pos (integrable_posterior_of_hessian_lower hF hm ht y hlo)).ne'
  generalize hZZ : (∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t)))) = Z at hZ ⊢
  field_simp [hZ]

/-- Spatial derivative of the raw displacement current, centered at the
point of differentiation so the moving-center product term is explicit. -/
theorem hasFDerivAt_raw_heat_displacement {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) (x : E) :
    HasFDerivAt (fun y => ∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t))) • (y - z))
      ((∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t)))) • ContinuousLinearMap.id ℝ E +
        ∫ z, ((-Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t)))) •
          (t⁻¹ • innerSL ℝ (x - z))).smulRight (x - z)) x := by
  have hg : Continuous (fun z : E => x - z) := continuous_const.sub continuous_id
  have hbound (z : E) : ‖x - z‖ ≤ ‖x‖ + 1 * ‖z‖ := by
    simpa only [one_mul] using norm_sub_le x z
  have hM := hasFDerivAt_weighted_posterior_partition hF hm ht hlo hg ‖x‖ 1 hbound x
  have hZ := hasFDerivAt_posterior_partition hF hm ht x hlo
  have hd := (hZ.smul ((hasFDerivAt_id x).sub_const x)).add hM
  have heq (y : E) :
      (∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t))) • (y - z)) =
      (∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t)))) • (y - x) +
        ∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t))) • (x - z) := by
    rw [← integral_smul_const]
    rw [← integral_add
      ((integrable_posterior_of_hessian_lower hF hm ht y hlo).smul_const (y - x))
      (integrable_weighted_posterior_of_affine_growth hF hm ht hlo hg ‖x‖ 1 hbound y)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [← smul_add]
    congr 1
    abel
  convert hd.congr_of_eventuallyEq (Eventually.of_forall heq) using 1
  simp only [id_eq, sub_self, ContinuousLinearMap.smulRight_zero, add_zero]

/-- The spatial divergence of the genuine raw displacement current, computed
in the actual orthonormal-coordinate definition of fluxDivergence. -/
theorem fluxDivergence_raw_heat_displacement {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) (C : ℝ) (x : E) :
    fluxDivergence (fun y => C •
      (∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t))) • (y - z))) x =
      C * ((Module.finrank ℝ E : ℝ) *
        (∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t)))) -
        t⁻¹ * ∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t))) * ‖z - x‖ ^ 2) := by
  let b := stdOrthonormalBasis ℝ E
  let W := fun z : E => Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t)))
  let Z := ∫ z, W z
  let M := fun z : E => ((-W z) • (t⁻¹ • innerSL ℝ (x - z))).smulRight (x - z)
  have hg : Continuous (fun z : E => x - z) := continuous_const.sub continuous_id
  have hbound (z : E) : ‖x - z‖ ≤ ‖x‖ + 1 * ‖z‖ := by
    simpa only [one_mul] using norm_sub_le x z
  have hM : Integrable M :=
    integrable_weighted_posterior_center_deriv hF hm ht hlo hg ‖x‖ 1 hbound x
  have hJ := (hasFDerivAt_raw_heat_displacement hF hm ht hlo x).const_smul C
  change HasFDerivAt (fun y => C •
    (∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t))) • (y - z)))
    (C • (Z • ContinuousLinearMap.id ℝ E + ∫ z, M z)) x at hJ
  have hc (i : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (fun y => inner ℝ (b i) (C •
        (∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t))) • (y - z)))) x (b i) =
      C * (Z + ∫ z, inner ℝ (b i) (M z (b i))) := by
    change fderiv ℝ ((innerSL ℝ (b i)) ∘ (fun y => C •
      (∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t))) • (y - z)))) x (b i) = _
    rw [((innerSL ℝ (b i)).hasFDerivAt.comp x hJ).fderiv]
    change inner ℝ (b i) (C • (Z • b i + (∫ z, M z) (b i))) = _
    rw [ContinuousLinearMap.integral_apply hM (b i)]
    have hi := (ContinuousLinearMap.apply ℝ E (b i)).integrable_comp hM
    change Integrable (fun z => M z (b i)) at hi
    have hinner := (innerSL ℝ (b i)).integral_comp_comm hi
    change (∫ z, inner ℝ (b i) (M z (b i))) = inner ℝ (b i) (∫ z, M z (b i)) at hinner
    rw [inner_smul_right, inner_add_right, inner_smul_right, ← hinner,
      b.inner_eq_ite]
    simp only [ite_true, mul_one]
  have hi (i : Fin (Module.finrank ℝ E)) : Integrable (fun z => inner ℝ (b i) (M z (b i))) := by
    exact (innerSL ℝ (b i)).integrable_comp
      ((ContinuousLinearMap.apply ℝ E (b i)).integrable_comp hM)
  have hp (z : E) : (∑ i, inner ℝ (b i) (M z (b i))) =
      -(t⁻¹) * (W z * ‖z - x‖ ^ 2) := by
    calc
      _ = ∑ i, (-(t⁻¹) * W z) * (inner ℝ (b i) (x - z)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [M, ContinuousLinearMap.smulRight_apply, smul_apply,
          innerSL_apply_apply, inner_smul_right, smul_eq_mul,
          real_inner_comm (x - z) (b i)]
        ring
      _ = (-(t⁻¹) * W z) * ‖x - z‖ ^ 2 := by
        rw [← Finset.mul_sum, b.sum_sq_inner_right]
      _ = _ := by rw [norm_sub_rev x z]; ring
  unfold fluxDivergence
  change (∑ i, fderiv ℝ (fun y => inner ℝ (b i) (C •
    (∫ z, Real.exp (-(F z + ‖z - y‖ ^ 2 / (2 * t))) • (y - z)))) x (b i)) = _
  simp_rw [hc]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [hp]
  rw [integral_const_mul]
  change C * ((Module.finrank ℝ E : ℝ) * Z + -(t⁻¹) *
    (∫ z, W z * ‖z - x‖ ^ 2)) = C * ((Module.finrank ℝ E : ℝ) * Z -
    t⁻¹ * ∫ z, W z * ‖z - x‖ ^ 2)
  ring

/-- The exact classical continuity equation for the actual normalized heat
density and actual reference drift. No PDE or law identity is a premise. -/
theorem originalHeatDensity_continuity_equation {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hI : Integrable (fun z => Real.exp (-F z))) (x : E) :
    heatDensityVelocity F t x +
      fluxDivergence (fun y => originalHeatDensity F t y •
        referenceDrift (heatPotential F) (fun _ => -(1/2 : ℝ)) t y) x = 0 := by
  rw [heatDensityVelocity_eq_secondMoment hF hm ht hlo hI]
  simp_rw [heatDensity_current_eq_raw hF hm ht hlo hI]
  rw [fluxDivergence_raw_heat_displacement hF hm ht hlo]
  have hmoment : (∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t))) *
      (‖z - x‖ ^ 2 / (2 * t ^ 2))) =
      (∫ z, Real.exp (-(F z + ‖z - x‖ ^ 2 / (2 * t))) * ‖z - x‖ ^ 2) /
        (2 * t ^ 2) := by
    simp_rw [← mul_div_assoc]
    simp only [div_eq_mul_inv, integral_mul_const]
  rw [hmoment]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The exact last field of OriginalHeatEvolutionData on the full analytic
open envelope, derived only from strictly positive original lower curvature. -/
theorem originalHeatDensity_continuity_equation_envelope {F : E → ℝ} {m A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m) (hA : 0 < A)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    ∀ t ∈ Ioo (3 * A / 4) R, ∀ x,
      heatDensityVelocity F t x +
        fluxDivergence (fun y => originalHeatDensity F t y •
          referenceDrift (heatPotential F) (fun _ => -(1/2 : ℝ)) t y) x = 0 := by
  intro t ht x
  have ht0 : 0 < t := by linarith [ht.1]
  exact originalHeatDensity_continuity_equation hF hm.le ht0 hlo
    (integrable_exp_neg_of_hessian_lower hF hm hlo) x

end AcceleratedLogConcave.Gibbs

namespace AcceleratedLogConcave.Kinetic.Reheating
open Gibbs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- All fields of the old OriginalHeatEvolutionData record, now supplied from
original C² and positive lower curvature. This does not identify heatedLaw or
construct the separate VarianceHeatFamily, and makes no sampler claim. -/
def originalHeatEvolutionData_of_hessian_lower {F : E → ℝ} {m A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m) (hA : 0 < A)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    OriginalHeatEvolutionData F A R where
  gradient_continuous := heatGradient_continuous_envelope hF hm.le hA hlo
  hessian_continuous := heatHessian_continuous_envelope hF hm.le hA hlo
  densityVelocity := heatDensityVelocity F
  density_continuous := normalizedHeatDensity_continuous_envelope hF hm hA hlo
  densityVelocity_continuous := heatDensityVelocity_continuous_envelope hF hm hA hlo
  density_hasDerivAt := normalizedHeatDensity_hasDerivAt_envelope hF hm hA hlo
  continuity_equation := originalHeatDensity_continuity_equation_envelope hF hm hA hlo

end AcceleratedLogConcave.Kinetic.Reheating
