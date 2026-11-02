import AcceleratedLogConcave.Conditional.Tilt.HeatIntegral

/-!
# Continuity of the canonical normalized heat density

The actual heat convolution is jointly continuous at positive variance, by
square completion and the existing Gaussian integral theorem. Its mass is the
original Gibbs partition function. Original strict positive lower curvature
supplies the required base integrability, without an upper Hessian bound.
This module supplies only density continuity and its normalization identity;
it makes no density time-derivative, PDE, law-identification or sampler claim.
-/

noncomputable section
open MeasureTheory Set Function InnerProductSpace
open scoped Convolution

namespace AcceleratedLogConcave.Gibbs
open Conditional.Tilt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Pointwise positivity of the actual convolution, without base integrability. -/
theorem heatConvolution_pos {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) (x : E) :
    0 < heatConvolution F t x := by
  rw [heatConvolution_eq_prefactor_mul_partition]
  exact mul_pos (heatGaussianPrefactor_pos ht)
    (integral_exp_pos (integrable_posterior_of_hessian_lower hF hm ht x hlo))

/-- The exponentiated actual heat potential is the actual heat convolution. -/
theorem exp_neg_heatPotential_eq_heatConvolution {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) (x : E) :
    Real.exp (-heatPotential F t x) = heatConvolution F t x := by
  simp only [heatPotential, neg_neg]
  exact Real.exp_log (heatConvolution_pos hF hm ht hlo x)

/-- The physical Gaussian kernel has unit mass, so convolution preserves the
original finite partition function. No Hessian assumption is used here. -/
theorem integral_heatConvolution {F : E → ℝ} {t : ℝ}
    (hI : Integrable (fun x => Real.exp (-F x))) (ht : 0 < t) :
    (∫ x, heatConvolution F t x) = ∫ x, Real.exp (-F x) := by
  have hg : Integrable (heatGaussianDensity (E := E) t) :=
    integrable_of_integral_eq_one (integral_heatGaussianDensity ht)
  unfold heatConvolution
  rw [integral_convolution _ hI hg]
  simp only [integral_heatGaussianDensity ht, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_one]

/-- The exact canonical heat normalizer is independent of positive variance.
Base integrability is explicit; strict lower curvature supplies it below. -/
theorem integral_exp_neg_heatPotential {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hI : Integrable (fun x => Real.exp (-F x))) :
    (∫ x, Real.exp (-heatPotential F t x)) = ∫ x, Real.exp (-F x) := by
  simp_rw [exp_neg_heatPotential_eq_heatConvolution hF hm ht hlo]
  exact integral_heatConvolution hI ht

/-- Joint continuity of the actual heat convolution, retaining its Gaussian
prefactor. Only original C² data and nonnegative lower curvature are used. -/
theorem continuousOn_heatConvolution {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ContinuousOn (uncurry (heatConvolution F)) (gaussianDomain (E := E)) := by
  have hlower (z : E) : F 0 + inner ℝ (gradient F 0) z ≤ F z := by
    have hh := quadratic_lower_bound_of_hessian_lower hF hlo z
    rw [← inner_gradient_left] at hh
    have hn : 0 ≤ m / 2 * ‖z‖ ^ 2 := by positivity
    linarith
  have hnat := (contDiffOn_gaussianIntegral_of_polynomial_growth hF.continuous
    (continuous_const : Continuous (fun _ : E => (1 : ℝ)))
    (F 0) (gradient F 0) hlower 1 0 0 (by intro z; simp)).continuousOn
  have ht : ContinuousOn (fun p : ℝ × E => p.1) gaussianDomain :=
    continuous_fst.continuousOn
  have hinv := ht.inv₀ (fun p hp => ne_of_gt hp)
  have hp : ContinuousOn (posteriorParameters (E := E)) gaussianDomain :=
    ((continuousOn_const.mul ht).inv₀ (by
      intro p hp
      exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp))).prodMk
      (hinv.smul continuous_snd.continuousOn)
  have hmap : MapsTo (posteriorParameters (E := E)) gaussianDomain gaussianDomain := by
    intro p hp
    change 0 < (2 * p.1)⁻¹
    exact inv_pos.mpr (mul_pos (by norm_num) hp)
  have hbase : ContinuousOn (fun p : ℝ × E => 2 * Real.pi * p.1) gaussianDomain :=
    continuousOn_const.mul ht
  have hpow := hbase.rpow_const (p := (Module.finrank ℝ E / 2 : ℝ))
    (by intro p hp; exact Or.inr (by positivity))
  have hpre : ContinuousOn (fun p : ℝ × E => heatGaussianPrefactor E p.1)
      gaussianDomain := hpow.inv₀ (by
    intro p hp
    have hpos : 0 < p.1 := hp
    exact (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi * p.1) _).ne')
  have hk : ContinuousOn (fun p : ℝ × E => Real.exp (-‖p.2‖ ^ 2 / (2 * p.1)))
      gaussianDomain :=
    ((((continuous_snd.continuousOn.norm.pow 2).neg).div
      (continuousOn_const.mul ht) (by
        intro p hp
        exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp))).rexp)
  apply (hpre.mul (hk.mul (hnat.comp hp hmap))).congr
  intro p hpt
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [uncurry_apply_pair, heatConvolution_eq_prefactor_mul_partition]
  congr 1
  simp_rw [posterior_density_eq_natural F p.1 p.2 _ (ne_of_gt hpt)]
  simp only [gaussianIntegral, smul_eq_mul, mul_one, integral_const_mul]

/-- Exact canonical-density continuity with base integrability explicit.
The denominator is proved equal to the fixed original partition function. -/
theorem continuousOn_normalizedHeatDensity_of_integrable {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hI : Integrable (fun x => Real.exp (-F x))) :
    ContinuousOn (fun p : ℝ × E => Real.exp (-heatPotential F p.1 p.2) /
      ∫ y, Real.exp (-heatPotential F p.1 y)) gaussianDomain := by
  apply ((continuousOn_heatConvolution hF hm hlo).div_const
    (∫ y, Real.exp (-F y))).congr
  intro p hp
  change Real.exp (-heatPotential F p.1 p.2) / _ = heatConvolution F p.1 p.2 / _
  rw [exp_neg_heatPotential_eq_heatConvolution hF hm hp hlo,
    integral_exp_neg_heatPotential hF hm hp hlo hI]

/-- Exact original-data density-continuity envelope field. Strict positive
lower curvature derives base integrability; no upper curvature is needed.
R is arbitrary, so the full analytic extension beyond A is retained. -/
theorem normalizedHeatDensity_continuous_envelope {F : E → ℝ} {m A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m) (hA : 0 < A)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ContinuousOn (fun p : ℝ × E => Real.exp (-heatPotential F p.1 p.2) /
      ∫ y, Real.exp (-heatPotential F p.1 y))
      (Icc (3 * A / 4) R ×ˢ (univ : Set E)) := by
  apply (continuousOn_normalizedHeatDensity_of_integrable hF hm.le hlo
    (integrable_exp_neg_of_hessian_lower hF hm hlo)).mono
  intro p hp
  change 0 < p.1
  have ht := hp.1.1
  linarith

end AcceleratedLogConcave.Gibbs
