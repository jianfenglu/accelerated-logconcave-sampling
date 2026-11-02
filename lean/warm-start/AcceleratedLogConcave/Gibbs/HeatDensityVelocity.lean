import AcceleratedLogConcave.Gibbs.HeatDensityContinuity

/-!
# The canonical scalar heat-density time velocity

All-order Gaussian-parameter regularity applies to the actual heat convolution
and hence its canonically normalized density. Its actual scalar time derivative
is jointly smooth at positive variance. Original C² and lower curvature suffice;
strict positive lower curvature supplies the explicit base integrability.

This is not the reference drift or density-weighted current. The classical PDE
and Gaussian-heated-law identification remain separate obligations.
-/

noncomputable section
open MeasureTheory Set Function InnerProductSpace
open scoped ContDiff

namespace AcceleratedLogConcave.Gibbs
open Conditional.Tilt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Joint smoothness of the actual heat convolution, including its physical
Gaussian prefactor. Only Gaussian parameters, not higher derivatives of F,
are differentiated in this proof. -/
theorem contDiffOn_heatConvolution {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ContDiffOn ℝ ∞ (uncurry (heatConvolution F)) (gaussianDomain (E := E)) := by
  have hlower (z : E) : F 0 + inner ℝ (gradient F 0) z ≤ F z := by
    have hh := quadratic_lower_bound_of_hessian_lower hF hlo z
    rw [← inner_gradient_left] at hh
    have hn : 0 ≤ m / 2 * ‖z‖ ^ 2 := by positivity
    linarith
  have hnat := contDiffOn_gaussianIntegral_of_polynomial_growth hF.continuous
    (continuous_const : Continuous (fun _ : E => (1 : ℝ)))
    (F 0) (gradient F 0) hlower 1 0 0 (by intro z; simp)
  have ht : ContDiffOn ℝ ∞ (fun p : ℝ × E => p.1) gaussianDomain :=
    contDiff_fst.contDiffOn
  have hinv := ht.inv (fun p hp => ne_of_gt hp)
  have hp : ContDiffOn ℝ ∞ (posteriorParameters (E := E)) gaussianDomain :=
    ((contDiffOn_const.mul ht).inv (by
      intro p hp
      exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp))).prodMk
      (hinv.smul contDiff_snd.contDiffOn)
  have hmap : MapsTo (posteriorParameters (E := E)) gaussianDomain gaussianDomain := by
    intro p hp
    change 0 < (2 * p.1)⁻¹
    exact inv_pos.mpr (mul_pos (by norm_num) hp)
  have hbase : ContDiffOn ℝ ∞ (fun p : ℝ × E => 2 * Real.pi * p.1)
      gaussianDomain := contDiffOn_const.mul ht
  have hpow := hbase.rpow_const_of_ne (p := (Module.finrank ℝ E / 2 : ℝ)) (by
    intro p hp
    have hpos : 0 < p.1 := hp
    exact (show 0 < 2 * Real.pi * p.1 by positivity).ne')
  have hpre : ContDiffOn ℝ ∞ (fun p : ℝ × E => heatGaussianPrefactor E p.1)
      gaussianDomain := hpow.inv (by
    intro p hp
    have hpos : 0 < p.1 := hp
    exact (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi * p.1) _).ne')
  have hk : ContDiffOn ℝ ∞ (fun p : ℝ × E => Real.exp (-‖p.2‖ ^ 2 / (2 * p.1)))
      gaussianDomain :=
    ((((contDiff_snd.contDiffOn.norm_sq ℝ).neg).div
      (contDiffOn_const.mul ht) (by
        intro p hp
        exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp))).exp)
  apply (hpre.mul (hk.mul (hnat.comp hp hmap))).congr
  intro p hpt
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [uncurry_apply_pair, heatConvolution_eq_prefactor_mul_partition]
  congr 1
  simp_rw [posterior_density_eq_natural F p.1 p.2 _ (ne_of_gt hpt)]
  simp only [gaussianIntegral, smul_eq_mul, mul_one, integral_const_mul]

/-- Joint smoothness of the actual canonical normalized density. The previous
mass identity fixes its denominator to the original finite partition function. -/
theorem contDiffOn_normalizedHeatDensity_of_integrable {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hI : Integrable (fun x => Real.exp (-F x))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => Real.exp (-heatPotential F p.1 p.2) /
      ∫ y, Real.exp (-heatPotential F p.1 y)) gaussianDomain := by
  apply ((contDiffOn_heatConvolution hF hm hlo).div_const
    (∫ y, Real.exp (-F y))).congr
  intro p hp
  change Real.exp (-heatPotential F p.1 p.2) / _ = heatConvolution F p.1 p.2 / _
  rw [exp_neg_heatPotential_eq_heatConvolution hF hm hp hlo,
    integral_exp_neg_heatPotential hF hm hp hlo hI]

/-- The actual scalar time derivative of the canonical normalized heat density.
No regularity or PDE property is included in this definition. -/
def heatDensityVelocity (F : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  deriv (fun s => Real.exp (-heatPotential F s x) /
    ∫ y, Real.exp (-heatPotential F s y)) t

/-- The actual partial time derivative is jointly smooth at positive variance,
by genuine joint differentiability of the canonical density. -/
theorem contDiffOn_heatDensityVelocity_of_integrable {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hI : Integrable (fun x => Real.exp (-F x))) :
    ContDiffOn ℝ ∞ (uncurry (heatDensityVelocity F)) (gaussianDomain (E := E)) := by
  have hs := contDiffOn_normalizedHeatDensity_of_integrable hF hm hlo hI
  intro p hp
  have hsAt := hs.contDiffAt (isOpen_gaussianDomain.mem_nhds hp)
  have haux : ContDiffAt ℝ ∞
      (uncurry (fun q : ℝ × E => fun s : ℝ => Real.exp (-heatPotential F s q.2) /
        ∫ y, Real.exp (-heatPotential F s y))) (p, p.1) := by
    convert hsAt.comp (p, p.1)
      (contDiffAt_snd.prodMk (contDiffAt_fst.snd)) using 1
    rfl
  have hd := haux.fderiv (contDiffAt_fst :
    ContDiffAt ℝ ∞ (fun p : ℝ × E => p.1) p) (by simp)
  change ContDiffWithinAt ℝ ∞
    (fun q : ℝ × E => (fderiv ℝ (fun s => Real.exp (-heatPotential F s q.2) /
      ∫ y, Real.exp (-heatPotential F s y)) q.1) 1) gaussianDomain p
  exact (hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))).contDiffWithinAt

/-- Genuine pointwise time differentiability of the canonical density, not an
assumed heat equation. The derivative value is the canonical scalar velocity. -/
theorem hasDerivAt_normalizedHeatDensity_of_integrable {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hI : Integrable (fun x => Real.exp (-F x))) (x : E) :
    HasDerivAt (fun s => Real.exp (-heatPotential F s x) /
      ∫ y, Real.exp (-heatPotential F s y)) (heatDensityVelocity F t x) t := by
  have hs := contDiffOn_normalizedHeatDensity_of_integrable hF hm hlo hI
  have hsAt := hs.contDiffAt (isOpen_gaussianDomain.mem_nhds (show (t, x) ∈
    gaussianDomain from ht))
  have hslice : ContDiffAt ℝ ∞ (fun s => Real.exp (-heatPotential F s x) /
      ∫ y, Real.exp (-heatPotential F s y)) t := by
    convert hsAt.comp t (contDiffAt_id.prodMk contDiffAt_const) using 1
    rfl
  exact (hslice.differentiableAt (by simp)).hasDerivAt

/-- Exact original-data velocity-continuity field on the full open envelope.
Strict original lower curvature derives the integrability premise. -/
theorem heatDensityVelocity_continuous_envelope {F : E → ℝ} {m A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m) (hA : 0 < A)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ContinuousOn (uncurry (heatDensityVelocity F))
      (Ioo (3 * A / 4) R ×ˢ (univ : Set E)) := by
  apply (contDiffOn_heatDensityVelocity_of_integrable hF hm.le hlo
    (integrable_exp_neg_of_hessian_lower hF hm hlo)).continuousOn.mono
  intro p hp
  change 0 < p.1
  have ht := hp.1.1
  linarith

/-- Exact original-data time-derivative field, with the same canonical velocity
as the continuity theorem, on the full open analytic envelope. -/
theorem normalizedHeatDensity_hasDerivAt_envelope {F : E → ℝ} {m A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m) (hA : 0 < A)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ∀ t ∈ Ioo (3 * A / 4) R, ∀ x,
      HasDerivAt (fun s => Real.exp (-heatPotential F s x) /
        ∫ y, Real.exp (-heatPotential F s y)) (heatDensityVelocity F t x) t := by
  intro t ht x
  have ht0 : 0 < t := by linarith [ht.1]
  exact hasDerivAt_normalizedHeatDensity_of_integrable hF hm.le ht0 hlo
    (integrable_exp_neg_of_hessian_lower hF hm hlo) x

end AcceleratedLogConcave.Gibbs
