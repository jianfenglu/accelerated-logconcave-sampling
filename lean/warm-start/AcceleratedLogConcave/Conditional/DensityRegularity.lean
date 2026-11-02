import AcceleratedLogConcave.Conditional.DensityScore

/-! # Joint smoothness of the actual interpolation density -/
noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The unnormalized Gaussian posterior partition is jointly smooth at every
positive variance, without additional regularity of the base potential. -/
theorem contDiffOn_posteriorPartition {B : E → ℝ} (hB : ContDiff ℝ 2 B)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ B) z a a) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦
      ∫ z, Real.exp (-(B z + ‖z - p.2‖ ^ 2 / (2 * p.1)))) Tilt.gaussianDomain := by
  have hlower (z : E) : B 0 + inner ℝ (gradient B 0) z ≤ B z := by
    have h := Gibbs.quadratic_lower_bound_of_hessian_lower hB (m := 0)
      (by simpa using hlo) z
    simpa only [zero_div, zero_mul, add_zero, inner_gradient_left] using h
  have hn := Tilt.contDiffOn_gaussianIntegral_of_polynomial_growth hB.continuous
    (continuous_const : Continuous (fun _ : E ↦ (1 : ℝ)))
    (B 0) (gradient B 0) hlower 1 0 0 (by intro z; simp)
  have ht : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ p.1) Tilt.gaussianDomain :=
    contDiff_fst.contDiffOn
  have hp : ContDiffOn ℝ ∞ (Tilt.posteriorParameters (E := E)) Tilt.gaussianDomain := by
    exact ((contDiffOn_const.mul ht).inv (fun p hp ↦
      mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp))).prodMk
      ((ht.inv (fun p hp ↦ ne_of_gt hp)).smul contDiff_snd.contDiffOn)
  have hmap : MapsTo (Tilt.posteriorParameters (E := E)) Tilt.gaussianDomain
      Tilt.gaussianDomain := by
    intro p hp
    change 0 < (2 * p.1)⁻¹
    exact inv_pos.mpr (mul_pos (by norm_num) hp)
  have he : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ Real.exp (-‖p.2‖ ^ 2 / (2 * p.1)))
      Tilt.gaussianDomain := by
    exact ((contDiff_snd.norm_sq ℝ).neg.contDiffOn.div (contDiffOn_const.mul ht)
      (fun p hp ↦ mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp))).exp
  apply (he.mul (hn.comp hp hmap)).congr
  intro p hpt
  simp only [Function.comp_def, Tilt.gaussianIntegral, smul_eq_mul, mul_one]
  simp_rw [Tilt.posterior_density_eq_natural B p.1 p.2 _ (ne_of_gt hpt)]
  exact integral_const_mul _ _

end General

section Euclidean
variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι

/-- Joint C∞ regularity of the actual interpolation density on the open
probability-time interval, with no higher derivatives of the base potential. -/
theorem contDiffOn_interpolationDensity {F : V → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a) (x : V) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V ↦ interpolationDensity F x r p.1 p.2)
      {p | -1 < p.1 ∧ p.1 < 1} := by
  let S : Set (ℝ × V) := {p | -1 < p.1 ∧ p.1 < 1}
  have hv (p : ℝ × V) (hp : p ∈ S) : 0 < conditionalVariance p.1 :=
    conditionalVariance_pos hp.1 hp.2
  have hB := contDiffOn_posteriorPartition (contDiff_primitivePotential hF x r)
    (primitivePotential_hessian_nonneg hF hlo x r)
  have hzero : ContDiff ℝ 2 (fun _ : V ↦ (0 : ℝ)) := contDiff_const
  have hz := contDiffOn_posteriorPartition hzero (by simp)
  have hp : ContDiff ℝ ∞ (fun p : ℝ × V ↦ (conditionalVariance p.1, p.1 • p.2)) := by
    unfold conditionalVariance
    fun_prop
  have hp0 : ContDiff ℝ ∞ (fun p : ℝ × V ↦ (conditionalVariance p.1, (0 : V))) := by
    unfold conditionalVariance
    fun_prop
  have hnum := hB.comp hp.contDiffOn (fun p hp ↦ hv p hp)
  have hden := hz.comp hp0.contDiffOn (fun p hp ↦ hv p hp)
  have he : ContDiff ℝ ∞ (fun p : ℝ × V ↦ Real.exp (-‖p.2‖ ^ 2 / 2)) :=
    ((contDiff_snd.norm_sq ℝ).neg.div_const 2).exp
  have hZ := integral_exp_pos (base_posterior_integrable hF hlo x r)
  have hnonzero (p : ℝ × V) (hpt : p ∈ S) :
      (∫ z : V, Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2))) *
        (∫ z : V, Real.exp (-(0 + ‖z - 0‖ ^ 2 / (2 * conditionalVariance p.1)))) ≠ 0 := by
    apply mul_ne_zero hZ.ne'
    exact (integral_exp_pos (Gibbs.integrable_posterior_of_hessian_lower hzero
      (m := 0) (le_refl 0) (hv p hpt) (0 : V) (by simp))).ne'
  have hh := (he.contDiffOn.mul hnum).div (contDiffOn_const.mul hden) hnonzero
  simpa only [Function.comp_def, zero_add, sub_zero, neg_div,
    interpolationDensity, Pi.div_def, S] using hh

end Euclidean

end AcceleratedLogConcave.Conditional
