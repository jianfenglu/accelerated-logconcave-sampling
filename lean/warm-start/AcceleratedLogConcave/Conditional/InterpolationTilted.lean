import AcceleratedLogConcave.Conditional.DensityScore
import AcceleratedLogConcave.Conditional.Flow.Regularity

/-! Actual-law prerequisites for weighted adjoint reduction. The normalized
law and potential are the existing interpolation objects, not an assumed
integration-by-parts certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem interpolationDensityFactor_mul_partition
    {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) :
    interpolationDensityFactor F x r ρ *
      (∫ y : E, Real.exp (-interpolationPotential F x r ρ y)) = 1 := by
  classical
  let H := interpolationPotential F x r ρ
  have hH := (contDiff_two_interpolationPotential hF hlo x r hρlo hρhi).continuous
  have heq := interpolationDensity_eq_factor_exp hF hlo x r ρ
    (conditionalVariance_pos hρlo hρhi)
  have hd : Measurable (interpolationDensity F x r ρ) := by
    have he : interpolationDensity F x r ρ = fun y =>
      interpolationDensityFactor F x r ρ * Real.exp (-H y) := funext heq
    rw [he]
    exact measurable_const.mul (Real.continuous_exp.comp hH.neg).measurable
  have hp := interpolationDensity_pos hF hlo x r ρ (conditionalVariance_pos hρlo hρhi)
  let := interpolationLaw_isProbabilityMeasure hF hlo x r ρ
  have h := integral_withDensity_eq_integral_toReal_smul (μ := volume) hd.ennreal_ofReal
    (Filter.Eventually.of_forall (fun y : E => ENNReal.ofReal_lt_top)) (fun _ : E => (1 : ℝ))
  rw [← interpolationLaw_eq_explicitDensity hF hlo x r ρ (conditionalVariance_pos hρlo hρhi)] at h
  simp only [integral_const, probReal_univ, ENNReal.toReal_ofReal (hp _).le,
    smul_eq_mul, mul_one] at h
  rw [show (∫ y : E, interpolationDensity F x r ρ y) =
      interpolationDensityFactor F x r ρ * (∫ y : E, Real.exp (-H y)) by
    simp_rw [heq]; exact integral_const_mul _ _] at h
  exact h.symm

/-- Normalizability is derived from the actual probability density identity. -/
theorem integrable_exp_neg_interpolationPotential
    {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) :
    Integrable (fun y : E => Real.exp (-interpolationPotential F x r ρ y)) := by
  classical
  by_contra hn
  have h := interpolationDensityFactor_mul_partition hF hlo x r hρlo hρhi
  rw [integral_undef hn, mul_zero] at h
  exact zero_ne_one h

/-- The genuine interpolation law is precisely the normalized Gibbs tilt. -/
theorem interpolationLaw_eq_tilted
    {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) :
    interpolationLaw F x r ρ = volume.tilted (fun y : E => -interpolationPotential F x r ρ y) := by
  classical
  have hn := interpolationDensityFactor_mul_partition hF hlo x r hρlo hρhi
  have hz : (∫ y : E, Real.exp (-interpolationPotential F x r ρ y)) ≠ 0 := by
    intro h; rw [h, mul_zero] at hn; exact zero_ne_one hn
  have hc : interpolationDensityFactor F x r ρ =
      (∫ y : E, Real.exp (-interpolationPotential F x r ρ y))⁻¹ := by
    simpa only [one_div] using (eq_div_iff hz).mpr hn
  rw [interpolationLaw_eq_explicitDensity hF hlo x r ρ (conditionalVariance_pos hρlo hρhi),
    Measure.tilted]
  congr 1
  funext y
  rw [interpolationDensity_eq_factor_exp hF hlo x r ρ (conditionalVariance_pos hρlo hρhi), hc]
  congr 1
  ring

/-- Gaussian smoothing makes the actual interpolation potential infinitely
smooth in space, without strengthening the original potential beyond C². -/
theorem contDiff_interpolationPotential
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) :
    ContDiff ℝ ∞ (interpolationPotential F x r ρ) := by
  have hm : ContDiff ℝ ∞ (conditionalMean F x r ρ) := by
    have hc : ContDiff ℝ ∞ (fun y : E => (ρ, y)) := contDiff_const.prodMk contDiff_id
    have hh := (contDiffOn_conditionalMean hF hlo hup x r).comp
      hc.contDiffOn (s := Set.univ) (fun _ _ => ⟨hρlo, hρhi⟩)
    exact contDiffOn_univ.mp hh
  have hg : ContDiff ℝ ∞ (gradient (interpolationPotential F x r ρ)) := by
    have he : gradient (interpolationPotential F x r ρ) =
        fun y => y + (r * ρ) • conditionalMean F x r ρ y :=
      funext (gradient_interpolationPotential hF hlo hup x r hρlo hρhi)
    rw [he]
    exact contDiff_id.add ((contDiff_const : ContDiff ℝ ∞ (fun _ : E => r * ρ)).smul hm)
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨(contDiff_two_interpolationPotential hF hlo x r hρlo hρhi).differentiable (by norm_num), ?_⟩
  rw [← toDual_comp_gradient]
  exact (InnerProductSpace.toDual ℝ E).contDiff.comp hg

end AcceleratedLogConcave.Conditional
