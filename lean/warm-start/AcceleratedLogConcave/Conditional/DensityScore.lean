import AcceleratedLogConcave.Conditional.Score
import AcceleratedLogConcave.Conditional.Joint.Density

/-! # The score of the actual interpolation density -/
noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory ProbabilityTheory Gibbs Channels
open scoped RealInnerProductSpace ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The spatially constant conversion factor between the heat potential and
its exact probability density. -/
def interpolationDensityFactor (F : E → ℝ) (x : E) (r ρ : ℝ) : ℝ :=
  ((∫ z : E, Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2))) *
    (∫ n : E, Real.exp (-‖n‖ ^ 2 / (2 * conditionalVariance ρ))) *
    heatGaussianPrefactor E (conditionalVariance ρ))⁻¹

omit [DecidableEq ι] in
theorem interpolationDensity_eq_factor_exp {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (hv : 0 < conditionalVariance ρ) (y : E) :
    interpolationDensity F x r ρ y = interpolationDensityFactor F x r ρ *
      Real.exp (-interpolationPotential F x r ρ y) := by
  have hP := conditional_posterior_integrable hF hlo x r ρ hv y
  have hz := integral_exp_pos (base_posterior_integrable hF hlo x r)
  have hc : 0 < ∫ n : E, Real.exp (-‖n‖ ^ 2 / (2 * conditionalVariance ρ)) := by
    simpa only [Real.coe_toNNReal _ hv.le] using
      gaussian_normalizer_pos (ι := ι) (conditionalVariance ρ).toNNReal
        (Real.toNNReal_pos.mpr hv)
  have hp : 0 < heatGaussianPrefactor E (conditionalVariance ρ) := heatGaussianPrefactor_pos hv
  let Z := ∫ z : E, Real.exp (-(primitivePotential F x r z +
    ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ)))
  let P := heatGaussianPrefactor E (conditionalVariance ρ)
  have hpot : interpolationPotential F x r ρ y =
      ‖y‖ ^ 2 / 2 - Real.log Z - Real.log P := by
    unfold interpolationPotential
    rw [heatPotential_eq_neg_log_partition hv (ρ • y) hP]
    dsimp [Z, P]
    ring
  have hexp : Real.exp (-interpolationPotential F x r ρ y) =
      Real.exp (-‖y‖ ^ 2 / 2) * Z * P := by
    rw [hpot, show -(‖y‖ ^ 2 / 2 - Real.log Z - Real.log P) =
      (-‖y‖ ^ 2 / 2 + Real.log Z) + Real.log P by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (integral_exp_pos hP), Real.exp_log hp]
  rw [hexp]
  unfold interpolationDensity interpolationDensityFactor
  dsimp [Z, P]
  field_simp
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  ring

omit [DecidableEq ι] in
theorem interpolationDensity_pos {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (hv : 0 < conditionalVariance ρ) (y : E) :
    0 < interpolationDensity F x r ρ y := by
  have hz := integral_exp_pos (base_posterior_integrable hF hlo x r)
  have hp := integral_exp_pos (conditional_posterior_integrable hF hlo x r ρ hv y)
  have hc : 0 < ∫ n : E, Real.exp (-‖n‖ ^ 2 / (2 * conditionalVariance ρ)) := by
    simpa only [Real.coe_toNNReal _ hv.le] using
      gaussian_normalizer_pos (ι := ι) (conditionalVariance ρ).toNNReal
        (Real.toNNReal_pos.mpr hv)
  exact div_pos (mul_pos (Real.exp_pos _) hp) (mul_pos hz hc)

omit [DecidableEq ι] in
/-- The score relation is proved for the density of the actual interpolation. -/
theorem hasFDerivAt_interpolationDensity {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    HasFDerivAt (interpolationDensity F x r ρ)
      ((-interpolationDensity F x r ρ y) •
        innerSL ℝ (y + (r * ρ) • conditionalMean F x r ρ y)) y := by
  have hreg := contDiff_two_interpolationPotential hF hlo x r hρlo hρhi
  have hd := ((hreg.differentiable (by norm_num) y).hasFDerivAt.neg.exp).const_mul
    (interpolationDensityFactor F x r ρ)
  have heq : interpolationDensity F x r ρ = fun z ↦
      interpolationDensityFactor F x r ρ * Real.exp (-interpolationPotential F x r ρ z) :=
    funext (interpolationDensity_eq_factor_exp hF hlo x r ρ (conditionalVariance_pos hρlo hρhi))
  rw [heq]
  convert hd using 1
  ext w
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, neg_apply]
  rw [← inner_gradient_left, gradient_interpolationPotential hF hlo hup x r hρlo hρhi y]
  simp only [Pi.neg_apply]
  ring

end AcceleratedLogConcave.Conditional
