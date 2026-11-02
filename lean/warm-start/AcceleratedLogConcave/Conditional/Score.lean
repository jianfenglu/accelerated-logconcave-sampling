import AcceleratedLogConcave.Conditional.JetBasics

/-! # The interpolation potential and its score

The potential here is defined up to a spatially constant normalizer.
Identification with the interpolation density is a separate measure statement.
-/
noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def interpolationPotential (F : E → ℝ) (x : E) (r ρ : ℝ) (y : E) : ℝ :=
  ‖y‖ ^ 2 / 2 + Gibbs.heatPotential (primitivePotential F x r) (conditionalVariance ρ) (ρ • y)

theorem contDiff_two_interpolationPotential {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) :
    ContDiff ℝ 2 (interpolationPotential F x r ρ) := by
  have hheat := Gibbs.contDiff_two_heatPotential (contDiff_primitivePotential hF x r)
    (m := 0) (le_refl 0) (conditionalVariance_pos hρlo hρhi)
    (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
  exact ((contDiff_norm_sq ℝ (E := E)).div_const 2).add
    (hheat.comp (contDiff_const.smul contDiff_id))

set_option backward.isDefEq.respectTransparency false in
/-- The source score formula from actual heat-score differentiation. -/
theorem gradient_interpolationPotential {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    gradient (interpolationPotential F x r ρ) y =
      y + (r * ρ) • conditionalMean F x r ρ y := by
  let G := Gibbs.heatPotential (primitivePotential F x r) (conditionalVariance ρ)
  have hg : ContDiff ℝ 2 G := Gibbs.contDiff_two_heatPotential
    (contDiff_primitivePotential hF x r) (m := 0) (le_refl 0)
    (conditionalVariance_pos hρlo hρhi)
    (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
  have hnorm : HasFDerivAt (fun z : E ↦ ‖z‖ ^ 2 / 2) (innerSL ℝ y) y := by
    convert ((hasFDerivAt_id y).norm_sq.const_mul (1 / 2 : ℝ)) using 1
    · ext z
      simp [div_eq_mul_inv, mul_comm]
    · ext w
      simp [smul_apply, innerSL_apply_apply]
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left]
  change fderiv ℝ (fun z ↦ ‖z‖ ^ 2 / 2 + G (ρ • z)) y w = _
  have hc : HasFDerivAt (fun z ↦ G (ρ • z))
      ((fderiv ℝ G (ρ • y)).comp (ρ • ContinuousLinearMap.id ℝ E)) y := by
    simpa only [Function.comp_def, Pi.smul_apply, id_eq] using
      (((hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp y
        ((hasFDerivAt_id y).const_smul ρ))
  rw [(hnorm.fun_add hc).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply, map_smul,
    smul_eq_mul, inner_add_left, inner_smul_left, conj_trivial]
  rw [← inner_gradient_left,
    heatGradient_eq_smul_conditionalMean hF hlo hup x r hρlo hρhi y]
  simp only [inner_smul_left, conj_trivial]
  ring

end AcceleratedLogConcave.Conditional
