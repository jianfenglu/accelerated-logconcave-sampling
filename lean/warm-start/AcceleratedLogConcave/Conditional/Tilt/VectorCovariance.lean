import AcceleratedLogConcave.Conditional.Tilt.HeatIntegral

noncomputable section
namespace AcceleratedLogConcave.Conditional.Tilt
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The centered vector covariance is an actual Bochner-integrable operator. -/
theorem integrable_centered_covariance
    {B : E → ℝ} {m t : ℝ} (hB : ContDiff ℝ 2 B) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z v v)
    {g : E → E} (hg : Continuous g) (A C : ℝ)
    (hbound : ∀ z, ‖g z‖ ≤ A + C * ‖z‖) (c a b : E) :
    Integrable (fun z ↦ (innerSL ℝ (z - a)).smulRight (g z - b))
      (Gibbs.heatPosterior B t c) := by
  let := Gibbs.heatPosterior_isProbabilityMeasure hB hm ht hlo c
  have hc : Continuous (fun z ↦ (innerSL ℝ (z - a)).smulRight (g z - b)) :=
    isBoundedBilinearMap_smulRight.continuous.comp
      (((innerSL ℝ (E := E)).continuous.comp (continuous_id.sub continuous_const)).prodMk
        (hg.sub continuous_const))
  have h0 : Integrable (fun _ : E ↦ ‖a‖ * (|A| + ‖b‖))
      (Gibbs.heatPosterior B t c) := integrable_const _
  have h1 := (Gibbs.integrable_norm_pow_heatPosterior hB hm ht hlo c 1).const_mul
    (|A| + ‖b‖ + ‖a‖ * |C|)
  have h2 := (Gibbs.integrable_norm_pow_heatPosterior hB hm ht hlo c 2).const_mul |C|
  refine ((h2.add h1).add h0).mono' hc.aestronglyMeasurable ?_
  filter_upwards [] with z
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hgz : ‖g z - b‖ ≤ |A| + |C| * ‖z‖ + ‖b‖ := by
    calc
      _ ≤ ‖g z‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ (A + C * ‖z‖) + ‖b‖ := by linarith [hbound z]
      _ ≤ _ := by gcongr <;> exact le_abs_self _
  calc
    _ ≤ (‖z‖ + ‖a‖) * (|A| + |C| * ‖z‖ + ‖b‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = _ := by simp only [Pi.add_apply, pow_one]; ring

/-- The actual normalized vector posterior derivative is its centered
position/observable covariance operator. -/
theorem fderiv_integral_heatPosterior_eq_vectorCovariance
    {B : E → ℝ} {m t : ℝ} (hB : ContDiff ℝ 2 B) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z v v)
    {g : E → E} (hg : Continuous g) (A C : ℝ)
    (hbound : ∀ z, ‖g z‖ ≤ A + C * ‖z‖) (c : E) :
    fderiv ℝ (fun c ↦ ∫ z, g z ∂Gibbs.heatPosterior B t c) c =
      t⁻¹ • ∫ z,
        (innerSL ℝ (z - ∫ z, z ∂Gibbs.heatPosterior B t c)).smulRight
          (g z - ∫ z, g z ∂Gibbs.heatPosterior B t c)
        ∂Gibbs.heatPosterior B t c := by
  let μ := Gibbs.heatPosterior B t c
  have hgi (d : E) : Integrable g (Gibbs.heatPosterior B t d) := by
    let := Gibbs.heatPosterior_isProbabilityMeasure hB hm ht hlo d
    exact (Gibbs.memLp_two_heatPosterior_of_affine_bound hB hm ht hlo d hg A C hbound).integrable
      (by norm_num)
  have hzi := Gibbs.integrable_id_heatPosterior hB hm ht hlo c
  have hci := integrable_centered_covariance hB hm ht hlo hg A C hbound c
    (∫ z, z ∂μ) (∫ z, g z ∂μ)
  have hmean := Gibbs.contDiff_one_integral_heatPosterior hB hm ht hlo hg A C hbound
  ext v
  apply ext_inner_right ℝ
  intro w
  let gw : E → ℝ := fun z ↦ inner ℝ w (g z)
  have hgw : Continuous gw := (innerSL ℝ w).continuous.comp hg
  have hbw (z : E) : ‖gw z‖ ≤ A * ‖w‖ + (C * ‖w‖) * ‖z‖ := by
    calc
      _ ≤ ‖w‖ * ‖g z‖ := norm_inner_le_norm _ _
      _ ≤ ‖w‖ * (A + C * ‖z‖) := mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg _)
      _ = _ := by ring
  have heq (d : E) : (∫ z, gw z ∂Gibbs.heatPosterior B t d) =
      inner ℝ w (∫ z, g z ∂Gibbs.heatPosterior B t d) :=
    (innerSL ℝ w).integral_comp_comm (hgi d)
  have hlin := (innerSL ℝ w).hasFDerivAt.comp c
    (hmean.differentiable (by norm_num) c).hasFDerivAt
  have hscalar : fderiv ℝ (fun d ↦ ∫ z, gw z ∂Gibbs.heatPosterior B t d) c v =
      inner ℝ w (fderiv ℝ (fun d ↦ ∫ z, g z ∂Gibbs.heatPosterior B t d) c v) := by
    have hf : (fun d ↦ ∫ z, gw z ∂Gibbs.heatPosterior B t d) =
        (innerSL ℝ w) ∘ (fun d ↦ ∫ z, g z ∂Gibbs.heatPosterior B t d) := funext heq
    rw [hf, hlin.fderiv]
    rfl
  conv_lhs => rw [real_inner_comm]
  rw [← hscalar,
    Gibbs.fderiv_integral_heatPosterior_eq_covariance hB hm ht hlo hgw
      (A * ‖w‖) (C * ‖w‖) hbw c v]
  conv_rhs => rw [real_inner_comm]
  rw [smul_apply, real_inner_smul_right,
    ContinuousLinearMap.integral_apply hci v]
  have hi : Integrable (fun z ↦
      (innerSL ℝ (z - ∫ z, z ∂μ)).smulRight (g z - ∫ z, g z ∂μ) v) μ :=
    hci.apply_continuousLinearMap v
  change _ = t⁻¹ * (innerSL ℝ w) (∫ z,
    (innerSL ℝ (z - ∫ z, z ∂μ)).smulRight (g z - ∫ z, g z ∂μ) v ∂μ)
  rw [← (innerSL ℝ w).integral_comp_comm hi]
  congr 1
  unfold covariance
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_sub_left, inner_sub_right, real_inner_smul_right, gw]
  have hzint : (∫ x, inner ℝ x v ∂Gibbs.heatPosterior B t c) =
      inner ℝ (∫ x, x ∂Gibbs.heatPosterior B t c) v := by
    simpa only [innerSL_apply_apply, real_inner_comm] using
      (innerSL ℝ v).integral_comp_comm hzi
  rw [heq c, hzint]
  change (inner ℝ w (g z) - inner ℝ w (∫ z, g z ∂μ)) *
    (inner ℝ z v - inner ℝ (∫ z, z ∂μ) v) = _
  ring

end AcceleratedLogConcave.Conditional.Tilt
