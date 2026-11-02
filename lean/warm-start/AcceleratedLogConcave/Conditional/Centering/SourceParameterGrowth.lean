import AcceleratedLogConcave.Conditional.Centering.Source
import AcceleratedLogConcave.Conditional.SourcePosteriorParameters
import AcceleratedLogConcave.Conditional.SourceParameterDomain

/-! Continuous linear-growth coefficients for the literal source phase field.
These coefficients are local parameter bounds, not bounds on its derivative. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace AcceleratedLogConcave.Conditional.Centering
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceGrowthSlope {ell : ℝ} (p : SourceParameters E ell) : ℝ :=
  p.width⁻¹ * ((2 * Real.exp 1 + 1) * (p.radius * ell))

def sourceGrowthOffset (F : E → ℝ) (b : ℝ) {ell : ℝ}
    (p : SourceParameters E ell) : ℝ :=
  p.width⁻¹ * ‖conditionalMean F p.center p.radius b 0 -
    conditionalMean F p.center p.radius 0 0‖

omit [Fintype ι] in
theorem sourceGrowthSlope_nonneg {ell : ℝ} (hell : 0 ≤ ell)
    (p : SourceParameters E ell) : 0 ≤ sourceGrowthSlope p := by
  unfold sourceGrowthSlope
  have := p.width_pos
  have := p.radius_pos
  positivity

theorem sourceGrowthOffset_nonneg (F : E → ℝ) (b : ℝ) {ell : ℝ}
    (p : SourceParameters E ell) : 0 ≤ sourceGrowthOffset F b p :=
  mul_nonneg (inv_nonneg.mpr p.width_pos.le) (norm_nonneg _)

omit [Fintype ι] in
theorem continuous_sourceGrowthSlope {ell : ℝ} :
    Continuous (sourceGrowthSlope (ι := ι) (ell := ell)) := by
  exact (SourceParameters.continuous_width.inv₀ (fun p => p.width_pos.ne')).mul
    (continuous_const.mul (SourceParameters.continuous_radius.mul continuous_const))

theorem continuous_sourceGrowthOffset {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2) :
    Continuous (sourceGrowthOffset F b (ell := ell)) := by
  have hm (t : ℝ) (ht : -1 < t ∧ t < 1) :
      Continuous (fun p : SourceParameters E ell => conditionalMean F p.center p.radius t 0) := by
    have hc : Continuous (fun p : SourceParameters E ell =>
        (p.center, p.radius, t, (0 : E))) :=
      SourceParameters.continuous_center.prodMk
        (SourceParameters.continuous_radius.prodMk (continuous_const.prodMk continuous_const))
    have hh := (contDiffOn_conditionalMean_parameters hF hlo hup).continuousOn.comp_continuous
      hc (fun p => ⟨p.radius_pos, ht⟩)
    simpa only [Function.comp_def] using hh
  exact (SourceParameters.continuous_width.inv₀ (fun p => p.width_pos.ne')).mul
    ((hm b ⟨by linarith, hb1⟩).sub (hm 0 ⟨by norm_num, by norm_num⟩)).norm

theorem norm_sourceVelocity_le {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell b : ℝ} (hell : 0 ≤ ell) (hb : 0 ≤ b) (hb1 : b < 1)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (p : SourceParameters E ell) (z : Phase E) :
    ‖velocity (transportedSteinKernelTranspose hF hell hlo hup p.center p.radius_pos hb hb1)
      (conditionalMean F p.center p.radius b) (conditionalMean F p.center p.radius 0 0)
      p.width z‖ ≤ sourceGrowthSlope p * ‖z‖ + sourceGrowthOffset F b p := by
  have h := norm_velocity_le (A := 2 * Real.exp 1 * (p.radius * ell))
    (B := ⟨p.radius * ell, mul_nonneg p.radius_pos.le hell⟩)
    (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (mul_nonneg p.radius_pos.le hell))
    (norm_transportedSteinKernelTranspose_le hF hell hlo hup p.center p.radius_pos hb hb1 p.small)
    (lipschitzWith_conditionalMean hF hell hlo hup p.center p.radius_pos (by linarith) hb1)
    (conditionalMean F p.center p.radius 0 0) p.width_pos z
  change _ ≤ p.width⁻¹ * ((2 * Real.exp 1 * (p.radius * ell) + p.radius * ell) * ‖z‖ +
    ‖conditionalMean F p.center p.radius b 0 - conditionalMean F p.center p.radius 0 0‖) at h
  convert h using 1
  dsimp [sourceGrowthSlope, sourceGrowthOffset]
  ring

/-- The literal source phase field, with its Hilbert product norm. -/
def sourceParameterVelocity {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell b : ℝ} (hell : 0 ≤ ell) (hb : 0 ≤ b) (hb1 : b < 1)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (p : SourceParameters E ell) : Phase E → Phase E :=
  velocity (transportedSteinKernelTranspose hF hell hlo hup p.center p.radius_pos hb hb1)
    (conditionalMean F p.center p.radius b) (conditionalMean F p.center p.radius 0 0) p.width

theorem contDiff_sourceParameterVelocity {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell b : ℝ} (hell : 0 ≤ ell) (hb : 0 ≤ b) (hb1 : b < 1)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (p : SourceParameters E ell) :
    ContDiff ℝ 1 (sourceParameterVelocity hF hell hb hb1 hlo hup p) :=
  contDiff_velocity
    (sourceKernel_contDiff_one hF hell hlo hup p.center p.radius_pos hb hb1 p.small)
    (contDiff_one_conditionalMean hF hlo hup p.center p.radius (by linarith) hb1) _ _

end AcceleratedLogConcave.Conditional.Centering
