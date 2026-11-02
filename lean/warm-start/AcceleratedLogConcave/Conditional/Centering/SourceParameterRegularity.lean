import AcceleratedLogConcave.Conditional.Centering.ParameterODE
import AcceleratedLogConcave.Conditional.Centering.SourceParameterGrowth
import AcceleratedLogConcave.Conditional.Stein.ParameterRegularity

/-!
# Joint regularity of the actual complete source centering flow

The relative source domain retains the equality boundary of the radius band.
All field coefficients below are the literal transported Stein kernel and
conditional means. Compact trajectory control uses the actual continuous
linear-growth coefficients, and spatial Lipschitz control is required only
for each fixed limiting field on a common compact ball.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff

namespace AcceleratedLogConcave.Conditional.Centering

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The literal source phase field is jointly continuous in parameters and phase. -/
theorem continuous_sourceParameterVelocity {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell b : ℝ} (hell : 0 ≤ ell) (hb : 0 ≤ b) (hb1 : b < 1)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2) :
    Continuous (fun p : SourceParameters E ell × Phase E =>
      sourceParameterVelocity hF hell hb hb1 hlo hup p.1 p.2) := by
  have hy : Continuous (fun p : SourceParameters E ell × Phase E => p.2.fst) :=
    (WithLp.prod_continuous_ofLp 2 E E).fst.comp continuous_snd
  have hg : Continuous (fun p : SourceParameters E ell × Phase E => p.2.snd) :=
    (WithLp.prod_continuous_ofLp 2 E E).snd.comp continuous_snd
  have hK := (continuous_transportedSteinKernelTranspose_parameters hF hell hlo hup hb hb1).comp
    (continuous_fst.prodMk hy)
  have hM := (continuous_conditionalMean_sourceParameters hF hlo hup hb1).comp
    (continuous_fst.prodMk
      ((continuous_const : Continuous (fun _ : SourceParameters E ell × Phase E =>
        (⟨b, hb, le_rfl⟩ : Icc 0 b))).prodMk hy))
  have hu := (continuous_conditionalMean_sourceParameters hF hlo hup hb1).comp
    (continuous_fst.prodMk
      ((continuous_const : Continuous (fun _ : SourceParameters E ell × Phase E =>
        (⟨0, le_rfl, hb⟩ : Icc 0 b))).prodMk
          (continuous_const : Continuous (fun _ : SourceParameters E ell × Phase E => (0 : E)))))
  have hs := (SourceParameters.continuous_width.comp
    (continuous_fst : Continuous (Prod.fst : SourceParameters E ell × Phase E → _))).inv₀
      (fun p => p.1.width_pos.ne')
  exact (WithLp.prod_continuous_toLp 2 E E).comp
    ((hs.smul (hK.clm_apply hg)).neg.prodMk (hs.smul (hM.sub hu)))

/-- The actual source centering flow varies jointly with all source parameters,
all real times, and the initial Hilbert phase point. -/
theorem continuous_sourceCenteringFlow_parameters {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell b : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (hb : 0 ≤ b) (hb1 : b < 1) :
    Continuous (fun p : SourceParameters E ell × ℝ × Phase E =>
      sourceCenteringFlow hF hell hlo hup p.1.center p.1.radius_pos hb hb1
        p.1.small p.1.width_pos p.2.2 p.2.1) := by
  let f (p : SourceParameters E ell × Phase E) :=
    sourceParameterVelocity hF hell hb hb1 hlo hup p.1
  let γ (p : SourceParameters E ell × Phase E) : ℝ → Phase E :=
    sourceCenteringFlow hF hell hlo hup p.1.center p.1.radius_pos hb hb1
      p.1.small p.1.width_pos p.2
  have hd (p : SourceParameters E ell × Phase E) (t : ℝ) :
      HasDerivAt (γ p) (f p (γ p t)) t :=
    sourceCenteringFlow_deriv hF hell hlo hup p.1.center p.1.radius_pos hb hb1
      p.1.small p.1.width_pos p.2 t
  have hγ (p : SourceParameters E ell × Phase E) : Continuous (γ p) :=
    continuous_iff_continuousAt.mpr (fun t => (hd p t).continuousAt)
  have hi : Continuous (fun p : SourceParameters E ell × Phase E => γ p 0) := by
    simpa only [γ, sourceCenteringFlow_initial] using
      (continuous_snd : Continuous (Prod.snd : SourceParameters E ell × Phase E → Phase E))
  have hc := continuous_parameter_trajectory_joint_of_linear_growth
    (f := f) (γ := γ)
    (C := fun p => sourceGrowthSlope p.1)
    (D := fun p => sourceGrowthOffset F b p.1)
    ((continuous_sourceParameterVelocity hF hell hb hb1 hlo hup).comp
      (continuous_fst.fst.prodMk continuous_snd))
    (fun p => contDiff_sourceParameterVelocity hF hell hb hb1 hlo hup p.1)
    ((continuous_sourceGrowthSlope (ell := ell)).comp continuous_fst)
    ((continuous_sourceGrowthOffset hF hb hb1 hlo hup).comp continuous_fst)
    (fun p => sourceGrowthSlope_nonneg hell p.1)
    (fun p => sourceGrowthOffset_nonneg F b p.1)
    (fun p z => norm_sourceVelocity_le hF hell hb hb1 hlo hup p.1 z) hγ hd hi
  have hperm : Continuous (fun p : SourceParameters E ell × ℝ × Phase E =>
      ((p.1, p.2.2), p.2.1)) :=
    (continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst
  simpa only [Function.comp_def, γ] using hc.comp hperm

/-- The exact momentum increment at source time one is jointly continuous. -/
theorem continuous_sourceCenteringFlow_increment_parameters {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {ell b : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (hb : 0 ≤ b) (hb1 : b < 1) :
    Continuous (fun p : SourceParameters E ell × Phase E =>
      (sourceCenteringFlow hF hell hlo hup p.1.center p.1.radius_pos hb hb1
        p.1.small p.1.width_pos p.2 1).snd - p.2.snd) := by
  have hf := (continuous_sourceCenteringFlow_parameters hF hell hlo hup hb hb1).comp
    (continuous_fst.prodMk
      ((continuous_const : Continuous (fun _ : SourceParameters E ell × Phase E => (1 : ℝ))).prodMk
        continuous_snd))
  exact ((WithLp.prod_continuous_ofLp 2 E E).snd.comp hf).sub
    ((WithLp.prod_continuous_ofLp 2 E E).snd.comp continuous_snd)

/-- Borel measurability of the actual source family, with its relative domain. -/
theorem measurable_sourceCenteringFlow_parameters {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell b : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (hb : 0 ≤ b) (hb1 : b < 1) :
    Measurable (fun p : SourceParameters E ell × ℝ × Phase E =>
      sourceCenteringFlow hF hell hlo hup p.1.center p.1.radius_pos hb hb1
        p.1.small p.1.width_pos p.2.2 p.2.1) :=
  (continuous_sourceCenteringFlow_parameters hF hell hlo hup hb hb1).measurable

/-- The literal retained-momentum increment is a Borel parameter family. -/
theorem measurable_sourceCenteringFlow_increment_parameters {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {ell b : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (hb : 0 ≤ b) (hb1 : b < 1) :
    Measurable (fun p : SourceParameters E ell × Phase E =>
      (sourceCenteringFlow hF hell hlo hup p.1.center p.1.radius_pos hb hb1
        p.1.small p.1.width_pos p.2 1).snd - p.2.snd) :=
  (continuous_sourceCenteringFlow_increment_parameters hF hell hlo hup hb hb1).measurable

end AcceleratedLogConcave.Conditional.Centering
