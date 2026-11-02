import AcceleratedLogConcave.Root.ClockSourcePhaseKL
import AcceleratedLogConcave.Root.ClockPhaseSections
import AcceleratedLogConcave.Root.ClockReferenceSections

/-! Stationary KL for the literal uniform-clock executable phase. Only the
actual measurable implementation and prescribed reference sections are mixed;
the pointwise completed couplings need not be jointly selected in the clock. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal
namespace AcceleratedLogConcave.Root.ClockSourceStationaryKL
open Oracle Kinetic Kinetic.Reheating
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (label : ℕ) (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
  (hyQuad : ClockQuadratureResolution.threshold P.K≤P.y)
local notation "Input" => Point d × Point d
local notation "Fphys" => OuterRootFlowIdentification.family hV hm P.delta_pos hlo hup
local notation "μX" => OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup
local notation "γ" => stdGaussian (Point d)
local notation "ν" => ((Fphys).law 0).prod γ
local notation "hG" => ClockOriginalGradientKernel.originalGradient_measurable hV
local notation "ref" => ClockReferenceSections.sections P hR hc hsmall hK hC hy hV hm hlo hup
local notation "impl" => ClockPhaseSections.sections P hR hc hsmall label
local instance center_probability : IsProbabilityMeasure μX := by unfold OuterRootExactTapePath.centerLaw; infer_instance
local instance physical_probability : IsProbabilityMeasure ν := by infer_instance

/-- The actual normalized entering center has the correct physical phase law. -/
theorem inputScale_law : ((μX).prod γ).map (ClockPhaseSections.inputScale P)=ν := by
  have hp : MeasurePreserving (fun x : Point d => Real.sqrt P.delta • x) μX ((Fphys).law 0) :=
    ⟨by fun_prop,OuterRootExactTapePath.centerLaw_physical_map P hV hm P.delta_pos hlo hup⟩
  exact (hp.prod (MeasurePreserving.id γ)).map_eq

include hyMean hyQuad in
/-- Fixed-clock stationary KL follows from the same retained joint and exact
source sections, rather than from a Gaussian output marginal. -/
theorem section_KL_le {Γ : ℝ} (hΓ : 0<Γ) (hhalf : Γ≤1/2) (u : UniformValue) :
    (∫⁻ x,klDiv (ref Γ (x,u)) (impl Γ (gradient V) hG (x,u)) ∂ν)≤
      ENNReal.ofReal (512*(d:ℝ)*(P.delta^P.K)^2/Γ) := by
  have h := ClockSourcePhaseKL.completed_phase_KL_paid P hR hc hsmall hK hC hy hV hm hlo hup
    (ClockUniformDraw.clockOfUniform u) label hyMean hyQuad hΓ hhalf
  dsimp only at h
  rw [ClockReferenceSections.completed_joint_section P hR hc hsmall hK hC hy hV hm hlo hup label hyMean Γ u,
    ClockPhaseSections.implemented_joint_section P hR hc hsmall label Γ (gradient V) hG u,
    inputScale_law P hV hm hlo hup,
    Probability.klDiv_compProd_same_eq_lintegral] at h
  exact h

private theorem averaged_eq_mixture (Γ : ℝ) (x : Input) :
    ClockReferenceSections.averaged P hR hc hsmall hK hC hy hV hm hlo hup Γ x=
      ((ref Γ).comap (fun u => (x,u)) measurable_prodMk_left) ∘ₘ (volume : Measure UniformValue) := by
  ext t ht
  rw [ClockReferenceSections.averaged_apply P hR hc hsmall hK hC hy hV hm hlo hup Γ x ht,
    Measure.bind_apply ht (Kernel.aemeasurable _)]
  rfl

include hyMean hyQuad in
/-- Concrete actual uniform-clock stationary phase KL, with all root accuracy
and original-data moment inputs supplied by the prescribed recursion. -/
theorem averaged_KL_le {Γ : ℝ} (hΓ : 0<Γ) (hhalf : Γ≤1/2) :
    (∫⁻ x,klDiv (ClockReferenceSections.averaged P hR hc hsmall hK hC hy hV hm hlo hup Γ x)
      (ClockFinitePhaseKernel.kernel P hR hc hsmall label Γ (gradient V) hG x) ∂ν)≤
      ENNReal.ofReal (512*(d:ℝ)*(P.delta^P.K)^2/Γ) := by
  simp_rw [averaged_eq_mixture P hR hc hsmall hK hC hy hV hm hlo hup]
  exact (ClockPhaseSections.averaged_KL_le P hR hc hsmall label Γ (gradient V) hG ν (ref Γ)).trans
    ((lintegral_mono (section_KL_le P hR hc hsmall hK hC hy hV hm hlo hup label hyMean hyQuad hΓ hhalf)).trans_eq
      (by simp))
local notation "H" => ClockReferencePhaseLaw.heatFamily P hV hm hlo hup
private theorem variance_pos : 0<2*P.delta^2 := by nlinarith [sq_pos_of_pos P.delta_pos]
private theorem variance_lt : 2*P.delta^2<2*(2*P.delta^2) := by nlinarith [sq_pos_of_pos P.delta_pos]
include hc hsmall hC in
private theorem order_pos : 0<P.m := by
  have h := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  omega
local notation "Q" => OriginalReferenceMixing.referenceKernel hV (inv_pos.mpr hm) P.delta_pos
  (FinalMeanScheduledData.delta_half P hK hc hsmall hC hy)
  (by simpa only [inv_inv] using hlo) hup (Oracle.CubicExecutableWorkShift.source P hR).M (order_pos P hc hsmall hC)
  P.t (P.t_pos hc) P.K

/-- The exact accepted source reference phase, including its prescribed
physical-radius child kernels. -/
def acceptedPhase (Γ : ℝ) : Kernel Input Input := by
  let := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  exact ReferencePhaseLaw.phaseKernel H (variance_pos P) (variance_lt P) (Real.sqrt 2*P.delta) Γ Q

include hyMean hyQuad in
/-- Stationary KL against the exact accepted reference phase, for the actual
full executable with its genuine uniform clock. -/
theorem accepted_KL_le {Γ : ℝ} (hΓ : 0<Γ) (hhalf : Γ≤1/2) :
    (∫⁻ x,klDiv (acceptedPhase P hR hc hsmall hK hC hy hV hm hlo hup Γ x)
      (ClockFinitePhaseKernel.kernel P hR hc hsmall label Γ (gradient V) hG x) ∂ν)≤
      ENNReal.ofReal (512*(d:ℝ)*(P.delta^P.K)^2/Γ) := by
  let := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  have he := ClockReferenceSections.averaged_eq_source_phase_ae P hR hc hsmall hK hC hy hV hm hlo hup Γ
  have hsame : (fun x => klDiv (acceptedPhase P hR hc hsmall hK hC hy hV hm hlo hup Γ x)
      (ClockFinitePhaseKernel.kernel P hR hc hsmall label Γ (gradient V) hG x))=ᵐ[ν]
      (fun x => klDiv (ClockReferenceSections.averaged P hR hc hsmall hK hC hy hV hm hlo hup Γ x)
        (ClockFinitePhaseKernel.kernel P hR hc hsmall label Γ (gradient V) hG x)) := by
    filter_upwards [he] with x hx
    exact congrArg (fun k => klDiv k (ClockFinitePhaseKernel.kernel P hR hc hsmall label Γ (gradient V) hG x)) hx.symm
  exact (lintegral_congr_ae hsame).le.trans
    (averaged_KL_le P hR hc hsmall hK hC hy hV hm hlo hup label hyMean hyQuad hΓ hhalf)

include hyMean hyQuad in
/-- Concrete stationary phase supplier at the source refresh rate. Its fixed
constant is compatible with the complete phase/cooling path budget. -/
theorem source_phase_KL_le {κ : ℝ} (hκ : 1≤κ) :
    (∫⁻ x,klDiv (acceptedPhase P hR hc hsmall hK hC hy hV hm hlo hup
        (ClockFinitePhaseKernel.sourceGamma P κ) x)
      (ClockFinitePhaseKernel.kernel P hR hc hsmall label (ClockFinitePhaseKernel.sourceGamma P κ)
        (gradient V) hG x) ∂ν)≤
      ENNReal.ofReal (4096*(d:ℝ)*P.delta^(2*P.K-2)/ClockFinitePhaseKernel.sourceGamma P κ) := by
  have hΓ := ClockPhaseGaussianKL.sourceGamma_pos P hκ
  have hd := FinalMeanScheduledData.delta_half P hK hc hsmall hC hy
  refine (accepted_KL_le P hR hc hsmall hK hC hy hV hm hlo hup label hyMean hyQuad hΓ
    ((ClockPhaseGaussianKL.sourceGamma_le_delta P hκ).trans hd)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ hΓ.le
  rw [← pow_mul]
  have hp : P.delta^(P.K*2)≤P.delta^(2*P.K-2) := by
    rw [Nat.mul_comm P.K 2]
    exact pow_le_pow_of_le_one P.delta_pos.le (hd.trans (by norm_num)) (Nat.sub_le _ _)
  have hm' : 512*(d:ℝ)*P.delta^(P.K*2)≤512*(d:ℝ)*P.delta^(2*P.K-2) :=
    mul_le_mul_of_nonneg_left hp (by positivity)
  exact hm'.trans (mul_le_mul_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α:=ℝ) d] : 512*(d:ℝ)≤4096*(d:ℝ))
    (pow_nonneg P.delta_pos.le _))
end AcceleratedLogConcave.Root.ClockSourceStationaryKL
