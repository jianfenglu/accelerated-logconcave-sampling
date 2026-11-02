import AcceleratedLogConcave.Root.SourceWarmReference
import AcceleratedLogConcave.Root.ClockSourceStationaryKL

/-! Actual stationary local phase KL at the one public warm-start schedule.
All lower recursive accuracy, joint laws and clock averaging are proved
suppliers; only original potential and public scalar hypotheses remain. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory
namespace AcceleratedLogConcave.Root.SourceWarmLocalKL
open Oracle Kinetic Kinetic.Reheating
variable (η Cw ε : ℝ) (D : ℕ) (hη : 0<η)
  (hD : SourceWarmSchedule.dimensionThreshold η Cw ε SourceWarmSampler.costCoefficient≤D)
  {κ : ℝ} (hκ : 1≤κ) {V : Point D→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,κ⁻¹*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
local notation "P" => SourceWarmSchedule.schedule η Cw D
local notation "hR" => SourceWarmSampler.radius_guard η Cw ε D hη hD
local notation "hc" => ((SourceWarmSchedule.scalar_guards η Cw D).2.1)
local notation "hsmall" => ((SourceWarmSchedule.scalar_guards η Cw D).2.2.1)
local notation "hK" => ((SourceWarmSchedule.scalar_guards η Cw D).1)
local notation "hC" => ((SourceWarmSchedule.scalar_guards η Cw D).2.2.2)
local notation "hy" => SourceWarmSampler.cubic_threshold η Cw ε D hη hD
local notation "hk" => (show 0<κ from lt_of_lt_of_le (by norm_num) hκ)

theorem phase_KL :
    (∫⁻ x,klDiv (SourceWarmReference.phase η Cw ε D hη hD hκ hV hlo hup x)
      (SourceWarmSampler.phase η Cw ε D hη hD κ V hV x)
      ∂Schedule.Dyadic.phaseReference V (Schedule.Dyadic.sourceVariance (P).delta))≤
    ENNReal.ofReal (SourceWarmSampler.costCoefficient*(D:ℝ)*(P).delta^(2*(P).K-2)/
      Schedule.Dyadic.sourceRate κ (P).delta) := by
  let := Gibbs.originalGibbs_probability_of_hessian_lower hV hk hlo
  have h := ClockSourceStationaryKL.source_phase_KL_le P hR hc hsmall hK hC hy
    hV (inv_pos.mpr hk) hlo hup 0 (SourceWarmSchedule.mean_threshold hη hD)
    (SourceWarmSchedule.quadrature_threshold hη hD) hκ
  have hg : Real.sqrt ((κ+2*(P).delta^2)⁻¹)*(P).delta=(P).delta/Real.sqrt (κ+2*(P).delta^2) := by
    rw [Real.sqrt_inv]
    ring
  rw [OriginalReferenceBaseAlignment.phaseReference_eq_source_clock_base hV hk (P).delta_pos hlo hup]
  simpa only [SourceWarmReference.phase,SourceWarmSampler.phase,SourceWarmSampler.costCoefficient,
    ClockSourceStationaryKL.acceptedPhase,ClockReferencePhaseLaw.heatFamily,inv_inv,
    OuterRootFlowIdentification.family,RecursiveInnovation.originalPhysicalReference,
    ClockFinitePhaseKernel.originalGradientKernel,Schedule.Dyadic.sourceRate,
    ClockFinitePhaseKernel.sourceGamma,hg,originalHeatMixingFamily] using h
end AcceleratedLogConcave.Root.SourceWarmLocalKL
