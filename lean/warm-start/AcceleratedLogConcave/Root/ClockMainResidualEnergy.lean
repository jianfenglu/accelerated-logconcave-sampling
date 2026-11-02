import AcceleratedLogConcave.Root.ClockCenterMoment
import AcceleratedLogConcave.Root.OuterRootMainResidual

/-! Actual main-row graph residual under the full original Clock base law. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockMainResidualEnergy
open Oracle ClockChronologicalCoupling OuterRootFlowIdentification ClockCenterMoment
variable (P : SourceSchedule) {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (clock : ClockLaw.Clock) (i : ClockNoisyLayer.Index P)

def residual (b : Base P d) : Point d :=
  OuterRootMainResidual.residual hV hm P.delta_pos hlo hup P.K clock i (physicalSeed P b)

theorem residual_eq_graph (b : Base P d) :
    residual P hV hm hlo hup clock i b =
      (ClockCollocation.graph P.delta P.delta_pos P.K clock b.1.1
        (ClockPublicSetup.splitValues b.1.2 b.2.1 0)).updateFromReplies
        (fun j => OuterRootLiteralScore.score hV P.delta_pos (lower_nonneg hm hlo) hup
          b.1.1 (ClockPublicSetup.splitValues b.1.2 b.2.1 0)
          (ClockCollocation.u P.delta P.K clock j)) i -
      ClockChronologicalCoupling.center P clock hV (lower_nonneg hm hlo) hup i b := by
  rw [residual,OuterRootMainResidual.residual_eq_graph,ClockCenterMoment.center_eq P hV hm hlo hup]
  simp only [physicalSeed,OuterRootCenterMoment.center,smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr P.delta_pos).ne',one_smul,ClockCollocation.rF]

theorem residual_energy (hsmall : P.delta≤1/2) :
    Integrable (fun b => ‖residual P hV hm hlo hup clock i b‖^2) (baseLaw P hV hm hlo hup) ∧
    (∫ b,‖residual P hV hm hlo hup clock i b‖^2 ∂baseLaw P hV hm hlo hup)≤
      ((ClockCollocation.rF P.delta/2)*ClockQuadraturePower.orderConstant P.K*
        Real.sqrt (d:ℝ)*P.delta^(P.K+6))^2 := by
  obtain ⟨hi,hb⟩ := OuterRootMainResidual.residual_energy hV hm P.delta_pos hlo hup P.K clock i hsmall
  have hp := physicalSeed_preserving P hV hm hlo hup
  refine ⟨hp.integrable_comp_of_integrable hi,?_⟩
  have hmeas := hi.aestronglyMeasurable
  rw [← hp.map_eq] at hmeas
  have heq := integral_map hp.measurable.aemeasurable hmeas
  rw [hp.map_eq] at heq
  exact heq.symm.trans_le (by simpa using hb)
end AcceleratedLogConcave.Root.ClockMainResidualEnergy
