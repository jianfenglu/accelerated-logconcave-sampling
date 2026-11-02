import AcceleratedLogConcave.Root.ClockMainResidualEnergy
import AcceleratedLogConcave.Root.ClockMainInitialEnergy

/-! Concrete L2 payments for the initial and row defects of the actual Clock
iteration. The original-data moment and quadrature suppliers discharge them. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory
namespace AcceleratedLogConcave.Root.ClockMainEnergyPayments
open Oracle ClockChronologicalCoupling ClockCenterMoment OuterRootFlowIdentification
variable (P : SourceSchedule) {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (clock : ClockLaw.Clock) (i : ClockNoisyLayer.Index P)

theorem residual_memLp : MemLp (ClockMainResidualEnergy.residual P hV hm hlo hup clock i)
    2 (baseLaw P hV hm hlo hup) :=
  (OuterRootMainResidual.residual_memLp hV hm P.delta_pos hlo hup P.K clock i).comp_measurePreserving
    (physicalSeed_preserving P hV hm hlo hup)

theorem residual_norm_le (hsmall : P.delta≤1/2) :
    ‖(residual_memLp P hV hm hlo hup clock i).toLp
      (ClockMainResidualEnergy.residual P hV hm hlo hup clock i)‖≤
      (ClockCollocation.rF P.delta/2)*ClockQuadraturePower.orderConstant P.K*
        Real.sqrt (d:ℝ)*P.delta^(P.K+6) := by
  have hb := (ClockMainResidualEnergy.residual_energy P hV hm hlo hup clock i hsmall).2
  rw [← Analysis.DominatedLp.norm_sq_toLp (residual_memLp P hV hm hlo hup clock i)] at hb
  apply (sq_le_sq₀ (norm_nonneg _) ?_).mp hb
  exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
    (ClockQuadraturePower.orderConstant_nonneg P.K)) (Real.sqrt_nonneg _))
    (pow_nonneg P.delta_pos.le _)
end AcceleratedLogConcave.Root.ClockMainEnergyPayments
