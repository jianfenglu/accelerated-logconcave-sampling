import AcceleratedLogConcave.Root.ClockRetainedFinalSplice
import AcceleratedLogConcave.Oracle.CovarianceSetupMeasurability

/-! Measurability of the actual clock-dependent public and retained-final
coefficients, with the source finite node inventory fixed before clock draw. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace AcceleratedLogConcave.Root.ClockCoefficientMeasurability
open MeasureTheory Oracle
open ClockNoisyLayer ClockCollocation ClockSchedule ClockRetainedFinalSplice

variable (P : SourceSchedule)

theorem measurable_u (i : Index P) :
    Measurable (fun clock : ClockLaw.Clock => ClockCollocation.u P.delta P.K clock i) := by
  unfold ClockCollocation.u
  fun_prop

theorem measurable_W (i j : Index P) :
    Measurable (fun clock : ClockLaw.Clock =>
      ClockCollocation.W P.delta P.delta_pos P.K clock
        (ClockCollocation.v P.delta P.K i) j) := by
  unfold ClockCollocation.W
  fun_prop

theorem measurable_A : Measurable (ClockNoisyLayer.A P) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun clock : ClockLaw.Clock =>
    -(ClockCollocation.rF P.delta)^2 *
      ClockCollocation.u P.delta P.K clock i *
      ClockCollocation.W P.delta P.delta_pos P.K clock
        (ClockCollocation.v P.delta P.K i) j)
  exact (measurable_const.mul (measurable_u P i)).mul (measurable_W P i j)

theorem measurable_radius (i : Index P) :
    Measurable (fun clock : ClockLaw.Clock => ClockNoisyLayer.radius P clock i) := by
  change Measurable (fun clock : ClockLaw.Clock =>
    ClockCollocation.rF P.delta * Real.sqrt
      (1-(ClockCollocation.u P.delta P.K clock i)^2))
  exact measurable_const.mul (measurable_const.sub ((measurable_u P i).pow_const 2)).sqrt

theorem measurable_radius_family :
    Measurable (fun clock : ClockLaw.Clock => ClockNoisyLayer.radius P clock) := by
  apply Measurable.of_eval
  intro i
  exact measurable_radius P i

theorem measurable_C : Measurable (ClockNoisyLayer.C P) := by
  exact CovarianceSetup.measurable_residualRoot (ClockNoisyLayer.A P)
    (fun _ => ClockNoisyLayer.rhoC P) (fun _ => ClockNoisyLayer.a P)
    (measurable_A P) measurable_const measurable_const

theorem measurable_public_slope (i : Index P) :
    Measurable (fun clock : ClockLaw.Clock => ClockPublicSetup.slopes P clock i) := by
  unfold ClockPublicSetup.slopes
  exact measurable_const.mul (measurable_u P i)

theorem measurable_public_slopes :
    Measurable (ClockPublicSetup.slopes P) := by
  apply Measurable.of_eval
  intro i
  exact measurable_public_slope P i

theorem measurable_direct {d : ℕ} (xF Y0 : Point d) (i : Index P) :
    Measurable (fun clock : ClockLaw.Clock => ClockNoisyLayer.b P clock xF Y0 i) := by
  change Measurable (fun clock : ClockLaw.Clock =>
    xF + (ClockCollocation.rF P.delta *
      ClockCollocation.u P.delta P.K clock i) • Y0)
  exact measurable_const.add ((measurable_const.mul (measurable_u P i)).smul measurable_const)

theorem measurable_direct_family {d : ℕ} (xF Y0 : Point d) :
    Measurable (fun clock : ClockLaw.Clock => ClockNoisyLayer.b P clock xF Y0) := by
  apply Measurable.of_eval
  intro i
  exact measurable_direct P xF Y0 i

/-- The public direct row is jointly measurable in the clock and both input
vectors, as required for the input-indexed full-root kernel. -/
theorem measurable_direct_joint {d : ℕ} (i : Index P) :
    Measurable (fun z : ClockLaw.Clock × (Point d × Point d) =>
      ClockNoisyLayer.b P z.1 z.2.1 z.2.2 i) := by
  change Measurable (fun z : ClockLaw.Clock × (Point d × Point d) =>
    z.2.1 + (ClockCollocation.rF P.delta *
      ClockCollocation.u P.delta P.K z.1 i) • z.2.2)
  have hu : Measurable (fun z : ClockLaw.Clock × (Point d × Point d) =>
      ClockCollocation.u P.delta P.K z.1 i) :=
    (measurable_u P i).comp measurable_fst
  exact measurable_snd.fst.add ((measurable_const.mul hu).smul measurable_snd.snd)

theorem measurable_direct_joint_family {d : ℕ} :
    Measurable (fun z : ClockLaw.Clock × (Point d × Point d) =>
      ClockNoisyLayer.b P z.1 z.2.1 z.2.2) := by
  apply Measurable.of_eval
  intro i
  exact measurable_direct_joint P i

theorem measurable_weight (i : Index P) :
    Measurable (fun clock : ClockLaw.Clock => ClockRetainedFinalSplice.weight P clock i) := by
  unfold ClockRetainedFinalSplice.weight ClockSchedule.weight
  fun_prop

theorem measurable_weight_family :
    Measurable (fun clock : ClockLaw.Clock => ClockRetainedFinalSplice.weight P clock) := by
  apply Measurable.of_eval
  intro i
  exact measurable_weight P i

theorem measurable_final_radius (i : Index P) :
    Measurable (fun clock : ClockLaw.Clock =>
      (FinalMeanScheduledData.state P i clock).radius) := by
  change Measurable (ClockBackwardKernel.sourceRadius P.delta P.delta_pos P.K i)
  exact (ClockBackwardKernel.continuous_sourceRadius P.delta P.delta_pos P.K i).measurable

theorem measurable_width (i : Index P) :
    Measurable (fun clock : ClockLaw.Clock => ClockRetainedFinalSplice.width P clock i) := by
  change Measurable (fun _ : ClockLaw.Clock => ClockBackwardKernel.sourceWidth P.delta)
  exact measurable_const

theorem measurable_width_family :
    Measurable (fun clock : ClockLaw.Clock => ClockRetainedFinalSplice.width P clock) := by
  apply Measurable.of_eval
  intro i
  exact measurable_width P i

theorem measurable_correctionWeight (i : Index P) :
    Measurable (fun clock : ClockLaw.Clock =>
      ClockRetainedFinalSplice.correctionWeight P clock i) := by
  unfold ClockRetainedFinalSplice.correctionWeight ClockRetainedFinalSplice.coefficient
  exact (measurable_weight P i).neg.div (measurable_width P i)

theorem measurable_correctionWeight_family :
    Measurable (fun clock : ClockLaw.Clock =>
      ClockRetainedFinalSplice.correctionWeight P clock) := by
  apply Measurable.of_eval
  intro i
  exact measurable_correctionWeight P i

end AcceleratedLogConcave.Root.ClockCoefficientMeasurability
