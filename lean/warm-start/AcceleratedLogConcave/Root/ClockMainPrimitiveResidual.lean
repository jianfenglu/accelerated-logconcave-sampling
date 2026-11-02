import AcceleratedLogConcave.Root.ClockMainResidualEnergy

/-! Exact primitive-mean readout of the executed main graph residual. All
centers and radii are the prescribed Clock nodes, including clock zero. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockMainPrimitiveResidual
open Oracle ClockChronologicalCoupling OuterRootFlowIdentification
variable (P : SourceSchedule) {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (clock : ClockLaw.Clock)

theorem score_eq_primitiveMean (j : ClockNoisyLayer.Index P) (b : Base P d) :
    OuterRootLiteralScore.score hV P.delta_pos (lower_nonneg hm hlo) hup b.1.1
      (ClockPublicSetup.splitValues b.1.2 b.2.1 0) (ClockCollocation.u P.delta P.K clock j) =
    Gibbs.primitiveMean (OuterRootOriginalData.potential V P.delta)
      (center P clock hV (lower_nonneg hm hlo) hup j b) (ClockNoisyLayer.radius P clock j) := by
  rw [center_eq_source,OuterRootLiteralScore.path_eq_rawY hV P.delta_pos (lower_nonneg hm hlo) hup _ _
    ⟨(ClockCollocation.u_mem P.delta_pos P.K clock j).1,
      (ClockCollocation.u_mem P.delta_pos P.K clock j).2.trans clock.2.2⟩]
  rfl

theorem residual_eq_primitive_graph (i : ClockNoisyLayer.Index P) (b : Base P d) :
    ClockMainResidualEnergy.residual P hV hm hlo hup clock i b =
      ClockNoisyLayer.b P clock b.1.1 (ClockPublicSetup.splitValues b.1.2 b.2.1 0) i +
      (∑ j, ClockNoisyLayer.A P clock i j •
        Gibbs.primitiveMean (OuterRootOriginalData.potential V P.delta)
          (center P clock hV (lower_nonneg hm hlo) hup j b) (ClockNoisyLayer.radius P clock j)) -
      center P clock hV (lower_nonneg hm hlo) hup i b := by
  rw [ClockMainResidualEnergy.residual_eq_graph]
  simp_rw [score_eq_primitiveMean P hV hm hlo hup clock]
  rfl
end AcceleratedLogConcave.Root.ClockMainPrimitiveResidual
