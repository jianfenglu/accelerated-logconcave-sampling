import AcceleratedLogConcave.Root.ClockCollocation
import AcceleratedLogConcave.Root.CubicOuterMainStability

/-! The constructed graph supplies the outer inventory witness. The resulting
mean stability is standalone: no noisy outer layer, loop or law is asserted. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockCollocation
open Oracle Oracle.CubicScheduleThreshold Oracle.FixedTapeStability Oracle.RecursiveSize
open FinalMeanScheduledData OuterMainStability
variable (P : SourceSchedule)

/-- Exact cardinality of the constructed center type at the prescribed resolution. -/
theorem prescribed_inventory :
    (Fintype.card (MainIndex P.delta P.K):ℝ) =
      128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ) := by
  rw [card_mainIndex, count, OuterInventoryPayment.outer_cells_literal]
  unfold ClockSchedule.sourceOrder
  push_cast
  ring

theorem prescribed_inventory_witness (hC : 1 ≤ P.Csch) :
    (count P.delta P.K:ℝ) ≤
      P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ) := by
  have he := prescribed_inventory P
  rw [card_mainIndex] at he
  rw [he]
  calc
    _ ≤ P.Csch*(128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ)) :=
      le_mul_of_one_le_left (by positivity) hC
    _ = _ := by ring

/-- This inventory is the length of the actual finite graph's request plan. -/
theorem prescribed_request_inventory {E : Type*} [AddCommGroup E] [Module ℝ E]
    (hC : 1 ≤ P.Csch) (clock : ClockLaw.Clock) (xF Y0 : E)
    (old : MainIndex P.delta P.K → E) :
    (((graph P.delta P.delta_pos P.K clock xF Y0).requestPlan old).length:ℝ) ≤
      P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ) := by
  rw [(requestPlan_inventory P.delta P.delta_pos P.K clock xF Y0 old).1]
  exact prescribed_inventory_witness P hC

/-- The existing main state receives precisely this graph radius. -/
theorem mainState_graph_radius {E : Type*} [AddCommGroup E] [Module ℝ E]
    (clock : ClockLaw.Clock) (xF Y0 : E) (i : MainIndex P.delta P.K) :
    (mainState P (count P.delta P.K) i clock).radius =
      (graph P.delta P.delta_pos P.K clock xF Y0).radius i := rfl

section Cubic
variable (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
  (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y)
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC hy
include hK hc hsmall hC hy

/-- The old scalar payment, now paid by a constructed graph rather than a witness premise. -/
theorem constructed_inventory_payment :
    4*Real.sqrt (count P.delta P.K:ℝ)*P.delta^(1-P.t) ≤ 1 :=
  OuterInventoryPayment.cubic_inventory_payment P hK hc hsmall hC hy
    (prescribed_inventory_witness P (by linarith))

theorem constructed_main_certificate (i : MainIndex P.delta P.K) (clock : ClockLaw.Clock) :
    0 < (mainState P (count P.delta P.K) i clock).radius ∧
    0 < (mainState P (count P.delta P.K) i clock).width ∧
    SizeBound P.delta P.delta 1 1 (mainState P (count P.delta P.K) i clock).radius
      (mainState P (count P.delta P.K) i clock).width :=
  CubicOuterMainStability.initial_main_certificate P hK hc hsmall hC hy
    (count_pos P.delta_pos P.K) i clock (prescribed_inventory_witness P (by linarith))

section OriginalOracle
variable {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
include hV hlo hup

/-- Standalone main mean with the constructed inventory and unchanged raw gradient. -/
theorem constructed_main_stable (i : MainIndex P.delta P.K) (clock : ClockLaw.Clock) :
    let E := mainData P hR hc hsmall (count P.delta P.K) i clock
    ChildStable E.program E.coefficient (gradient V) (2*P.delta) :=
  CubicOuterMainStability.standalone_main_stable P hK hc hsmall hC hy hV hlo hup
    (count_pos P.delta_pos P.K) i clock (prescribed_inventory_witness P (by linarith))

/-- Same complete input momentum and raw tape, at two designated centers. -/
theorem constructed_main_sub_le (i : MainIndex P.delta P.K) (clock : ClockLaw.Clock)
    (momentum x z : Point d)
    (tape : Tape d (mainData P hR hc hsmall (count P.delta P.K) i clock).program) :
    let E := mainData P hR hc hsmall (count P.delta P.K) i clock
    ‖RetainedMeanFinalBatch.childPoint (run E.program (gradient V)
        ⟨E.coefficient,x,momentum⟩ Env.empty tape) -
      RetainedMeanFinalBatch.childPoint (run E.program (gradient V)
        ⟨E.coefficient,z,momentum⟩ Env.empty tape)‖ ≤ 2*P.delta*‖x-z‖ :=
  CubicOuterMainStability.standalone_main_sub_le P hK hc hsmall hC hy hV hlo hup
    (count_pos P.delta_pos P.K) i clock (prescribed_inventory_witness P (by linarith)) momentum x z tape
end OriginalOracle
end Cubic
end AcceleratedLogConcave.Root.ClockCollocation
