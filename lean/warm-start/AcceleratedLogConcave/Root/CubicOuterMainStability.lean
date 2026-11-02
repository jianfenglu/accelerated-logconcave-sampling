import AcceleratedLogConcave.Root.OuterInventoryPayment
import AcceleratedLogConcave.Root.OuterMainStability

/-! The unchanged cubic schedule pays the distinct main-width scalar inequality
from an explicit outer inventory witness. The actual outer table, loop and law
are not constructed. The old literal standalone executable is retained. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.CubicOuterMainStability
open Oracle Oracle.CubicExecutableWorkShift Oracle.CubicScheduleThreshold
open Oracle.FixedTapeStability Oracle.RecursiveSize
open FinalMeanScheduledData OuterMainStability OuterInventoryPayment
variable (P : SourceSchedule)
  (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
  (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y)
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC hy
include hK hc hsmall hC hy

/-- The positive initial certificate, with inventory witness instead of hpay. -/
theorem initial_main_certificate {Nr : ℕ} (hNr : 0 < Nr) (i : Slot P) (clock : ClockLaw.Clock)
    (hinv : (Nr:ℝ) ≤ P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ)) :
    0 < (mainState P Nr i clock).radius ∧ 0 < (mainState P Nr i clock).width ∧
    SizeBound P.delta P.delta 1 1 (mainState P Nr i clock).radius (mainState P Nr i clock).width :=
  OuterMainInitialCertificate.mainSlot_initialCertificate P.delta_pos (delta_half P hK hc hsmall hC hy)
    P.t hNr P.K i clock (cubic_inventory_payment P hK hc hsmall hC hy hinv)

section OriginalOracle
variable {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
include hV hlo hup

/-- The actual standalone main mean: the old scalar payment is now derived. -/
theorem standalone_main_stable {Nr : ℕ} (hNr : 0 < Nr) (i : Slot P) (clock : ClockLaw.Clock)
    (hinv : (Nr:ℝ) ≤ P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ)) :
    let E := mainData P hR hc hsmall Nr i clock
    ChildStable E.program E.coefficient (gradient V) (2*P.delta) :=
  main_mean_stable P hK hc hsmall hC hy hV hlo hup hNr i clock
    (cubic_inventory_payment P hK hc hsmall hC hy hinv)

/-- Same designated momentum and full raw tape for both centers. -/
theorem standalone_main_sub_le {Nr : ℕ} (hNr : 0 < Nr) (i : Slot P) (clock : ClockLaw.Clock)
    (hinv : (Nr:ℝ) ≤ P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ))
    (momentum x z : Point d) (tape : Tape d (mainData P hR hc hsmall Nr i clock).program) :
    let E := mainData P hR hc hsmall Nr i clock
    ‖RetainedMeanFinalBatch.childPoint (run E.program (gradient V)
        ⟨E.coefficient,x,momentum⟩ Env.empty tape) -
      RetainedMeanFinalBatch.childPoint (run E.program (gradient V)
        ⟨E.coefficient,z,momentum⟩ Env.empty tape)‖ ≤ 2*P.delta*‖x-z‖ :=
  main_mean_sub_le P hK hc hsmall hC hy hV hlo hup hNr i clock
    (cubic_inventory_payment P hK hc hsmall hC hy hinv) momentum x z tape
end OriginalOracle
end AcceleratedLogConcave.Root.CubicOuterMainStability
