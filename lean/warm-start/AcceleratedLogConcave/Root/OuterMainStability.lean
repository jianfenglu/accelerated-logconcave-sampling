import AcceleratedLogConcave.Root.OuterMainInitialCertificate
import AcceleratedLogConcave.Root.FinalMeanScheduledData
import AcceleratedLogConcave.Oracle.RecursiveCertifiedRootStability

/-! Standalone main means at the prescribed physical resolution h=delta.
Nr is independent of NP/Hs and of the final-slot inventory. The scalar
4*sqrt(Nr)*delta^(1-t)<=1 remains explicit; no outer loop or law is assembled. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.OuterMainStability
open Oracle Oracle.CubicExecutableWorkShift Oracle.CubicScheduleThreshold
open Oracle.RecursiveCall Oracle.RecursiveSize Oracle.FixedTapeStability Oracle.Precision
open FinalMeanScheduledData OuterMainInitialCertificate
open scoped BigOperators NNReal
variable (P : SourceSchedule)

def mainState (Nr : ℕ) (i : Slot P) (clock : ClockLaw.Clock) : State :=
  mainMeanState P.delta P.delta_pos P.t Nr P.K i clock

def mainData (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (Nr : ℕ) (i : Slot P) (clock : ClockLaw.Clock) : ExecutableData :=
  data P hR hc hsmall (scale P) (mainState P Nr i clock).radius
    (mainState P Nr i clock).width (mainState P Nr i clock).precision

theorem mainData_literal (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (Nr : ℕ) (i : Slot P) (clock : ClockLaw.Clock) :
    mainData P hR hc hsmall Nr i clock = data P hR hc hsmall (Real.sqrt P.delta)
      (ClockBackwardKernel.sourceRadius P.delta P.delta_pos P.K i clock)
      (1/(2*P.Ds*Real.sqrt (Nr:ℝ)*Real.sqrt (2*P.delta))) (P.K:ℝ) := rfl

theorem mainState_radius_precision (Nr : ℕ) (i : Slot P) (clock : ClockLaw.Clock) :
    (mainState P Nr i clock).radius = (FinalMeanScheduledData.state P i clock).radius ∧
    (mainState P Nr i clock).precision = (P.K:ℝ) := ⟨rfl,rfl⟩

theorem mainState_width_pos {Nr : ℕ} (hNr : 0 < Nr) (i : Slot P) (clock : ClockLaw.Clock) :
    0 < (mainState P Nr i clock).width := mainWidth_pos P.delta_pos P.t hNr

theorem step_domain (hc : 0 < P.csch) (hsmall : P.csch < 1/160) : 0 < P.t ∧ P.t < 1 :=
  ⟨P.t_pos hc, (P.t_le hc hsmall).trans_lt (by norm_num)⟩

section Scheduled
variable (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
  (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y)
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC hy

include hK hc hsmall hC hy in
/-- Only the distinct outer inventory payment remains beyond scalar schedule guards. -/
theorem initial_main_size (Nr : ℕ) (i : Slot P) (clock : ClockLaw.Clock)
    (hpay : 4*Real.sqrt (Nr:ℝ)*P.delta^(1-P.t) ≤ 1) :
    SizeBound P.delta P.delta 1 1 (mainState P Nr i clock).radius (mainState P Nr i clock).width :=
  OuterMainInitialCertificate.radiusBand_sizeBound P.delta_pos (delta_half P hK hc hsmall hC hy)
    P.t Nr (ClockBackwardKernel.radiusParameter P.delta P.delta_pos P.K i clock) hpay

/-- Work is uniform in all standalone inputs and complete tapes, independently of hpay. -/
theorem main_work {d : ℕ} (Nr : ℕ) (i : Slot P) (clock : ClockLaw.Clock) (oracle : Point d → Point d)
    (input : Inputs d (mainData P hR hc hsmall Nr i clock).size)
    (tape : Tape d (mainData P hR hc hsmall Nr i clock).program) :
    let E := mainData P hR hc hsmall Nr i clock
    let counts := traceCounts (run E.program oracle input Env.empty tape).trace
    ((counts.queries+counts.gaussianBlocks:ℕ):ℝ) ≤ Real.exp (P.y/64) :=
  (executed_work P hK hc hsmall hC hy (scale P) (mainState P Nr i clock).radius
    (mainState P Nr i clock).width (P.K:ℝ) le_rfl oracle input tape).2

theorem main_queryShift_and_mass (Nr : ℕ) (i : Slot P) (clock : ClockLaw.Clock) :
    let E := mainData P hR hc hsmall Nr i clock
    ChildAbsorption.QueryShift E.program E.enumeration E.coefficient (mainState P Nr i clock).radius E.shiftVector ∧
      CovarianceSetup.shiftSq E.shiftVector ≤ P.Ds^2 := by
  have hs := queryShift_and_mass P hK hc hsmall hC hy (scale P) (mainState P Nr i clock).radius
    (mainState P Nr i clock).width (P.K:ℝ) (root_positive P i clock).1 le_rfl
  exact ⟨hs.1, hs.2.2⟩

section OriginalOracle
variable {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
include hV hlo hup

/-- Actual standalone main mean. No supplied SizeBound, normalized Lipschitz,
child, descendant, rank, mesh or dimension certificate enters this endpoint. -/
theorem main_mean_stable {Nr : ℕ} (hNr : 0 < Nr) (i : Slot P) (clock : ClockLaw.Clock)
    (hpay : 4*Real.sqrt (Nr:ℝ)*P.delta^(1-P.t) ≤ 1) :
    let E := mainData P hR hc hsmall Nr i clock
    ChildStable E.program E.coefficient (gradient V) (2*P.delta) := by
  have hC1 : 1 ≤ P.Csch := by linarith
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hsmall hC hy).1
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC hy
  have hg := geometry_exact P hR
  have hcost : 10*P.t*(precisionRank (1/4) (P.K:ℝ):ℝ) ≤ 1/2 :=
    (P.rank_budget hc hsmall).le.trans (by norm_num)
  exact certified_source_childStable (source P hR) (anchors P hR) (seeds P hR) (scale P)
    (gradient V) (oracleConstant P) (normalized_gradient P hV hlo hup) (mainState P Nr i clock) P.Bsize
    (initial_main_size P hK hc hsmall hC hy Nr i clock hpay) (P.m_ge_two hc hsmall hC1)
    (root_positive P i clock).1 (mainState_width_pos P hNr i clock)
    P.Ds_pos P.delta_pos (P.delta_le_one hy0) (P.t_pos hc) (P.t_le hc hsmall)
    (P.w_pos hc).le (P.w_lt_t hc hC1).le (P.Bsize_ge_one hc hsmall hC1 hy0) hg.1 le_rfl
    hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2 hcost hs.2.2.2.2.1
    hg.2.1 hs.2.2.2.2.2.1.2.2.2 hg.2.2

/-- A designated input momentum and full raw tape are shared by the two runs. -/
theorem main_mean_sub_le {Nr : ℕ} (hNr : 0 < Nr) (i : Slot P) (clock : ClockLaw.Clock)
    (hpay : 4*Real.sqrt (Nr:ℝ)*P.delta^(1-P.t) ≤ 1) (momentum x z : Point d)
    (tape : Tape d (mainData P hR hc hsmall Nr i clock).program) :
    let E := mainData P hR hc hsmall Nr i clock
    ‖RetainedMeanFinalBatch.childPoint (run E.program (gradient V)
        ⟨E.coefficient,x,momentum⟩ Env.empty tape) -
      RetainedMeanFinalBatch.childPoint (run E.program (gradient V)
        ⟨E.coefficient,z,momentum⟩ Env.empty tape)‖ ≤ 2*P.delta*‖x-z‖ :=
  childStable_tape _ _ (gradient V) _
    (main_mean_stable P hK hc hsmall hC hy hV hlo hup hNr i clock hpay) momentum x z tape
end OriginalOracle
end Scheduled
end AcceleratedLogConcave.Root.OuterMainStability
