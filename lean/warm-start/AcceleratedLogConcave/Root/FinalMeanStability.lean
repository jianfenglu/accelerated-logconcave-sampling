import AcceleratedLogConcave.Root.FinalMeanScheduledData
import AcceleratedLogConcave.Oracle.RecursiveCertifiedSamplingStability

/-! Original-data deterministic final-mean stability for the prescribed physical
resolution. The only analytic premises concern the raw potential V, with unit
Hessian upper bound. All root and descendant certificates are derived. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.FinalMeanStability
open Oracle Oracle.CubicExecutableWorkShift Oracle.CubicScheduleThreshold
open Oracle.RecursiveCall Oracle.RecursiveSize Oracle.FixedTapeStability Oracle.Precision
open FinalMeanScheduledData
open scoped BigOperators NNReal
variable (P : SourceSchedule)

def privateData (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (p : State) : ExecutableData :=
  (source P hR).privateSampler (anchors P hR) (seeds P hR) (P.t_pos hc)
    (step_quarter P hc hsmall) (scale P) p

section Scheduled
variable (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
  (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y)
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC hy
local notation "C" => source P hR

/-- Actual endpoint rows and radius smallness, with no supplied root certificate. -/
theorem reachable_rows (i : Slot P) (clock : ClockLaw.Clock) {p : State} {depth cost : ℕ}
    (hp : Path C (state P i clock) p depth cost) :
    (∀ j : (source P hR).M.MeanNode, 2*P.delta*(∑ u, |(source P hR).M.matrix p.radius p.width j u|) ≤
      P.delta^((1:ℝ)/3)) ∧ 2*P.delta*p.radius^2 ≤ P.delta^((1:ℝ)/3) := by
  have hC1 : 1 ≤ P.Csch := by linarith
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hsmall hC hy).1
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC hy
  have hg := geometry_exact P hR
  have hpos := root_positive P i clock
  have hcost : 10*P.t*(precisionRank (1/4) (P.K:ℝ):ℝ) ≤ 1/2 :=
    (P.rank_budget hc hsmall).le.trans (by norm_num)
  exact hp.actual_rows_small P.delta P.Bsize
    (initial_size P hK hc hsmall hC hy i clock) (P.m_ge_two hc hsmall hC1) P.delta_pos.le
    hpos.1 hpos.2 P.Ds_pos P.delta_pos (P.delta_le_one hy0)
    (P.t_pos hc) (P.t_le hc hsmall) (P.w_pos hc).le (P.w_lt_t hc hC1).le
    (P.Bsize_ge_one hc hsmall hC1 hy0) hg.1 le_rfl
    hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2 hcost hs.2.2.2.2.1
    hg.2.1 hs.2.2.2.2.2.1.2.2.2 hg.2.2

section OriginalOracle
variable {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
include hV hlo hup

/-- Every actual mean endpoint inherits 2h stability from original V. -/
theorem reachable_mean_stable (i : Slot P) (clock : ClockLaw.Clock) {p : State} {depth cost : ℕ}
    (hp : Path C (state P i clock) p depth cost) :
    let E := data P hR hc hsmall (scale P) p.radius p.width p.precision
    ChildStable E.program E.coefficient (gradient V) (2*P.delta) := by
  have hC1 : 1 ≤ P.Csch := by linarith
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hsmall hC hy).1
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC hy
  have hg := geometry_exact P hR
  have hpos := root_positive P i clock
  have hcost : 10*P.t*(precisionRank (1/4) (P.K:ℝ):ℝ) ≤ 1/2 :=
    (P.rank_budget hc hsmall).le.trans (by norm_num)
  exact Path.certified_childStable C (anchors P hR) (seeds P hR) (scale P)
    (gradient V) (oracleConstant P) (normalized_gradient P hV hlo hup) (state P i clock) P.Bsize
    (initial_size P hK hc hsmall hC hy i clock) (P.m_ge_two hc hsmall hC1)
    hpos.1 hpos.2 P.Ds_pos P.delta_pos (P.delta_le_one hy0)
    (P.t_pos hc) (P.t_le hc hsmall) (P.w_pos hc).le (P.w_lt_t hc hC1).le
    (P.Bsize_ge_one hc hsmall hC1 hy0) hg.1 le_rfl
    hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2 hcost hs.2.2.2.2.1
    hg.2.1 hs.2.2.2.2.2.1.2.2.2 hg.2.2 hp

/-- Actual designated outer final slot, not the internal active-final child. -/
theorem final_mean_stable (i : Slot P) (clock : ClockLaw.Clock) :
    let E := finalData P hR hc hsmall i clock
    ChildStable E.program E.coefficient (gradient V) (2*P.delta) :=
  reachable_mean_stable P hK hc hsmall hC hy hV hlo hup i clock (RecursiveCall.Path.refl _)

/-- The literal reachable private sampling block retains q-1/4 mean children. -/
theorem reachable_private_stable (i : Slot P) (clock : ClockLaw.Clock) {p : State} {depth cost : ℕ}
    (hp : Path C (state P i clock) p depth cost) (hq : 1/2 < p.precision) :
    ChildStable (privateData P hR hc hsmall p).program
      (privateData P hR hc hsmall p).coefficient (gradient V) (5*p.radius*P.delta) := by
  have hC1 : 1 ≤ P.Csch := by linarith
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hsmall hC hy).1
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC hy
  have hg := geometry_exact P hR
  have hpos := root_positive P i clock
  have hcost : 10*P.t*(precisionRank (1/4) (P.K:ℝ):ℝ) ≤ 1/2 :=
    (P.rank_budget hc hsmall).le.trans (by norm_num)
  exact Path.certified_privateSampler_childStable C (anchors P hR) (seeds P hR) (scale P)
    (gradient V) (oracleConstant P) (normalized_gradient P hV hlo hup) (state P i clock) P.Bsize
    (initial_size P hK hc hsmall hC hy i clock) (P.m_ge_two hc hsmall hC1)
    hpos.1 hpos.2 P.Ds_pos P.delta_pos (P.delta_le_one hy0)
    (P.t_pos hc) (P.t_le hc hsmall) (P.w_pos hc).le (P.w_lt_t hc hC1).le
    (P.Bsize_ge_one hc hsmall hC1 hy0) hg.1 le_rfl
    hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2 hcost hs.2.2.2.2.1
    hg.2.1 hs.2.2.2.2.2.1.2.2.2 hg.2.2 hp hq

/-- Same entering momentum and complete raw tape; only stored output points. -/
theorem final_mean_sub_le (i : Slot P) (clock : ClockLaw.Clock) (momentum x z : Point d)
    (tape : Tape d (finalData P hR hc hsmall i clock).program) :
    let E := finalData P hR hc hsmall i clock
    ‖RetainedMeanFinalBatch.childPoint (run E.program (gradient V)
        ⟨E.coefficient,x,momentum⟩ Env.empty tape) -
      RetainedMeanFinalBatch.childPoint (run E.program (gradient V)
        ⟨E.coefficient,z,momentum⟩ Env.empty tape)‖ ≤ 2*P.delta*‖x-z‖ :=
  childStable_tape _ _ (gradient V) _
    (final_mean_stable P hK hc hsmall hC hy hV hlo hup i clock) momentum x z tape

theorem reachable_private_sub_le (i : Slot P) (clock : ClockLaw.Clock) {p : State} {depth cost : ℕ}
    (hp : Path C (state P i clock) p depth cost) (hq : 1/2 < p.precision)
    (momentum x z : Point d) (tape : Tape d (privateData P hR hc hsmall p).program) :
    let E := privateData P hR hc hsmall p
    ‖RetainedMeanFinalBatch.childPoint (run E.program (gradient V)
        ⟨E.coefficient,x,momentum⟩ Env.empty tape) -
      RetainedMeanFinalBatch.childPoint (run E.program (gradient V)
        ⟨E.coefficient,z,momentum⟩ Env.empty tape)‖ ≤ (5*p.radius*P.delta)*‖x-z‖ :=
  childStable_tape _ _ (gradient V) _
    (reachable_private_stable P hK hc hsmall hC hy hV hlo hup i clock hp hq) momentum x z tape
end OriginalOracle
end Scheduled
end AcceleratedLogConcave.Root.FinalMeanStability
