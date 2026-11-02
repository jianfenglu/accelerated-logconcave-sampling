import AcceleratedLogConcave.Oracle.ExecutableWorkCardinality
import AcceleratedLogConcave.Oracle.CubicSchedulePayments

/-! Actual query-plus-Gaussian work and whole-run QueryShift under the fixed
cubic schedule. No analytic regularity, size certificate, tape law or new
recursion is introduced. Anchor/seed slots are the genuine finite geometry. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.CubicExecutableWorkShift
open Numerics.AffineGraph TapeLowering ChildAbsorption CovarianceSetup
open ScalarSchedulePayment CubicScheduleThreshold ExecutableWorkCardinality
variable (P : SourceSchedule)

/-- Exact inherited producer, including its fixed node and private-node equivalences. -/
def source (hR : P.R ≤ 1/2) : RecursiveCall.Source P.m (n P hR) (ns P hR) :=
  PrescribedSourceGeometry.source P.m P.R P.h0 P.R_pos hR P.h0_pos P.Ds P.delta P.t P.w P.NP

def anchorCount (hR : P.R ≤ 1/2) : ℕ := Fintype.card (source P hR).M.Anchor
def seedCount (hR : P.R ≤ 1/2) : ℕ := Fintype.card (Fin P.m × (source P hR).M.Kernel)
def anchors (hR : P.R ≤ 1/2) : Fin (anchorCount P hR) ≃ (source P hR).M.Anchor := (Fintype.equivFin _).symm
def seeds (hR : P.R ≤ 1/2) : Fin (seedCount P hR) ≃ Fin P.m × (source P hR).M.Kernel := (Fintype.equivFin _).symm

theorem source_parameters (hR : P.R ≤ 1/2) :
    let C := source P hR
    C.Ds = P.Ds ∧ C.δ = P.delta ∧ C.t = P.t ∧ C.w = P.w ∧ C.layers = P.NP ∧
    C.M.R = P.R ∧ C.M.psi = P.R^4 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem step_quarter (hc : 0 < P.csch) (hsmall : P.csch < 1/160) : P.t ≤ 1/4 := by
  have := P.t_le hc hsmall
  linarith

/-- Existing executable constructor and its existing complete Gaussian enumeration. -/
def data (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (scale r σ q : ℝ) : ExecutableData :=
  let C := source P hR
  RecursiveExecutable.mean C.M C.nodes (anchors P hR) (seeds P hR) C.Ds C.δ C.t C.w
    (P.t_pos hc) (step_quarter P hc hsmall) C.layers C.mesh C.snodes scale r σ q

theorem data_terminal (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (scale r σ q : ℝ) (hq : q ≤ 1/2) :
    data P hR hc hsmall scale r σ q = RecursiveExecutable.terminal scale r σ :=
  RecursiveExecutable.mean_terminal (source P hR).M (source P hR).nodes (anchors P hR) (seeds P hR)
    (source P hR).S (source P hR).snodes P.Ds P.delta P.t P.w (P.t_pos hc) (step_quarter P hc hsmall)
    P.NP scale r σ q hq

theorem producer_cardinality (hR : P.R ≤ 1/2) :
    P.m ≤ n P hR ∧ seedCount P hR = P.m*(Fintype.card ((source P hR).M.backward.Source P.m)+1) ∧
    seedCount P hR ≤ n P hR :=
  source_cardinality (source P hR).M (source P hR).nodes (seeds P hR)

theorem branching_le_D (hR : P.R ≤ 1/2) :
    (RecursiveExecutable.fullBranching P.NP (n P hR) (ns P hR) P.m (seedCount P hR):ℝ) ≤ D P hR := by
  exact fullBranching_le_source (source P hR).M (source P hR).nodes (seeds P hR) P.NP (ns P hR)

theorem D_ge_two (hR : P.R ≤ 1/2) : 2 ≤ D P hR := sourceShiftBase_ge_two P.NP (I P hR)

section Paid
variable (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
  (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y)
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC hy

/-- Both terminal instructions are included, for every oracle, input and exact tape. -/
theorem executed_work {d : ℕ} (scale r σ q : ℝ) (hqK : q ≤ (P.K:ℝ))
    (oracle : Point d → Point d)
    (input : Inputs d (data P hR hc hsmall scale r σ q).size)
    (tape : Tape d (data P hR hc hsmall scale r σ q).program) :
    let counts := traceCounts (run (data P hR hc hsmall scale r σ q).program oracle input Env.empty tape).trace
    ((counts.queries+counts.gaussianBlocks:ℕ):ℝ) ≤ (D P hR)^(G P) ∧
    ((counts.queries+counts.gaussianBlocks:ℕ):ℝ) ≤ Real.exp (P.y/64) := by
  let C := source P hR
  have hwork := RecursiveExecutable.executed_full_work_mean_le C.M C.nodes (anchors P hR) (seeds P hR)
    C.Ds C.δ C.t C.w C.layers (P.t_pos hc) (step_quarter P hc hsmall) C.mesh C.snodes
    scale r σ q oracle input tape
  have hrank := Precision.precisionRank_mono (P.t_pos hc) hqK
  have hcap := rho_add_one_le_G P hc (by linarith : 1 ≤ P.Csch)
  have hpow := absorb_leading_two (D_ge_two P hR) (branching_le_D P hR)
    (show Precision.precisionRank P.t q+1 ≤ G P by change Precision.precisionRank P.t (P.K:ℝ)+1 ≤ G P at hcap; omega)
  have hworkR : ((traceCounts (run (data P hR hc hsmall scale r σ q).program oracle input Env.empty tape).trace).queries+
      (traceCounts (run (data P hR hc hsmall scale r σ q).program oracle input Env.empty tape).trace).gaussianBlocks:ℕ) ≤
      2*RecursiveExecutable.fullBranching P.NP (n P hR) (ns P hR) P.m (seedCount P hR)^Precision.precisionRank P.t q := hwork
  have hpaid := (CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC hy).2.1
  have hfinal := (show (((traceCounts (run (data P hR hc hsmall scale r σ q).program oracle input Env.empty tape).trace).queries+
      (traceCounts (run (data P hR hc hsmall scale r σ q).program oracle input Env.empty tape).trace).gaussianBlocks:ℕ):ℝ) ≤
      ((2*RecursiveExecutable.fullBranching P.NP (n P hR) (ns P hR) P.m (seedCount P hR)^Precision.precisionRank P.t q:ℕ):ℝ) by exact_mod_cast hworkR).trans hpow
  exact ⟨hfinal, hfinal.trans hpaid⟩

/-- The source support budget now pays the actual shift base. This is a
sum-of-squared-coordinate budget, not a tape law or an accuracy statement. -/
theorem actual_shift_budget :
    RecursiveExecutable.shiftBase P.NP (n P hR) (ns P hR)^Precision.precisionRank (1/4) (P.K:ℝ) ≤ P.Ds^2 := by
  have hp := (CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC hy).2.2.2.1
  exact RecursiveExecutable.source_shift_budget (inventory := I P hR) (Hs := P.Hs)
    (by rfl) (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC) hp

/-- Actual whole-run equality with the constructor's fixed enumeration. The
same entering momentum and residual tape are retained by QueryShift. -/
theorem queryShift_and_mass (scale r σ q : ℝ) (hr : 0 < r) (hqK : q ≤ (P.K:ℝ)) :
    let E := data P hR hc hsmall scale r σ q
    QueryShift E.program E.enumeration E.coefficient r E.shiftVector ∧
    shiftSq E.shiftVector ≤ RecursiveExecutable.shiftBase P.NP (n P hR) (ns P hR)^Precision.precisionRank (1/4) q ∧
    shiftSq E.shiftVector ≤ P.Ds^2 := by
  let C := source P hR
  have hp := (CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC hy).2.2.2.1
  have hs := RecursiveExecutable.source_mean_queryShift_and_mass C.M C.nodes (anchors P hR) (seeds P hR)
    C.mesh C.snodes C.Ds C.δ C.t C.w C.layers (P.t_pos hc) (step_quarter P hc hsmall)
    (P.K:ℝ) scale P.Ds_pos (by exact le_rfl) (I P hR) P.Hs (by rfl)
    (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC) hp r σ q hr hqK
  have hmono := Precision.precisionRank_mono (by norm_num : (0:ℝ)<1/4) hqK
  have hbase := RecursiveExecutable.shiftBase_ge_one P.NP (n P hR) (ns P hR)
  have hb := (pow_le_pow_right₀ hbase hmono).trans (actual_shift_budget P hK hc hsmall hC hy)
  exact ⟨hs.1, hs.2, hs.2.trans hb⟩
end Paid
end AcceleratedLogConcave.Oracle.CubicExecutableWorkShift
