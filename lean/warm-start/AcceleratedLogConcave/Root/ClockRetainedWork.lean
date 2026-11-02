import AcceleratedLogConcave.Root.ClockRetainedFinalSplice
import AcceleratedLogConcave.Root.ClockMainWork
import AcceleratedLogConcave.Kinetic.SourceDimensionPhaseCount
import AcceleratedLogConcave.Numerics.SourceWorkResolution

/-! Every-tape query and Gaussian-block work of the literal retained final
splice, including the public prefix, initial centers, all main layers, every
fresh final child and the algebraic correction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace AcceleratedLogConcave.Root.ClockRetainedWork
open Oracle Oracle.CubicScheduleThreshold Oracle.RecursiveMeanProgram
open ClockRetainedFinalSplice ClockNoisyLayer ClockRepeatedLayers
open scoped BigOperators

private theorem tape_nonempty {c d : ℕ} {Γ : Ctx} {τ : Ty}
    (p : Prog c Γ τ) : Nonempty (Tape d p) := by
  induction p with
  | ret r => exact ⟨PUnit.unit⟩
  | step origin instr next ih =>
    have hi : Nonempty (instr.Tape d) := by
      cases instr with
      | gaussian => exact ⟨(0 : Point d)⟩
      | uniform => exact ⟨⟨0, by constructor <;> norm_num⟩⟩
      | _ => exact ⟨PUnit.unit⟩
    exact ⟨Classical.choice hi, Classical.choice ih⟩
  | batch origin children next ihChildren ihNext =>
    exact ⟨fun j => Classical.choice (ihChildren j), Classical.choice ihNext⟩

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock)

/-- Exact full-root count on every raw tape. The final child summand counts
even zero-weight nodes. -/
theorem executed_work_eq {d : ℕ} (ell : ℕ) (oracle : Point d → Point d)
    (input : Inputs d (size P hR hc hsmall clock))
    (tape : Tape d (code P hR hc hsmall clock ell)) :
    let counts := traceCounts
      (run (code P hR hc hsmall clock ell) oracle input Env.empty tape).trace
    counts.queries + counts.gaussianBlocks =
      1 + 2*N P + (P.K+4) *
        (2*N P + ∑ i, bookkeepingWork (p P hR hc hsmall clock i)) +
        ∑ i, bookkeepingWork (pf P hR hc hsmall clock i) := by
  have hq := executed_count P hR hc hsmall clock ell .gradient oracle input tape
  have hg := executed_count P hR hc hsmall clock ell .gaussian oracle input tape
  change shapeCount .gradient _ + shapeCount .gaussian _ = _
  rw [hq, hg]
  simp only [layerInventory, reduceCtorEq, ite_false, ite_true, Nat.zero_add]
  simp only [bookkeepingWork, syntaxCounts, Finset.sum_add_distrib]
  have hm : (∑ i,syntaxCount .gaussian (p P hR hc hsmall clock i)) =
      ∑ i,g P hR hc hsmall clock i := by
    apply Finset.sum_congr rfl
    intro i _
    exact gaussianCount_eq_tapeShape (p P hR hc hsmall clock i)
  have hf : (∑ i,syntaxCount .gaussian (pf P hR hc hsmall clock i)) =
      ∑ i,gf P hR hc hsmall clock i := by
    apply Finset.sum_congr rfl
    intro i _
    exact gaussianCount_eq_tapeShape (pf P hR hc hsmall clock i)
  rw [hm,hf]
  ring

section Scheduled
variable (hK : 10 ≤ P.K) (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y)
local notation "hRs" => CubicSchedulePayments.radius_guard P hK hc hsmall hC hy

/-- A fresh final call has the same source work cap as an internal call. -/
theorem final_child_work (i : Index P) :
    (bookkeepingWork (pf P hRs hc hsmall clock i):ℝ) ≤ Real.exp (P.y/64) := by
  have h := FinalMeanScheduledData.final_work P hK hc hsmall hC hy i clock
    (fun _ : Point 0 => 0) ⟨fun _ => 0,0,0⟩
    (Classical.choice (tape_nonempty (pf P hRs hc hsmall clock i)))
  dsimp only at h
  rw [run_counts] at h
  exact h

theorem final_sum_work :
    ((∑ i,bookkeepingWork (pf P hRs hc hsmall clock i):ℕ):ℝ) ≤
      (N P:ℝ)*Real.exp (P.y/64) := by
  push_cast
  calc
    ∑ i,(bookkeepingWork (pf P hRs hc hsmall clock i):ℝ) ≤
      ∑ _i : Index P, Real.exp (P.y/64) :=
      Finset.sum_le_sum (fun i _ => final_child_work P hc hsmall clock hK hC hy i)
    _ = _ := by simp [Index]

/-- The extra initializer batch and every fresh final child fit within one
additional main-component envelope. -/
theorem final_overhead_payment :
    (N P:ℝ) + ((∑ i,bookkeepingWork (pf P hRs hc hsmall clock i):ℕ):ℝ) ≤
      Real.exp (P.y/32) := by
  have hp := CubicSchedulePayments.prerequisites P hK hc hsmall hC hy
  have hE : 1 ≤ Real.exp (P.y/64) := Real.one_le_exp_iff.mpr (by linarith [hp.1])
  have hN : (N P:ℝ) ≤ 256*((P.K:ℝ)+4)*Real.exp (P.y/128) := by
    exact ClockMainWorkBounds.inventory_upper P hp.1
  have hcoef : 512*((P.K:ℝ)+4) ≤ Oracle.ScalarSchedulePayment.a P := by
    have hpoly : 512*((P.K:ℝ)+4) ≤ 3585*((P.K:ℝ)+2)^2 := by
      have hk : 0 ≤ (P.K:ℝ) := Nat.cast_nonneg _
      nlinarith [sq_nonneg (P.K:ℝ)]
    exact hpoly.trans (ClockMainWorkBounds.coefficient_payment P hc hsmall (by linarith))
  have ha : Oracle.ScalarSchedulePayment.a P ≤ Real.exp (P.y/256) :=
    (Real.log_le_iff_le_exp
      (by linarith [(Oracle.ScalarSchedulePayment.a_lower P hc hsmall (by linarith)).2])).mp
      (ClockMainWorkBounds.log_a_payment P hc hsmall (by linarith) hp.2.1)
  have h2N : 2*(N P:ℝ) ≤ Oracle.ScalarSchedulePayment.a P*Real.exp (P.y/128) := by
    calc
      _ ≤ 512*((P.K:ℝ)+4)*Real.exp (P.y/128) := by linarith [hN]
      _ ≤ Oracle.ScalarSchedulePayment.a P*Real.exp (P.y/128) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
  have hNpay : 2*(N P:ℝ)*Real.exp (P.y/64) ≤ Real.exp (P.y/32) := by
    calc
      _ ≤ (Oracle.ScalarSchedulePayment.a P*Real.exp (P.y/128))*Real.exp (P.y/64) :=
        mul_le_mul_of_nonneg_right h2N (Real.exp_nonneg _)
      _ ≤ (Real.exp (P.y/256)*Real.exp (P.y/128))*Real.exp (P.y/64) := by
        gcongr
      _ = Real.exp (7*P.y/256) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (P.y/32) := Real.exp_le_exp.mpr (by linarith [hp.1])
  have hfinal := final_sum_work P hc hsmall clock hK hC hy
  have hNsmall : (N P:ℝ) ≤ (N P:ℝ)*Real.exp (P.y/64) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (N P)) (sub_nonneg.mpr hE)]
  linarith

/-- Every execution of the exact full retained splice, including all public
and final work, has this query-plus-Gaussian-block cap. -/
theorem executed_full_work_le {d : ℕ} (ell : ℕ) (oracle : Point d → Point d)
    (input : Inputs d (size P hRs hc hsmall clock))
    (tape : Tape d (code P hRs hc hsmall clock ell)) :
    let counts := traceCounts
      (run (code P hRs hc hsmall clock ell) oracle input Env.empty tape).trace
    ((counts.queries+counts.gaussianBlocks:ℕ):ℝ) ≤ 2*Real.exp (P.y/32) := by
  dsimp only
  rw [executed_work_eq P hRs hc hsmall clock ell oracle input tape]
  push_cast
  have hmain := ClockMainWorkBounds.cubic_payment P hK hc hsmall hC hy
    (ClockMainWork.child_sum_work P hK hc hsmall hC hy clock)
  have hextra := final_overhead_payment P hc hsmall clock hK hC hy
  change (1:ℝ)+(N P:ℝ)+((P.K:ℝ)+4)*
    (2*(N P:ℝ)+((∑ i,bookkeepingWork (p P hRs hc hsmall clock i):ℕ):ℝ)) ≤
      Real.exp (P.y/32) at hmain
  push_cast at hmain hextra
  linarith

/-- In particular, every original-gradient query in the literal full code is
paid, with no exceptional tape and no discount for repeated query points. -/
theorem executed_gradient_queries_le {d : ℕ} (ell : ℕ) (oracle : Point d → Point d)
    (input : Inputs d (size P hRs hc hsmall clock))
    (tape : Tape d (code P hRs hc hsmall clock ell)) :
    let counts := traceCounts
      (run (code P hRs hc hsmall clock ell) oracle input Env.empty tape).trace
    (counts.queries:ℝ) ≤ 2*Real.exp (P.y/32) := by
  have h := executed_full_work_le P hc hsmall clock hK hC hy ell oracle input tape
  dsimp only at h ⊢
  exact le_trans (by exact_mod_cast Nat.le_add_right _ _) h

/-- Specialization to the actual original-gradient oracle. The C² assumption
belongs to kernel measurability and accuracy, not the deterministic count. -/
theorem original_gradient_queries_le {d : ℕ} (ell : ℕ) (V : Point d → ℝ)
    (input : Inputs d (size P hRs hc hsmall clock))
    (tape : Tape d (code P hRs hc hsmall clock ell)) :
    let counts := traceCounts
      (run (code P hRs hc hsmall clock ell) (gradient V) input Env.empty tape).trace
    (counts.queries:ℝ) ≤ 2*Real.exp (P.y/32) :=
  executed_gradient_queries_le P hc hsmall clock hK hC hy ell (gradient V) input tape

/-- At the original dimension prescription `y = e log D`, the actual
reference horizon times every-tape full-root gradient calls fits the target
dimension power. This counts one entire literal root execution per phase. -/
theorem dimension_phase_gradient_queries_le {D e θ κ Cw ε η : ℝ}
    (hD : 1 ≤ D) (he : 0 < e) (hθ : 0 < θ) (hκ : 1 ≤ κ)
    (hCw : 0 ≤ Cw) (hε : 0 < ε) (hε4 : ε < 1/4)
    (heη : e ≤ η/3) (hySource : P.y = e*Real.log D)
    {d : ℕ} (ell : ℕ) (oracle : Point d → Point d)
    (input : Inputs d (size P hRs hc hsmall clock))
    (tape : Tape d (code P hRs hc hsmall clock ell)) :
    let steps := AcceleratedLogConcave.Kinetic.referenceHorizon
      (AcceleratedLogConcave.Kinetic.sourceRate θ κ (D ^ (-e)))
      (AcceleratedLogConcave.Kinetic.warmMixingExponent (D ^ Cw) ε)
    let counts := traceCounts
      (run (code P hRs hc hsmall clock ell) oracle input Env.empty tape).trace
    (steps:ℝ)*(counts.queries:ℝ) ≤
      2*AcceleratedLogConcave.Kinetic.sourceDimensionPhaseConstant θ Cw ε e *
        Real.sqrt κ * D ^ η := by
  dsimp only
  have hq := executed_gradient_queries_le P hc hsmall clock hK hC hy ell oracle input tape
  dsimp only at hq
  have hk := AcceleratedLogConcave.Kinetic.source_dimension_horizon_le
    hθ hκ hD he hCw hε hε4
  have hDp : 0 < D := by linarith
  have hexp : Real.exp (P.y/32) ≤ D ^ e := by
    rw [hySource]
    calc
      Real.exp ((e*Real.log D)/32) = D ^ (e/32) := by
        rw [Real.rpow_def_of_pos hDp]
        congr 1
        ring
      _ ≤ D ^ e := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hpow : D ^ (2*e)*D ^ e = D ^ (3*e) := by
    rw [← Real.rpow_add hDp]
    congr 1
    ring
  have hconst := AcceleratedLogConcave.Kinetic.sourceDimensionPhaseConstant_pos
    hθ hCw he hε hε4
  have hη : D ^ (3*e) ≤ D ^ η :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  calc
    _ ≤ (AcceleratedLogConcave.Kinetic.referenceHorizon
        (AcceleratedLogConcave.Kinetic.sourceRate θ κ (D ^ (-e)))
        (AcceleratedLogConcave.Kinetic.warmMixingExponent (D ^ Cw) ε):ℝ) *
        (2*Real.exp (P.y/32)) :=
      mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    _ ≤ (AcceleratedLogConcave.Kinetic.sourceDimensionPhaseConstant θ Cw ε e *
        Real.sqrt κ * D ^ (2*e))*(2*Real.exp (P.y/32)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ ≤ (AcceleratedLogConcave.Kinetic.sourceDimensionPhaseConstant θ Cw ε e *
        Real.sqrt κ * D ^ (2*e))*(2*D ^ e) := by
      apply mul_le_mul_of_nonneg_left (by linarith [hexp])
      positivity
    _ = 2*AcceleratedLogConcave.Kinetic.sourceDimensionPhaseConstant θ Cw ε e *
        Real.sqrt κ * D ^ (3*e) := by
      calc
        _ = (2*AcceleratedLogConcave.Kinetic.sourceDimensionPhaseConstant θ Cw ε e *
            Real.sqrt κ)*(D ^ (2*e)*D ^ e) := by ring
        _ = _ := by rw [hpow]
    _ ≤ 2*AcceleratedLogConcave.Kinetic.sourceDimensionPhaseConstant θ Cw ε e *
        Real.sqrt κ * D ^ η :=
      mul_le_mul_of_nonneg_left hη (by positivity)

end Scheduled

/-- The same budget for the literal four-parameter source schedule, with no
abstract per-call work hypothesis. -/
theorem source_schedule_dimension_phase_gradient_queries_le
    (K : ℕ) (c C D e θ κ Cw ε η : ℝ)
    (hK : 10 ≤ K) (hc : 0 < c) (hsmall : c < 1/160) (hC : 8 ≤ C)
    (hD : 1 ≤ D) (he : 0 < e) (hθ : 0 < θ) (hκ : 1 ≤ κ)
    (hCw : 0 ≤ Cw) (hε : 0 < ε) (hε4 : ε < 1/4)
    (heη : e ≤ η/3) :
    let P := AcceleratedLogConcave.Numerics.SourceWorkResolution.schedule
      K c C (e*Real.log D)
    ∀ (hy : threshold P ≤ P.y) (clock : ClockLaw.Clock),
      let hR := CubicSchedulePayments.radius_guard P hK hc hsmall hC hy
      ∀ {d : ℕ} (ell : ℕ) (oracle : Point d → Point d)
        (input : Inputs d (size P hR hc hsmall clock))
        (tape : Tape d (code P hR hc hsmall clock ell)),
        let steps := AcceleratedLogConcave.Kinetic.referenceHorizon
          (AcceleratedLogConcave.Kinetic.sourceRate θ κ (D ^ (-e)))
          (AcceleratedLogConcave.Kinetic.warmMixingExponent (D ^ Cw) ε)
        let counts := traceCounts
          (run (code P hR hc hsmall clock ell) oracle input Env.empty tape).trace
        (steps:ℝ)*(counts.queries:ℝ) ≤
          2*AcceleratedLogConcave.Kinetic.sourceDimensionPhaseConstant θ Cw ε e *
            Real.sqrt κ * D ^ η := by
  dsimp only
  intro hy clock d ell oracle input tape
  exact dimension_phase_gradient_queries_le
    (AcceleratedLogConcave.Numerics.SourceWorkResolution.schedule K c C (e*Real.log D))
    hc hsmall clock hK hC hy hD he hθ hκ hCw hε hε4 heη rfl ell oracle input tape

end AcceleratedLogConcave.Root.ClockRetainedWork
