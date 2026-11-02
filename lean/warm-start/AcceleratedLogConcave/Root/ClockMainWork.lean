import AcceleratedLogConcave.Root.ClockMainWorkBounds
import AcceleratedLogConcave.Root.ClockRepeatedLayers

/-! Every-execution query plus Gaussian-block work of the actual main component.
This is not the complete manuscript chronology: active-final input assembly,
fresh final calls and retained correction are outside this component. Its input
center is already normalized, and its clock is fixed (no uniform clock draw).
The program, table, enumerations and child family are inherited unchanged. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockMainWork
open Oracle Oracle.CubicScheduleThreshold Oracle.RecursiveMeanContinuation Oracle.RecursiveMeanProgram
open ClockNoisyLayer ClockRepeatedLayers
open scoped BigOperators

/-- A tape witness only for transferring an every-execution count bound to
syntax; no execution or probability law is defined by this existence proof. -/
private theorem tape_nonempty {c d : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) : Nonempty (Tape d p) := by
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

variable (P : SourceSchedule)

section Exact
variable (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock)
local notation "p₀" => p P hR hc hsmall clock
local notation "C₀" => ClockPublicSetup.size P hR hc hsmall clock

/-- Complete component count, with explicit continuation overhead. -/
theorem executed_work_eq {d : ℕ} {τ : Ty} (ell D : ℕ)
    (finish : Finish P hR hc hsmall clock τ) (fq fg : ℕ)
    (hq : ∀ {Δ : Ctx} (old direct : Index P → Ref Δ .point) (saved : RefMap (entryCtx P) Δ),
      syntaxCount .gradient (finish old direct saved) = fq)
    (hg : ∀ {Δ : Ctx} (old direct : Index P → Ref Δ .point) (saved : RefMap (entryCtx P) Δ),
      syntaxCount .gaussian (finish old direct saved) = fg)
    (oracle : Point d → Point d) (input : Inputs d C₀)
    (tape : Tape d (code P hR hc hsmall clock ell D finish)) :
    let counts := traceCounts (run (code P hR hc hsmall clock ell D finish) oracle input Env.empty tape).trace
    counts.queries+counts.gaussianBlocks =
      1+N P+D*(2*N P+∑ i,bookkeepingWork (p₀ i))+fq+fg := by
  have hqc := executed_counts P hR hc hsmall clock ell D finish .gradient fq hq oracle input tape
  have hgc := executed_counts P hR hc hsmall clock ell D finish .gaussian fg hg oracle input tape
  change shapeCount .gradient _+shapeCount .gaussian _ = _
  rw [hqc,hgc]
  simp only [layerInventory, reduceCtorEq, ite_false, ite_true, Nat.zero_add]
  simp only [bookkeepingWork, syntaxCounts, Finset.sum_add_distrib]
  have he : (∑ i,syntaxCount .gaussian (p₀ i)) = ∑ i,g P hR hc hsmall clock i := by
    apply Finset.sum_congr rfl
    intro i _
    exact gaussianCount_eq_tapeShape (p₀ i)
  rw [he]
  ring

theorem saved_work_eq {d : ℕ} (ell D : ℕ) (r : Ref (entryCtx P) .point)
    (oracle : Point d → Point d) (input : Inputs d C₀)
    (tape : Tape d (code P hR hc hsmall clock ell D (finishSaved P hR hc hsmall clock r))) :
    let counts := traceCounts (run (code P hR hc hsmall clock ell D (finishSaved P hR hc hsmall clock r)) oracle input Env.empty tape).trace
    counts.queries+counts.gaussianBlocks = 1+N P+D*(2*N P+∑ i,bookkeepingWork (p₀ i)) := by
  simpa only [Nat.add_zero] using executed_work_eq P hR hc hsmall clock ell D
    (finishSaved P hR hc hsmall clock r) 0 0 (fun _ _ _ => rfl) (fun _ _ _ => rfl) oracle input tape
end Exact

section Scheduled
variable (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
  (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y) (clock : ClockLaw.Clock)
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC hy
local notation "p₀" => p P hR hc hsmall clock
local notation "C₀" => ClockPublicSetup.size P hR hc hsmall clock

/-- Specializes the existing actual standalone main-mean work supplier. -/
theorem child_executed_work {d : ℕ} (i : Index P) (oracle : Point d → Point d)
    (input : Inputs d (c P hR hc hsmall clock i)) (tape : Tape d (p₀ i)) :
    let counts := traceCounts (run (p₀ i) oracle input Env.empty tape).trace
    ((counts.queries+counts.gaussianBlocks:ℕ):ℝ) ≤ Real.exp (P.y/64) :=
  OuterMainStability.main_work P hK hc hsmall hC hy (N P) i clock oracle input tape

/-- Syntax equals every execution; no new child-work premise is accepted. -/
theorem child_work (i : Index P) : (bookkeepingWork (p₀ i):ℝ) ≤ Real.exp (P.y/64) := by
  have h := child_executed_work P hK hc hsmall hC hy clock i
    (fun _ : Point 0 => 0) ⟨fun _ => 0,0,0⟩ (Classical.choice (tape_nonempty (p₀ i)))
  dsimp only at h
  rw [run_counts] at h
  exact h

theorem child_sum_work : ((∑ i,bookkeepingWork (p₀ i):ℕ):ℝ) ≤ (N P:ℝ)*Real.exp (P.y/64) := by
  push_cast
  calc
    ∑ i,(bookkeepingWork (p₀ i):ℝ) ≤ ∑ _i : Index P,Real.exp (P.y/64) :=
      Finset.sum_le_sum (fun i _ => child_work P hK hc hsmall hC hy clock i)
    _ = _ := by simp [Index]

/-- Every target raw tape is covered; a generic finish pays its own query/block cost. -/
theorem component_work_with_finish {d : ℕ} {τ : Ty} (ell : ℕ)
    (finish : Finish P hR hc hsmall clock τ) (fq fg : ℕ)
    (hq : ∀ {Δ : Ctx} (old direct : Index P → Ref Δ .point) (saved : RefMap (entryCtx P) Δ),
      syntaxCount .gradient (finish old direct saved) = fq)
    (hg : ∀ {Δ : Ctx} (old direct : Index P → Ref Δ .point) (saved : RefMap (entryCtx P) Δ),
      syntaxCount .gaussian (finish old direct saved) = fg)
    (oracle : Point d → Point d) (input : Inputs d C₀)
    (tape : Tape d (prescribed P hR hc hsmall clock ell finish)) :
    let counts := traceCounts (run (prescribed P hR hc hsmall clock ell finish) oracle input Env.empty tape).trace
    ((counts.queries+counts.gaussianBlocks:ℕ):ℝ) ≤ Real.exp (P.y/32)+(fq:ℝ)+(fg:ℝ) := by
  dsimp only [prescribed]
  rw [executed_work_eq P hR hc hsmall clock ell (P.K+4) finish fq fg hq hg oracle input tape]
  push_cast
  have h := ClockMainWorkBounds.cubic_payment P hK hc hsmall hC hy
    (child_sum_work P hK hc hsmall hC hy clock)
  simp only [ClockCollocation.count, Nat.cast_mul, Nat.cast_sum] at h
  linarith

/-- Zero-event saved-value finish: complete actual main-component work <= exp(y/32).
This excludes fresh final calls, uniform cost and all arithmetic/bit costs. -/
theorem component_work {d : ℕ} (ell : ℕ) (r : Ref (entryCtx P) .point)
    (oracle : Point d → Point d) (input : Inputs d C₀)
    (tape : Tape d (prescribed P hR hc hsmall clock ell (finishSaved P hR hc hsmall clock r))) :
    let counts := traceCounts (run (prescribed P hR hc hsmall clock ell (finishSaved P hR hc hsmall clock r)) oracle input Env.empty tape).trace
    ((counts.queries+counts.gaussianBlocks:ℕ):ℝ) ≤ Real.exp (P.y/32) := by
  simpa only [Nat.cast_zero,add_zero] using component_work_with_finish P hK hc hsmall hC hy clock ell
    (finishSaved P hR hc hsmall clock r) 0 0 (fun _ _ _ => rfl) (fun _ _ _ => rfl) oracle input tape
end Scheduled
end AcceleratedLogConcave.Root.ClockMainWork
