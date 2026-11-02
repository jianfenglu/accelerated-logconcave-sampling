import AcceleratedLogConcave.Oracle.MeanChronologicalFinish
import AcceleratedLogConcave.Oracle.MeanFinalBatchCoupling

/-! Exact identification of the reached mean-final continuation and the
canonical designated final occurrence. The equality follows along every
executed cursor advance; no final-cut equality is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.TailOccurrenceCut.TailCut
open TapeLowering

theorem trans_assoc {c : ℕ} {Γ Δ Ξ Ω : Ctx} {τ σ υ η : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} {r : Prog c Ξ υ} {s : Prog c Ω η}
    (inner : TailCut s r) (middle : TailCut r q) (outer : TailCut q p) :
    trans inner (trans middle outer)=trans (trans inner middle) outer := by
  induction outer with
  | here => rfl
  | step o a next cut ih => exact congrArg (TailCut.step o a next) ih
  | batch o cs next cut ih => exact congrArg (TailCut.batch o cs next) ih

theorem trans_here {c : ℕ} {Γ Δ : Ctx} {τ σ : Ty} {p : Prog c Γ τ} {q : Prog c Δ σ}
    (cut : TailCut q p) : trans .here cut=cut := by
  induction cut with
  | here => rfl
  | step o a next cut ih => exact congrArg (TailCut.step o a next) ih
  | batch o cs next cut ih => exact congrArg (TailCut.batch o cs next) ih
end AcceleratedLogConcave.Oracle.TailOccurrenceCut.TailCut

namespace AcceleratedLogConcave.Oracle.MeanChronologicalFinalAlignment
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling
variable {m n a h : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)

/-- The final occurrence reached by finishing the actual remaining loop. -/
def atCursor (s : Cursor M nodes anchors seeds main final sampling N) :
    FinishFocus (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling)
      (Host M nodes anchors seeds main final sampling N) :=
  let f := atFinish (fun i => (main i).size) (fun i => (main i).program)
    (mainSlot (a := a) main final sampling) (fun i => (main i).enumeration)
    layerOrigin mainDesignated residualOrigin (mainAuxiliary main)
    (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling)
    s.remaining s.old s.direct s.saved
  ⟨f.ctx,f.old,f.direct,f.saved,TailCut.trans f.cut s.cut⟩

/-- Consuming exactly the actual child, residual and row batches leaves the
same complete final occurrence inside the unchanged original host. -/
theorem atCursor_advance (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) :
    atCursor M nodes anchors seeds main final sampling N
      (advance M nodes anchors seeds main final sampling N s hs)=
        atCursor M nodes anchors seeds main final sampling N s := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      dsimp only [atCursor,advance,focus,afterLayer,afterBatch,atFinish]
      simp only [TailCut.trans_assoc]
      rfl

theorem atCursor_stage (k : ℕ) (hk : k≤N) :
    atCursor M nodes anchors seeds main final sampling N
      (stage M nodes anchors seeds main final sampling N k hk).1=
        atCursor M nodes anchors seeds main final sampling N (entry M nodes anchors seeds main final sampling N) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [stage,atCursor_advance]
    exact ih (by omega)

/-- The literal reached final focus, before the original paid final batch. -/
def terminalFocus :
    FinishFocus (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling)
      (Host M nodes anchors seeds main final sampling N) :=
  ⟨(terminalCursor M nodes anchors seeds main final sampling N).ctx,
    (terminalCursor M nodes anchors seeds main final sampling N).old,
    (terminalCursor M nodes anchors seeds main final sampling N).direct,
    (terminalCursor M nodes anchors seeds main final sampling N).saved,
    terminalCut M nodes anchors seeds main final sampling N⟩

theorem atCursor_zero (s : Cursor M nodes anchors seeds main final sampling N) (hz : s.remaining=0) :
    atCursor M nodes anchors seeds main final sampling N s=
      ⟨s.ctx,s.old,s.direct,s.saved,MeanChronologicalFinish.zeroCut M nodes anchors seeds main final sampling N s hz⟩ := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => simp only [atCursor,atFinish,TailCut.trans_here]; rfl
    | succ remaining => exact False.elim (Nat.succ_ne_zero remaining hz)

theorem atCursor_entry :
    atCursor M nodes anchors seeds main final sampling N (entry M nodes anchors seeds main final sampling N)=
      MeanFinalBatchCoupling.finishFocus M nodes anchors seeds main final sampling N := by
  dsimp only [atCursor,entry,MeanInitialComparison.entryCut,afterBatch,MeanFinalBatchCoupling.finishFocus]
  simp only [TailCut.trans_assoc]
  rfl

/-- Exact full typed focus equality, including the original syntax-tail cut.
Thus its stored Pi and all same final tapes are those in the final API. -/
theorem terminalFocus_eq : terminalFocus M nodes anchors seeds main final sampling N=
    MeanFinalBatchCoupling.finishFocus M nodes anchors seeds main final sampling N := by
  calc
    terminalFocus M nodes anchors seeds main final sampling N=
        atCursor M nodes anchors seeds main final sampling N (terminalCursor M nodes anchors seeds main final sampling N) :=
      (atCursor_zero M nodes anchors seeds main final sampling N _ (terminal_remaining M nodes anchors seeds main final sampling N)).symm
    _=atCursor M nodes anchors seeds main final sampling N (entry M nodes anchors seeds main final sampling N) :=
      atCursor_stage M nodes anchors seeds main final sampling N N le_rfl
    _=_ := atCursor_entry M nodes anchors seeds main final sampling N
end AcceleratedLogConcave.Oracle.MeanChronologicalFinalAlignment
