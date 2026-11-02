import AcceleratedLogConcave.Oracle.NoisyLayer

/-!
The existing noisy layer inside a larger source public table. Reindexing applies
only to its coefficient reads, not to its continuation, so the continuation may
read independent final-child and retained-correction table regions. Every child
and random occurrence of NoisyLayer.noisyLayer is retained.
-/
namespace AcceleratedLogConcave.Oracle.SourceMeanLayer
open NoisyLayer AffineLowering TapeLowering
open scoped BigOperators

def layerAt (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog C (nextCtx n Γ) τ) : Prog C Γ τ :=
  .batch outer (fun i => freshChild (p i) (e i) (slots ∘ childSlot c p i)
    (old i) (designated i) (auxiliary i))
    (.batch [] (fun i => residualDraw (residual i))
      (.batch [] (noisyRow (fun j k => slots (aSlot c p j k))
        (fun j k => slots (residualSlot c p j k)) direct) next))

/-- The larger table changes no event counts and drops no zero-weight child. -/
theorem syntaxCount_layerAt (kind : EventKind) (c : Fin n → ℕ)
    (p : ∀ i, Program (c i) .point) (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog C (nextCtx n Γ) τ) :
    syntaxCount kind (layerAt c p slots e old direct outer designated residual auxiliary next) =
      (if kind = .gaussian then n + (∑ i, (tapeShape (p i)).gaussianBlocks) + n
        else ∑ i, syntaxCount kind (p i)) + syntaxCount kind next := by
  have hchild (i : Fin n) := syntaxCount_freshChild kind (p i) (e i)
    (slots ∘ childSlot c p i) (old i) (designated i) (auxiliary i)
  simp only [layerAt, syntaxCount, hchild, Fin.sum_ofFn]
  cases kind <;> simp [syntaxCount, syntaxCount_noisyRow, residualDraw,
    instructionCount, Instr.eventKind, Finset.sum_add_distrib, Nat.add_assoc]

/-- Identity routing recovers the existing layer definition exactly. -/
theorem layerAt_id (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog (publicSize c p) (nextCtx n Γ) τ) :
    layerAt c p (fun j => j) e old direct outer designated residual auxiliary next =
      noisyLayer c p e old direct outer designated residual auxiliary next := rfl

end AcceleratedLogConcave.Oracle.SourceMeanLayer
