import AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
import AcceleratedLogConcave.Oracle.RetainedMeanFinalBatch

/-!
Source-facing finite local join: paid initialization, all main synchronous
layers, all designated active-final children, and the retained-input correction.
The private anchor and Gaussian input assembly must already have been executed
into the incoming store. Children and their shifts remain supplied here; this
is not yet the precision-indexed recursive constructor.
-/
namespace AcceleratedLogConcave.Oracle.NonterminalMeanBlock
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram
open RecursiveMeanContinuation RetainedMeanFinalBatch
open scoped BigOperators

/-- Exact stored source inputs survive initialization and the complete loop. -/
def code (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (mainSlots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (ef : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (finalSlots : ∀ i, Fin (childSize (pf i)) → Fin C)
    (correctionSlots : Fin (1+(m+m)) → Fin C) (rhoSlot : Fin C)
    (P : Ref Γ .point) (designated : Fin m → Ref Γ .point)
    (direct : Fin n → Ref Γ .point) (active : Fin m → Fin n)
    (initialOrigin : Fin n → Origin) (outer : ℕ → Origin)
    (mainDesignated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finalOuter : Origin)
    (finalAuxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin)
    (N : ℕ) : Prog C Γ .point :=
  initializeCenters rhoSlot direct [] initialOrigin
    (iterateThen c p mainSlots e outer mainDesignated residual auxiliary
      (fun old _ saved => paidCorrection cf pf ef finalSlots correctionSlots
        (saved P) (fun i => old (active i)) (fun i => saved (designated i))
        finalOuter finalAuxiliary)
      N batchRef
      (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
      (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)))

/-- Exact work identity pays initialization (zero gradient calls), every main
supplier occurrence, and every active-final supplier. No assumed parent bound. -/
theorem queries_code (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (mainSlots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (ef : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (finalSlots : ∀ i, Fin (childSize (pf i)) → Fin C)
    (correctionSlots : Fin (1+(m+m)) → Fin C) (rhoSlot : Fin C)
    (P : Ref Γ .point) (designated : Fin m → Ref Γ .point)
    (direct : Fin n → Ref Γ .point) (active : Fin m → Fin n)
    (initialOrigin : Fin n → Origin) (outer : ℕ → Origin)
    (mainDesignated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finalOuter : Origin)
    (finalAuxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin)
    (N : ℕ) :
    syntaxCount .gradient (code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designated direct active initialOrigin outer mainDesignated residual
      auxiliary finalOuter finalAuxiliary N) =
      N * (∑ i, syntaxCount .gradient (p i)) + ∑ i, syntaxCount .gradient (pf i) := by
  unfold code
  rw [syntaxCount_initialize]
  simp only [show EventKind.gradient ≠ EventKind.gaussian from by decide, ite_false, zero_add]
  apply syntaxCount_iterateThen
  intro Δ old direct saved
  exact queries_paidCorrection cf pf ef finalSlots correctionSlots
    (saved P) (fun i => old (active i)) (fun i => saved (designated i))
    finalOuter finalAuxiliary

end AcceleratedLogConcave.Oracle.NonterminalMeanBlock
