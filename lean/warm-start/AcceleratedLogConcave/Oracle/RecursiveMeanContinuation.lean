import AcceleratedLogConcave.Oracle.RecursiveMeanProgram
import AcceleratedLogConcave.Oracle.SourceMeanLayer

/-!
Continuation-preserving synchronous loop. Unlike iterateCode, it keeps every
final center available for the paid active-final child batch. An explicit
saved reference map retains the original parent P and designated final inputs
through every iteration, without storing them inside a numerical direct row. This is not yet
a complete precision-indexed family: the literal source continuation and its
public coefficient reindexing must still be supplied by that construction.
-/
namespace AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram SourceMeanLayer
open scoped BigOperators

/-- All centers and direct rows remain stored until the final continuation. -/
def iterateThen (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ) :
    (N : ℕ) → {Γ : Ctx} → (Fin n → Ref Γ .point) →
      (Fin n → Ref Γ .point) → RefMap Ξ Γ → Prog C Γ τ
  | 0, _, old, direct, saved => finish old direct saved
  | N+1, _, old, direct, saved =>
      layerAt c p slots e old direct (outer N) (designated N) (residual N) (auxiliary N)
        (iterateThen c p slots e outer designated residual auxiliary finish N
          (fun j => batchRef j) (fun j => preserveDirect (direct j))
          (fun r => preserveDirect (saved r)))

/-- Compositional inventory: a concrete final continuation pays its full cost.
The premise is only its local syntax inventory, not the desired recursive bound,
accuracy, or any probabilistic property. No final supplier is erased. -/
theorem syntaxCount_iterateThen (kind : EventKind)
    (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
    (finalCount : ℕ)
    (hfinish : ∀ {Δ : Ctx} (old direct : Fin n → Ref Δ .point) (saved : RefMap Ξ Δ),
      syntaxCount kind (finish old direct saved) = finalCount)
    (N : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) :
    syntaxCount kind (iterateThen c p slots e outer designated residual auxiliary finish N old direct saved) =
      N * layerInventory kind c p + finalCount := by
  induction N generalizing Γ with
  | zero => simpa [iterateThen] using hfinish old direct saved
  | succ N ih =>
      rw [iterateThen, syntaxCount_layerAt, ih]
      change layerInventory kind c p + (N * layerInventory kind c p + finalCount) = _
      simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm]

end AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
