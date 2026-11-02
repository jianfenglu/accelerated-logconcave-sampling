import AcceleratedLogConcave.Oracle.NoisyLayer
import AcceleratedLogConcave.Oracle.TerminalMean

/-!
Finite synchronous iteration of actual child programs. This is the operational
loop needed by the recursive mean compiler, not the complete source compiler.
All child calls use freshChild and all replies are stored before any row update.
Direct rows survive every layer. The children may themselves be compiled loops.
No Gibbs primitive occurs in this module. No claim about conditional Gaussian
laws, accuracy, source ranks, or source-selected public parameters is made.
-/
namespace AcceleratedLogConcave.Oracle.RecursiveMeanProgram
open AffineLowering TapeLowering NoisyLayer
open scoped BigOperators

/-- Preserve old references past replies, residual draws, and updated rows. -/
def preserveDirect : RefMap Γ (nextCtx n Γ) :=
  fun r => RefMap.shiftMany n (RefMap.shiftMany n (RefMap.shiftMany n r))

/-- Direct data is not recomputed or overwritten by a layer. -/
theorem stored_preserveDirect (env : Env d Γ) (Q Z X : Fin n → Point d)
    (r : Ref Γ .point) :
    storedPoint (Env.prepend X (Env.prepend Z (Env.prepend Q env)))
      (preserveDirect r) = storedPoint env r := by
  exact (prepend_shiftMany X (Env.prepend Z (Env.prepend Q env))
    (RefMap.shiftMany n (RefMap.shiftMany n r))).trans
      ((prepend_shiftMany Z (Env.prepend Q env) (RefMap.shiftMany n r)).trans
        (prepend_shiftMany Q env r))

/-- Execute exactly N synchronous layers, returning one requested stored node.
The arbitrary initial store is intentional: free-state setup and the final mean
row belong to the enclosing compiler and are not hidden as free oracle inputs. -/
def iterateCode (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (selected : Fin n) : (N : ℕ) → {Γ : Ctx} →
      (Fin n → Ref Γ .point) → (Fin n → Ref Γ .point) →
      Prog (publicSize c p) Γ .point
  | 0, _, old, _ => .ret (old selected)
  | N+1, _, old, direct =>
      noisyLayer c p e old direct (outer N) (designated N) (residual N) (auxiliary N)
        (iterateCode c p e outer designated residual auxiliary selected N
          (fun j => batchRef j) (fun j => preserveDirect (direct j)))

/-- The per-layer inventory includes every child and both fresh Gaussian blocks;
zero coefficients and unused child replies receive no discount. -/
def layerInventory (kind : EventKind) (c : Fin n → ℕ)
    (p : ∀ i, Program (c i) .point) : ℕ :=
  if kind = .gaussian then n + (∑ i, (tapeShape (p i)).gaussianBlocks) + n
  else ∑ i, syntaxCount kind (p i)

 theorem syntaxCount_iterateCode (kind : EventKind)
    (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (selected : Fin n) (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) :
    syntaxCount kind (iterateCode c p e outer designated residual auxiliary selected N old direct) =
      N * layerInventory kind c p := by
  induction N generalizing Γ with
  | zero => simp [iterateCode, syntaxCount]
  | succ N ih =>
      rw [iterateCode, syntaxCount_noisyLayer, ih]
      change layerInventory kind c p + N * layerInventory kind c p = _
      simp [Nat.succ_mul, Nat.add_comm]

/-- Deterministic, every-tape original-gradient cost of the actual loop. -/
theorem executed_queries (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (selected : Fin n) (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point)
    (G : Point d → Point d) (input : Inputs d (publicSize c p)) (env : Env d Γ)
    (tape : Tape d (iterateCode c p e outer designated residual auxiliary selected N old direct)) :
    (traceCounts (run (iterateCode c p e outer designated residual auxiliary selected N old direct)
      G input env tape).trace).queries = N * ∑ i, queryCount (p i) := by
  rw [run_counts]
  change syntaxCount .gradient _ = _
  rw [syntaxCount_iterateCode]
  rfl

/-- Work induction consumes only child syntax budgets, never an accuracy event. -/
theorem queryCount_le (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (selected : Fin n) (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (budget : Fin n → ℕ)
    (hchild : ∀ i, queryCount (p i) ≤ budget i) :
    queryCount (iterateCode c p e outer designated residual auxiliary selected N old direct) ≤
      N * ∑ i, budget i := by
  change syntaxCount .gradient _ ≤ _
  rw [syntaxCount_iterateCode]
  change N * (∑ i, queryCount (p i)) ≤ _
  exact Nat.mul_le_mul_left N (Finset.sum_le_sum (fun i _ => hchild i))

/-- Explicit one-layer interpreter correspondence. The next recursive call reads
exactly the newly stored rows, not an externally supplied numerical iterate. -/
theorem run_iterateCode_succ (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (selected : Fin n) (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point)
    (G : Point d → Point d) (input : Inputs d (publicSize c p)) (env : Env d Γ)
    (tape : Tape d (iterateCode c p e outer designated residual auxiliary selected (N+1) old direct)) :
    let children := fun i => run
      (freshChild (p i) (e i) (childSlot c p i) (old i) (designated N i) (auxiliary N i))
      G input env (tape.1 i)
    let Q := fun i => (children i).value
    let Z := fun i => (tape.2.1 i).1
    let env' : Env d (nextCtx n Γ) := Env.prepend (noisyValues (aSlot c p) (residualSlot c p) direct input env Q Z)
      (Env.prepend Z (Env.prepend Q env))
    let tail := run (iterateCode c p e outer designated residual auxiliary selected N
      (fun j => batchRef j) (fun j => preserveDirect (direct j))) G input env' tape.2.2.2
    run (iterateCode c p e outer designated residual auxiliary selected (N+1) old direct)
      G input env tape =
      ⟨tail.value, ((List.ofFn (fun i => (children i).trace)).flatten ++
        List.ofFn (fun i => Event.gaussian (residual N i)) ++ tail.trace).map
          (Event.withPrefix (outer N))⟩ :=
  run_noisyLayer c p e old direct (outer N) (designated N) (residual N) (auxiliary N)
    _ G input env tape

end AcceleratedLogConcave.Oracle.RecursiveMeanProgram
