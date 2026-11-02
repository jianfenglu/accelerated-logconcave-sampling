import AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
import AcceleratedLogConcave.Oracle.SourceMeanLayerValue

/-! The final continuation state is extracted from the actual execution tape.
It is not supplied as a premise and does not replace recursive child calls. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram SourceMeanLayer

structure FinalState (C n d : ℕ) (Ξ : Ctx) (τ : Ty)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ) where
  ctx : Ctx
  old : Fin n → Ref ctx .point
  direct : Fin n → Ref ctx .point
  saved : RefMap Ξ ctx
  env : Env d ctx
  tape : Tape d (finish old direct saved)

def finalState (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
    (G : Point d → Point d) (input : Inputs d C) :
    (N : ℕ) → {Γ : Ctx} → (old direct : Fin n → Ref Γ .point) →
      (saved : RefMap Ξ Γ) → (env : Env d Γ) →
      Tape d (iterateThen c p slots e outer designated residual auxiliary finish N
        old direct saved) → FinalState C n d Ξ τ finish
  | 0, Γ, old, direct, saved, env, tape => ⟨Γ,old,direct,saved,env,tape⟩
  | N+1, _, old, direct, saved, env, tape =>
      let Q := fun i => (run (freshChild (p i) (e i) (slots ∘ childSlot c p i)
        (old i) (designated N i) (auxiliary N i)) G input env (tape.1 i)).value
      let Z := fun i => (tape.2.1 i).1
      let X := noisyValues (fun j k => slots (aSlot c p j k))
        (fun j k => slots (residualSlot c p j k)) direct input env Q Z
      finalState c p slots e outer designated residual auxiliary finish G input N
        batchRef (fun j => preserveDirect (direct j))
        (fun r => preserveDirect (saved r))
        (Env.prepend X (Env.prepend Z (Env.prepend Q env))) tape.2.2.2

theorem run_iterateThen_value (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
    (G : Point d → Point d) (input : Inputs d C)
    (N : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point)
    (saved : RefMap Ξ Γ) (env : Env d Γ)
    (tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finish N
      old direct saved)) :
    let state := finalState c p slots e outer designated residual auxiliary finish
      G input N old direct saved env tape
    (run (iterateThen c p slots e outer designated residual auxiliary finish N
      old direct saved) G input env tape).value =
      (run (finish state.old state.direct state.saved) G input state.env state.tape).value := by
  induction N generalizing Γ with
  | zero => rfl
  | succ N ih =>
      dsimp only [iterateThen] at tape ⊢
      rw [run_layerAt]
      exact ih batchRef (fun j => preserveDirect (direct j))
        (fun r => preserveDirect (saved r)) _ _

theorem finalState_saved (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
    (G : Point d → Point d) (input : Inputs d C)
    (N : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point)
    (saved : RefMap Ξ Γ) (env : Env d Γ)
    (tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finish N
      old direct saved))
    (r : Ref Ξ .point) :
    let state := finalState c p slots e outer designated residual auxiliary finish
      G input N old direct saved env tape
    storedPoint state.env (state.saved r) = storedPoint env (saved r) := by
  induction N generalizing Γ with
  | zero => rfl
  | succ N ih =>
      simp only [finalState]
      rw [ih]
      exact stored_preserveDirect env _ _ _ (saved r)

end AcceleratedLogConcave.Oracle.RecursiveMeanContinuation
