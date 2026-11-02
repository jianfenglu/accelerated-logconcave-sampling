import AcceleratedLogConcave.Oracle.NonterminalMeanBlock
import AcceleratedLogConcave.Oracle.RecursiveMeanFinalState
import AcceleratedLogConcave.Oracle.RetainedMeanFinalValue

noncomputable section
namespace AcceleratedLogConcave.Oracle.NonterminalMeanBlock
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram
open RecursiveMeanContinuation RetainedMeanFinalBatch
open scoped BigOperators

/-- End-to-end value uses the actual recursively extracted terminal store/tape.
It retains original inputs, executes every final supplier, and assumes no law. -/
theorem run_code_value (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
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
    (N : ℕ)
    (sigma : ℝ) (omega width : Fin m → ℝ)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (htable : input.coefficient ∘ correctionSlots =
      RetainedMeanCorrection.table sigma omega width)
    (tape : Tape d (code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designated direct active initialOrigin outer mainDesignated residual
      auxiliary finalOuter finalAuxiliary N)) :
    let finish := fun {Δ : Ctx} (old _ : Fin n → Ref Δ .point) (saved : RefMap Γ Δ) =>
      paidCorrection cf pf ef finalSlots correctionSlots (saved P)
        (fun i => old (active i)) (fun i => saved (designated i)) finalOuter finalAuxiliary
    let Z : Fin n → Point d := fun i => (tape.1 i).1
    let initialEnv : Env d (replyCtx n (replyCtx n Γ)) := Env.prepend
      (fun j => storedPoint env (direct j) + input.coefficient rhoSlot • Z j)
      (Env.prepend Z env)
    let state := finalState c p mainSlots e outer mainDesignated residual auxiliary
      finish G input N batchRef
      (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
      (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)) initialEnv tape.2.2
    let children := fun i => run
      (designatedChild (pf i) (ef i) (finalSlots i) (state.old (active i))
        (state.saved (designated i)) (finalAuxiliary i)) G input state.env (state.tape.1 i)
    (run (code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designated direct active initialOrigin outer mainDesignated residual
      auxiliary finalOuter finalAuxiliary N) G input env tape).value =
      sigma • storedPoint env P + ∑ i, omega i •
        (childPoint (children i) - width i • storedPoint env (designated i)) := by
  dsimp only
  dsimp only [code] at tape ⊢
  rw [run_initialize, run_iterateThen_value]
  erw [run_paidCorrection cf pf ef finalSlots correctionSlots _ _ _
    finalOuter finalAuxiliary sigma omega width G input _ htable]
  simp only [pointResult, finalState_saved]
  let Z : Fin n → Point d := fun i => (tape.1 i).1
  let X : Fin n → Point d := fun j =>
    storedPoint env (direct j) + input.coefficient rhoSlot • Z j
  have hs (r : Ref Γ .point) :
      storedPoint (Env.prepend X (Env.prepend Z env))
        (RefMap.shiftMany n (RefMap.shiftMany n r)) = storedPoint env r :=
    (prepend_shiftMany X (Env.prepend Z env) (RefMap.shiftMany n r)).trans
      (prepend_shiftMany Z env r)
  dsimp only [X, Z] at hs
  simp only [hs]
  all_goals rfl

end AcceleratedLogConcave.Oracle.NonterminalMeanBlock
