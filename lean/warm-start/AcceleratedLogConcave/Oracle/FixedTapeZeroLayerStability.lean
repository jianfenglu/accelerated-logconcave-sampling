import AcceleratedLogConcave.Oracle.FixedTapeMainReadout

/-! The actual initialized zero-layer mean block needs only paid-final child IHs.
Its main syntax, slot maps and origins remain arbitrary; no main-row estimate is used. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.FixedTapeStability
open TapeLowering AffineLowering NoisyLayer RecursiveMeanProgram
open RecursiveMeanContinuation SourceMeanLayer RetainedMeanFinalBatch
open scoped BigOperators
variable {d n m C : ℕ} {Γ : Ctx}

theorem code_zero_sub_le (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (mainSlots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (ef : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (finalSlots : ∀ i, Fin (childSize (pf i)) → Fin C)
    (correctionSlots : Fin (1+(m+m)) → Fin C) (rhoSlot : Fin C)
    (P : Ref Γ .point) (designatedFinal : Fin m → Ref Γ .point)
    (direct : Fin n → Ref Γ .point) (active : Fin m → Fin n)
    (initialOrigin : Fin n → Origin) (outer : ℕ → Origin)
    (mainDesignated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finalOuter : Origin)
    (finalAuxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin)
    (Tf : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeffF : ∀ i, Fin (cf i) → ℝ)
    (σ : ℝ) (w width : Fin m → ℝ)
    (G : Point d → Point d) (input : Inputs d C) (κ B : ℝ)
    (hκ : 0 ≤ κ) (hB0 : 0 ≤ B)
    (htableF : ∀ i, input.coefficient ∘ finalSlots i = matrixTable (Tf i) (coeffF i))
    (hchildF : ∀ i, ChildStable (pf i) (coeffF i) G κ)
    (hcorrection : input.coefficient ∘ correctionSlots = RetainedMeanCorrection.table σ w width)
    (hweights : ∑ i, |w i| ≤ 1)
    (env env' : Env d Γ)
    (hP : storedPoint env P = storedPoint env' P)
    (hdesignated : ∀ i, storedPoint env (designatedFinal i) = storedPoint env' (designatedFinal i))
    (hB : ∀ i, ‖storedPoint env (direct i)-storedPoint env' (direct i)‖ ≤ B)
    (tape : Tape d (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary 0)) :
    ‖childPoint (run (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary 0) G input env tape) -
      childPoint (run (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary 0) G input env' tape)‖ ≤ κ*B := by
  let Z : Fin n → Point d := fun i => (tape.1 i).1
  let X := fun i => storedPoint env (direct i)+input.coefficient rhoSlot • Z i
  let X' := fun i => storedPoint env' (direct i)+input.coefficient rhoSlot • Z i
  let ρ : Env d (replyCtx n (replyCtx n Γ)) := Env.prepend X (Env.prepend Z env)
  let ρ' : Env d (replyCtx n (replyCtx n Γ)) := Env.prepend X' (Env.prepend Z env')
  have hs (r : Ref Γ .point) :
      storedPoint ρ (RefMap.shiftMany n (RefMap.shiftMany n r)) = storedPoint env r := by
    exact (prepend_shiftMany X (Env.prepend Z env) (RefMap.shiftMany n r)).trans
      (prepend_shiftMany Z env r)
  have hs' (r : Ref Γ .point) :
      storedPoint ρ' (RefMap.shiftMany n (RefMap.shiftMany n r)) = storedPoint env' r := by
    exact (prepend_shiftMany X' (Env.prepend Z env') (RefMap.shiftMany n r)).trans
      (prepend_shiftMany Z env' r)
  have hf := paidCorrection_sub_le cf pf ef finalSlots correctionSlots
    (RefMap.shiftMany n (RefMap.shiftMany n P)) (fun i => batchRef (active i))
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (designatedFinal i)))
    finalOuter finalAuxiliary Tf coeffF σ w width G input ρ ρ' htableF hcorrection
    κ B hκ hB0 hchildF hweights (by rw [hs,hs']; exact hP)
    (fun i => by rw [hs,hs']; exact hdesignated i)
    (fun i => by simpa only [ρ,ρ',prepend_batchRef,X,X',add_sub_add_right_eq_sub] using hB (active i))
    tape.2.2
  dsimp only [NonterminalMeanBlock.code] at tape ⊢
  rw [run_initialize,run_initialize]
  exact hf

end AcceleratedLogConcave.Oracle.FixedTapeStability
