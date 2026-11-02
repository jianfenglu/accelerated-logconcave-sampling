import AcceleratedLogConcave.Oracle.NoisyLayer
import AcceleratedLogConcave.Oracle.RetainedMeanCorrection

/-!
Paid active-final batch. Designated P_i are existing retained references from
the local input assembly. Unlike freshChild, these calls do not draw new P_i.
They draw their own auxiliary tapes and execute every child, even when its
shift is zero. The original parent P survives until the source correction.
-/
namespace AcceleratedLogConcave.Oracle.RetainedMeanFinalBatch
open AffineLowering TapeLowering NoisyLayer
open scoped BigOperators

def designatedChild (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (slots : Fin (N*N+c) → Fin c') (center P : Ref Γ .point)
    (auxiliary : Fin N → Origin) : Prog c' Γ .point :=
  (compileWith p e auxiliary).embed slots center P


/-- Every-tape execution retains the exact designated input already in store. -/
theorem run_designatedChild (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (slots : Fin (N*N+c) → Fin c') (center P : Ref Γ .point)
    (auxiliary : Fin N → Origin) (T : Fin N → Fin N → ℝ) (coeff : Fin c → ℝ)
    (G : Point d → Point d) (input : Inputs d c') (env : Env d Γ)
    (htable : input.coefficient ∘ slots = matrixTable T coeff)
    (tape : Tape d (designatedChild p e slots center P auxiliary)) :
    let restored := restoreTape slots (compileWith p e auxiliary) (fun r => nomatch r)
      center P tape
    let data := unpackCompiledTape p e auxiliary restored
    let source := run p G ⟨coeff,storedPoint env center,storedPoint env P⟩ Env.empty
      (transformedSourceTape p e T data.1 data.2)
    run (designatedChild p e slots center P auxiliary) G input env tape =
      ⟨source.value, List.ofFn (fun j => Event.gaussian (auxiliary j)) ++
        source.trace.filter keepNonGaussian⟩ := by
  dsimp only [designatedChild] at tape ⊢
  rw [run_embed_every_tape]
  simp only [htable]
  exact run_compileWith_every_tape p e auxiliary T coeff
    (storedPoint env center) (storedPoint env P) G _

theorem syntaxCount_designatedChild (kind : EventKind) (p : Program c .point)
    (e : GaussianSlot p ≃ Fin N) (slots : Fin (N*N+c) → Fin c')
    (center P : Ref Γ .point) (auxiliary : Fin N → Origin) :
    syntaxCount kind (designatedChild p e slots center P auxiliary) =
      if kind = .gaussian then N else syntaxCount kind p := by
  simp [designatedChild, Program.embed, syntaxCount_lower, syntaxCount_compileWith]

/-- The final cached arithmetic is reindexed, never evaluated by an opaque
closure. The dummy center/momentum supplied to lower are not read by that code. -/
def paidCorrection (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (e : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (slots : ∀ i, Fin (childSize (pf i)) → Fin c)
    (correctionSlots : Fin (1+(m+m)) → Fin c)
    (P : Ref Γ .point) (center designated : Fin m → Ref Γ .point)
    (outer : Origin)
    (auxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin) :
    Prog c Γ .point :=
  .batch outer (fun i => designatedChild (pf i) (e i) (slots i)
      (center i) (designated i) (auxiliary i))
    ((RetainedMeanCorrection.code (RefMap.shiftMany m P) batchRef
      (fun i => RefMap.shiftMany m (designated i))).lower correctionSlots
        (fun r => r) (RefMap.shiftMany m P) (RefMap.shiftMany m P))

/-- Exact original-gradient work includes every active-final child occurrence. -/
theorem queries_paidCorrection (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (e : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (slots : ∀ i, Fin (childSize (pf i)) → Fin c)
    (correctionSlots : Fin (1+(m+m)) → Fin c)
    (P : Ref Γ .point) (center designated : Fin m → Ref Γ .point)
    (outer : Origin)
    (auxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin) :
    syntaxCount .gradient (paidCorrection cf pf e slots correctionSlots P center designated
      outer auxiliary) = ∑ i, syntaxCount .gradient (pf i) := by
  simp [paidCorrection, syntaxCount, syntaxCount_designatedChild, syntaxCount_lower,
    RetainedMeanCorrection.syntaxCount_code, Fin.sum_ofFn]

end AcceleratedLogConcave.Oracle.RetainedMeanFinalBatch
