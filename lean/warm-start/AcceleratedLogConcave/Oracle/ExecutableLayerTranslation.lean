import AcceleratedLogConcave.Oracle.SourceMeanLayerValue

/-! Full Result composition for one actual source synchronous layer. The
continuation premise is a local interpreter statement on the computed stores,
so it can be discharged by finite iteration induction. -/
namespace AcceleratedLogConcave.Oracle.SourceMeanLayer
open NoisyLayer AffineLowering TapeLowering

/-- Equal full child executions and a translated literal continuation give a
translated layer result with exactly the same full query trace. -/
theorem run_layerAt_translation (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog C (nextCtx n Γ) .point)
    (G : Point d → Point d) (input input' : Inputs d C) (env env' : Env d Γ)
    (tape tape' : Tape d (layerAt c p slots e old direct outer designated residual auxiliary next))
    (outputDelta : Point d)
    (hchildren : ∀ i, run
      (freshChild (p i) (e i) (slots ∘ childSlot c p i) (old i) (designated i) (auxiliary i))
      G input' env' (tape'.1 i) =
      run (freshChild (p i) (e i) (slots ∘ childSlot c p i) (old i) (designated i) (auxiliary i))
      G input env (tape.1 i))
    (htail :
      let children := fun i => run
        (freshChild (p i) (e i) (slots ∘ childSlot c p i) (old i) (designated i) (auxiliary i))
        G input env (tape.1 i)
      let Q : Fin n → Point d := fun i => (children i).value
      let Z : Fin n → Point d := fun i => (tape.2.1 i).1
      let Z' : Fin n → Point d := fun i => (tape'.2.1 i).1
      let result := run next G input
        (Env.prepend (noisyValues (fun j k => slots (aSlot c p j k))
          (fun j k => slots (residualSlot c p j k)) direct input env Q Z)
          (Env.prepend Z (Env.prepend Q env))) tape.2.2.2
      run next G input'
        (Env.prepend (noisyValues (fun j k => slots (aSlot c p j k))
          (fun j k => slots (residualSlot c p j k)) direct input' env' Q Z')
          (Env.prepend Z' (Env.prepend Q env'))) tape'.2.2.2 =
        ⟨(show Point d from result.value) + outputDelta,result.trace⟩) :
    run (layerAt c p slots e old direct outer designated residual auxiliary next)
      G input' env' tape' =
    let result := run (layerAt c p slots e old direct outer designated residual auxiliary next)
      G input env tape
    ⟨(show Point d from result.value) + outputDelta,result.trace⟩ := by
  have ha := run_layerAt c p slots e old direct outer designated residual auxiliary next G input' env' tape'
  have hb := run_layerAt c p slots e old direct outer designated residual auxiliary next G input env tape
  dsimp only at ha hb htail ⊢
  simp only [hchildren] at ha
  rw [ha,hb,htail]

end AcceleratedLogConcave.Oracle.SourceMeanLayer
