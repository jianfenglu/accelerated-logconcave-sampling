import AcceleratedLogConcave.Oracle.SourceMeanLayer

namespace AcceleratedLogConcave.Oracle.SourceMeanLayer
open NoisyLayer AffineLowering TapeLowering
open scoped BigOperators

theorem run_layerAt (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog C (nextCtx n Γ) τ)
    (G : Point d → Point d) (input : Inputs d C) (ρ : Env d Γ)
    (ω : Tape d (layerAt c p slots e old direct outer designated residual auxiliary next)) :
    let children := fun i => run
      (freshChild (p i) (e i) (slots ∘ childSlot c p i) (old i) (designated i) (auxiliary i))
      G input ρ (ω.1 i)
    let Q : Fin n → Point d := fun i => (children i).value
    let Z : Fin n → Point d := fun j => (ω.2.1 j).1
    let tail := run next G input
      (Env.prepend (noisyValues (fun j k => slots (aSlot c p j k)) (fun j k => slots (residualSlot c p j k)) direct input ρ Q Z)
        (Env.prepend Z (Env.prepend Q ρ))) ω.2.2.2
    run (layerAt c p slots e old direct outer designated residual auxiliary next) G input ρ ω =
      ⟨tail.value, ((List.ofFn (fun j => (children j).trace)).flatten ++
        List.ofFn (fun j => Event.gaussian (residual j)) ++ tail.trace).map
          (Event.withPrefix outer)⟩ := by
  change (let children := fun i => run
                             (freshChild (p i) (e i) (slots ∘ childSlot c p i) (old i)
                               (designated i) (auxiliary i)) G input ρ (ω.1 i)
          let tail := run (finishLayer (fun j k => slots (aSlot c p j k)) (fun j k => slots (residualSlot c p j k)) direct residual next)
                        G input (Env.prepend (fun i => (children i).value) ρ) ω.2
          (⟨tail.value, ((List.ofFn (fun i => (children i).trace)).flatten ++ tail.trace).map
            (Event.withPrefix outer)⟩ : Result d τ)) = _
  dsimp only
  have h := run_finishLayer (fun j k => slots (aSlot c p j k)) (fun j k => slots (residualSlot c p j k)) direct residual next G input ρ
    (fun i => (run (freshChild (p i) (e i) (slots ∘ childSlot c p i) (old i)
      (designated i) (auxiliary i)) G input ρ (ω.1 i)).value) ω.2
  erw [h]
  simp only [List.append_assoc]

end AcceleratedLogConcave.Oracle.SourceMeanLayer
