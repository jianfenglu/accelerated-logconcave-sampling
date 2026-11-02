import AcceleratedLogConcave.Oracle.RetainedMeanFinalBatch

/-! Packaged every-tape retained final-output semantics. ResidualTape is not
assumed Gaussian: all uniform and unit coordinates remain in each child tape. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.RetainedMeanFinalBatch
open AffineLowering TapeLowering NoisyLayer
open scoped BigOperators

/-- Typed point readout prevents dependent Ty.denote projections escaping elaboration. -/
def childPoint (result : Result d .point) : Point d := result.value

private theorem run_lower_every_tape (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (G : Point d → Point d) (input : Inputs d c') (env : Env d Γ)
    (center momentum : Ref Γ .point)
    (tape : Tape d (p.lower κ (fun r => r) center momentum)) :
    run (p.lower κ (fun r => r) center momentum) G input env tape =
      run p G ⟨input.coefficient ∘ κ, env center, env momentum⟩ env
        (restoreTape κ p (fun r => r) center momentum tape) := by
  calc
    _ = run (p.lower κ (fun r => r) center momentum) G input env
        (lowerTape κ p (fun r => r) center momentum
          (restoreTape κ p (fun r => r) center momentum tape)) :=
      congrArg (fun z => run (p.lower κ (fun r => r) center momentum) G input env z)
        (lowerTape_restoreTape κ p (fun r => r) center momentum tape).symm
    _ = _ := run_lower κ p G _ input (fun r => r) center momentum env env _
      (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- The actual batch result, including all paid child traces and the original
parent/designated inputs. No probability law or desired accuracy is assumed. -/
theorem run_paidCorrection (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (e : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (slots : ∀ i, Fin (childSize (pf i)) → Fin c)
    (correctionSlots : Fin (1+(m+m)) → Fin c)
    (P : Ref Γ .point) (center designated : Fin m → Ref Γ .point)
    (outer : Origin)
    (auxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin)
    (sigma : ℝ) (omega width : Fin m → ℝ)
    (G : Point d → Point d) (input : Inputs d c) (env : Env d Γ)
    (htable : input.coefficient ∘ correctionSlots =
      RetainedMeanCorrection.table sigma omega width)
    (tape : Tape d (paidCorrection cf pf e slots correctionSlots P center designated
      outer auxiliary)) :
    let children := fun i => run
      (designatedChild (pf i) (e i) (slots i) (center i) (designated i) (auxiliary i))
      G input env (tape.1 i)
    run (paidCorrection cf pf e slots correctionSlots P center designated outer auxiliary)
      G input env tape =
      pointResult (sigma • storedPoint env P + ∑ i, omega i •
        (childPoint (children i) - width i • storedPoint env (designated i)))
        (((List.ofFn fun i => (children i).trace).flatten).map
          (Event.withPrefix outer)) := by
  dsimp only
  dsimp only [paidCorrection] at tape ⊢
  simp only [run]
  rw [run_lower_every_tape]
  simp only [htable]
  erw [RetainedMeanCorrection.run_code]
  let Q : Fin m → Point d := fun i => childPoint
    (run (designatedChild (pf i) (e i) (slots i) (center i) (designated i) (auxiliary i))
      G input env (tape.1 i))
  have hp (r : Ref Γ .point) :
      storedPoint (Env.prepend Q env) (RefMap.shiftMany m r) = storedPoint env r :=
    prepend_shiftMany Q env r
  have hq (i : Fin m) : storedPoint (Env.prepend Q env) (batchRef i) = Q i :=
    prepend_batchRef Q env i
  dsimp only [Q, childPoint] at hp hq
  simp only [pointResult, List.append_nil, hp, hq, childPoint]

end AcceleratedLogConcave.Oracle.RetainedMeanFinalBatch
