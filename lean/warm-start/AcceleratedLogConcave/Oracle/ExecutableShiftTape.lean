import AcceleratedLogConcave.Oracle.ExecutableShiftWeights

/-! Full tape identities joining actual structural Gaussian weights to the
source compiler's existing raw auxiliary translation. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.ExecutableShiftWeights
open TapeLowering AffineLowering NoisyLayer LayerShift

@[simp] theorem translate_zero (p : Prog c Γ τ) (r : ℝ) (Δ : Point d) (tape : Tape d p) :
    translate p (fun _ => 0) r Δ tape = tape := by
  induction p with
  | ret a => rfl
  | step origin instr next ih =>
      cases instr <;> simp only [translate,translateInstr,zero_div,zero_smul,ih]
      all_goals first
        | rfl
        | exact congrArg (fun z : Point d => (z,tape.2)) (add_zero (show Point d from tape.1))
  | batch origin children next ihc ihn =>
      simp only [translate,ihc,ihn]
      rfl

/-- The actual compiler's structural weights translate precisely its raw batch;
its complete residual replay tape is unchanged. -/
theorem translate_packCompiledTape (p : Program c τ) (e : GaussianSlot p ≃ Fin N)
    (auxiliary : Fin N → Origin) (w : Fin N → ℝ) (r : ℝ) (Δ : Point d)
    (data : (Fin N → Point d) × ResidualTape p) :
    translate (compileWith p e auxiliary) (compiledWeights p e auxiliary w) r Δ
      (packCompiledTape p e auxiliary data) =
    packCompiledTape p e auxiliary (shiftAux w r Δ data.1,data.2) := by
  simp only [compileWith,packCompiledTape,translate,translateInstr,compiledWeights,
    rawDraw,shiftAux]
  erw [translate_zero]
  simp only [translate_zero]
  rfl

/-- Slot translation of a fresh child is exactly the existing raw auxiliary
translation, on every actual execution tape. -/
theorem translate_freshWeights (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (slots : Fin (N*N+c) → Fin C) (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin)
    (w : Fin N → ℝ) (r : ℝ) (Δ : Point d)
    (tape : Tape d (freshChild p e slots old designated auxiliary)) :
    translate (freshChild p e slots old designated auxiliary)
      (freshWeights p e slots old designated auxiliary w) r Δ tape =
    shiftFreshTape p e slots old designated auxiliary w r Δ tape := by
  let t := freshChildTapeEquiv (d := d) p e slots old designated auxiliary
  have ts (a : Point d × ((Fin N → Point d) × ResidualTape p)) :
      t.symm a = (a.1,lowerTape slots (compileWith p e auxiliary)
        (fun s => nomatch s) (.there old) .here (packCompiledTape p e auxiliary a.2)) := rfl
  have h (a : Point d × ((Fin N → Point d) × ResidualTape p)) :
      translate (freshChild p e slots old designated auxiliary)
        (freshWeights p e slots old designated auxiliary w) r Δ (t.symm a) =
      t.symm (a.1,shiftAux w r Δ a.2.1,a.2.2) := by
    rw [ts,ts]
    change (a.1 + (0/r) • Δ, translate ((compileWith p e auxiliary).embed slots (.there old) .here)
      (lowerWeights slots (compileWith p e auxiliary) (fun s => nomatch s)
        (.there old) .here (compiledWeights p e auxiliary w)) r Δ
      (lowerTape slots (compileWith p e auxiliary) (fun s => nomatch s)
        (.there old) .here (packCompiledTape p e auxiliary a.2))) =
      (a.1,lowerTape slots (compileWith p e auxiliary) (fun s => nomatch s)
        (.there old) .here
        (packCompiledTape p e auxiliary (shiftAux w r Δ a.2.1,a.2.2)))
    rw [zero_div,zero_smul,add_zero]
    congr 1
    unfold Program.embed
    erw [← lowerTape_translate,translate_packCompiledTape]
    rfl
  calc
    _ = translate (freshChild p e slots old designated auxiliary)
        (freshWeights p e slots old designated auxiliary w) r Δ (t.symm (t tape)) :=
      congrArg (translate (freshChild p e slots old designated auxiliary)
        (freshWeights p e slots old designated auxiliary w) r Δ) (t.symm_apply_apply tape).symm
    _ = t.symm ((t tape).1,shiftAux w r Δ (t tape).2.1,(t tape).2.2) := h (t tape)
    _ = _ := rfl

end AcceleratedLogConcave.Oracle.ExecutableShiftWeights
