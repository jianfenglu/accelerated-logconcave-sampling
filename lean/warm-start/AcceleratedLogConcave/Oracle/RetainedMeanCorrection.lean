import AcceleratedLogConcave.Oracle.AffineLowering

/-!
Literal final correction in warm-start.tex, eq. compiled-mean-correction.
The original supplied P and designated final P_i are retained references.
Only arithmetic is performed here; the enclosing program must execute all
active-final children before using their stored replies. There is no draw of
or access to the comparison coordinate G_E.
-/
noncomputable section
namespace AcceleratedLogConcave.Oracle.RetainedMeanCorrection
open AffineLowering
open scoped BigOperators

/-- Public coefficients: sigma, followed by omega_i and -omega_i sigma_i. -/
def table (sigma : ℝ) (omega width : Fin m → ℝ) : Fin (1+(m+m)) → ℝ :=
  Fin.append (fun _ : Fin 1 => sigma)
    (Fin.append omega (fun i => -(omega i * width i)))

/-- The original momentum enters once, before the cached correction terms. -/
def code (P : Ref Γ .point) (reply designated : Fin m → Ref Γ .point) :
    Prog (1+(m+m)) Γ .point :=
  .step [] (.pure (.publicScalar (Fin.castAdd (m+m) (0 : Fin 1)))) <|
  .step [] (.pure (.smul .here (.there P))) <|
  affineRow [] .here (List.ofFn fun j : Fin (m+m) =>
    (Fin.natAdd 1 j, .there (.there (Fin.append reply designated j))))

/-- Exact source correction with every designated input subtracted, not a
benchmark mean row and not a replacement of child replies by exact means. -/
theorem run_code (sigma : ℝ) (omega width : Fin m → ℝ)
    (P : Ref Γ .point) (reply designated : Fin m → Ref Γ .point)
    (G : Point d → Point d) (hostX hostP : Point d) (env : Env d Γ)
    (tape : Tape d (code P reply designated)) :
    run (code P reply designated) G ⟨table sigma omega width,hostX,hostP⟩ env tape =
      pointResult (sigma • storedPoint env P + ∑ i, omega i •
        (storedPoint env (reply i) - width i • storedPoint env (designated i))) [] := by
  simp only [code, run, evalInstr, evalPure]
  rw [run_affineRow_ofFn]
  simp only [table, Fin.append_left, Fin.append_right]
  change pointResult (sigma • storedPoint env P +
    ∑ j : Fin (m+m), Fin.append omega (fun i => -(omega i * width i)) j •
      storedPoint env (Fin.append reply designated j)) [] = _
  apply congrArg (fun v : Point d => pointResult v [])
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [smul_smul, sub_eq_add_neg]

/-- All final supplier work has already been paid; the correction adds none. -/
theorem syntaxCount_code (kind : EventKind) (P : Ref Γ .point)
    (reply designated : Fin m → Ref Γ .point) :
    syntaxCount kind (code P reply designated) = 0 := by
  simp [code, syntaxCount, instructionCount, Instr.eventKind, syntaxCount_affineRow]

end AcceleratedLogConcave.Oracle.RetainedMeanCorrection
