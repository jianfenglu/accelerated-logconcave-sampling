import AcceleratedLogConcave.Oracle.TerminalMeanShift
import AcceleratedLogConcave.Oracle.RetainedMeanFinalValue

/-! Deterministic center stability on complete fixed tapes. The child premise
quantifies every entering momentum and every residual tape; no probability or
admissibility assertion is needed for transfer through the existing wrappers. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.FixedTapeStability
open TapeLowering AffineLowering NoisyLayer RetainedMeanFinalBatch
open scoped NNReal

/-- Child induction hypothesis on the complete source tape. -/
def ChildStable (p : Program c .point) (coeff : Fin c → ℝ)
    (G : Point d → Point d) (κ : ℝ) : Prop :=
  ∀ (P x y : Point d) (z : GaussianSlot p → Point d) (rest : ResidualTape p),
    ‖childPoint (run p G ⟨coeff,x,P⟩ Env.empty (joinTape p z rest)) -
      childPoint (run p G ⟨coeff,y,P⟩ Env.empty (joinTape p z rest))‖ ≤ κ * ‖x-y‖

/-- Split/join covers arbitrary raw tapes, retaining all residual coordinates. -/
theorem childStable_tape (p : Program c .point) (coeff : Fin c → ℝ)
    (G : Point d → Point d) (κ : ℝ) (h : ChildStable p coeff G κ)
    (P x y : Point d) (tape : Tape d p) :
    ‖childPoint (run p G ⟨coeff,x,P⟩ Env.empty tape) -
      childPoint (run p G ⟨coeff,y,P⟩ Env.empty tape)‖ ≤ κ * ‖x-y‖ := by
  simpa only [joinTape_splitTape] using h P x y (splitTape p tape).1 (splitTape p tape).2

/-- Actual terminal normalization is scale on both sides of the oracle call. -/
theorem terminal_childStable (origin : Origin) (scale r σ : ℝ)
    (G : Point d → Point d) (κ : ℝ≥0)
    (hG : LipschitzWith κ (fun x => scale • G (scale • x))) :
    ChildStable (terminalMeanProgram origin)
      (TerminalMeanShift.coefficients scale r σ) G κ := by
  intro P x y z rest
  simp only [TerminalMeanShift.run_joinTape,childPoint]
  rw [add_sub_add_right_eq_sub]
  simpa only [add_sub_add_right_eq_sub] using
    hG.norm_sub_le (x+r • z (TerminalMeanShift.auxiliarySlot origin))
      (y+r • z (TerminalMeanShift.auxiliarySlot origin))

/-- Equivalent unnormalized bound pays both factors of the terminal scale. -/
theorem terminal_childStable_of_oracle (origin : Origin) (scale r σ : ℝ)
    (G : Point d → Point d) (κ : ℝ≥0) (hG : LipschitzWith κ G) :
    ChildStable (terminalMeanProgram origin)
      (TerminalMeanShift.coefficients scale r σ) G (|scale|^2 * κ) := by
  intro P x y z rest
  simp only [TerminalMeanShift.run_joinTape,childPoint,add_sub_add_right_eq_sub]
  rw [← smul_sub,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |scale| * ((κ:ℝ) * ‖scale • (x+r • z (TerminalMeanShift.auxiliarySlot origin)) -
        scale • (y+r • z (TerminalMeanShift.auxiliarySlot origin))‖) :=
      mul_le_mul_of_nonneg_left (hG.norm_sub_le _ _) (abs_nonneg _)
    _ = _ := by rw [← smul_sub,add_sub_add_right_eq_sub,norm_smul,Real.norm_eq_abs]; ring

/-- A fresh child uses exactly the same transformed full tape and entering P. -/
theorem freshChild_sub_le (p : Program c .point) (e : GaussianSlot p ≃ Fin g)
    (slots : Fin (g*g+c) → Fin C) (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin g → Origin)
    (T : Fin g → Fin g → ℝ) (coeff : Fin c → ℝ)
    (G : Point d → Point d) (input : Inputs d C) (env env' : Env d Γ)
    (htable : input.coefficient ∘ slots = matrixTable T coeff)
    (κ : ℝ) (hchild : ChildStable p coeff G κ)
    (tape : Tape d (freshChild p e slots old designated auxiliary)) :
    ‖childPoint (run (freshChild p e slots old designated auxiliary) G input env tape) -
      childPoint (run (freshChild p e slots old designated auxiliary) G input env' tape)‖ ≤
      κ * ‖storedPoint env old - storedPoint env' old‖ := by
  rw [run_freshChild p e slots old designated auxiliary T coeff G input env htable,
    run_freshChild p e slots old designated auxiliary T coeff G input env' htable]
  exact childStable_tape p coeff G κ hchild _ _ _ _

/-- Designated inputs are retained identically; only the entering center varies. -/
theorem designatedChild_sub_le (p : Program c .point) (e : GaussianSlot p ≃ Fin g)
    (slots : Fin (g*g+c) → Fin C) (center P : Ref Γ .point)
    (auxiliary : Fin g → Origin) (T : Fin g → Fin g → ℝ) (coeff : Fin c → ℝ)
    (G : Point d → Point d) (input : Inputs d C) (env env' : Env d Γ)
    (htable : input.coefficient ∘ slots = matrixTable T coeff)
    (hP : storedPoint env P = storedPoint env' P)
    (κ : ℝ) (hchild : ChildStable p coeff G κ)
    (tape : Tape d (designatedChild p e slots center P auxiliary)) :
    ‖childPoint (run (designatedChild p e slots center P auxiliary) G input env tape) -
      childPoint (run (designatedChild p e slots center P auxiliary) G input env' tape)‖ ≤
      κ * ‖storedPoint env center - storedPoint env' center‖ := by
  rw [run_designatedChild p e slots center P auxiliary T coeff G input env htable,
    run_designatedChild p e slots center P auxiliary T coeff G input env' htable]
  dsimp only [childPoint]
  rw [hP]
  exact childStable_tape p coeff G κ hchild _ _ _ _

end AcceleratedLogConcave.Oracle.FixedTapeStability
