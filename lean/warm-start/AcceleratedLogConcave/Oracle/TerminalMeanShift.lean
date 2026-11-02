import AcceleratedLogConcave.Oracle.TerminalMean
import AcceleratedLogConcave.Oracle.ChildAbsorption
import Mathlib.Tactic.Abel

/-!
Actual base case for the recursive compiler's query-shift invariant.
The sole auxiliary Gaussian is shifted by -Delta/r while the supplied momentum
is retained. Equality is of the full execution Result, including the original
query point and oracle reply, not merely of the returned vector or its law.
No Gaussian-law hypothesis, Lipschitz premise, or accuracy certificate is used.
-/
noncomputable section
namespace AcceleratedLogConcave.Oracle.TerminalMeanShift
open TapeLowering ChildAbsorption CovarianceSetup

/-- The literal public table of the already implemented terminal branch. -/
def coefficients (a r sigma : ℝ) : Fin 3 → ℝ :=
  fun j => if j.val = 0 then r else if j.val = 1 then sigma else a

/-- The actual Gaussian instruction occurs after the five input/setup steps. -/
def auxiliarySlot (origin : Origin) : GaussianSlot (terminalMeanProgram origin) :=
  .inr (.inr (.inr (.inr (.inr (.inl PUnit.unit)))))

/-- Exact interpreter result on the existing split/join tape, retaining every
nongeneric residual coordinate rather than postulating a new seed model. -/
theorem run_joinTape (origin : Origin) (G : Point d → Point d)
    (a r sigma : ℝ) (x P : Point d)
    (z : GaussianSlot (terminalMeanProgram origin) → Point d)
    (rest : ResidualTape (terminalMeanProgram origin)) :
    run (terminalMeanProgram origin) G ⟨coefficients a r sigma,x,P⟩ Env.empty
      (joinTape (terminalMeanProgram origin) z rest) =
      ⟨a • G (a • (x + r • z (auxiliarySlot origin))) + sigma • P,
        [Event.gaussian origin,
          Event.gradient origin (a • (x + r • z (auxiliarySlot origin)))
            (G (a • (x + r • z (auxiliarySlot origin))))]⟩ := rfl

/-- Terminal query absorption for any enumeration of its sole Gaussian slot.
The scalar a remains the public original-gradient scale adapter. -/
theorem queryShift (origin : Origin) (a r sigma : ℝ) (hr : 0 < r)
    (e : GaussianSlot (terminalMeanProgram origin) ≃ Fin 1) :
    QueryShift (terminalMeanProgram origin) e (coefficients a r sigma) r
      (fun _ => -1) := by
  intro d G x P Delta z rest
  rw [run_joinTape, run_joinTape]
  have hscale : r * ((-1:ℝ)/r) = -1 := by
    field_simp [ne_of_gt hr]
  have hcenter : x + Delta + r • (z (e (auxiliarySlot origin)) + ((-1:ℝ)/r) • Delta) =
      x + r • z (e (auxiliarySlot origin)) := by
    rw [smul_add, smul_smul, hscale, neg_one_smul]
    abel
  simp only [hcenter]

/-- Canonical source base case for downstream freshChild/LayerShift consumers. -/
theorem queryShift_canonical (origin : Origin) (a r sigma : ℝ) (hr : 0 < r) :
    QueryShift (terminalMeanProgram origin) (gaussianSlotEquiv (terminalMeanProgram origin))
      (coefficients a r sigma) r (fun _ => -1) :=
  queryShift origin a r sigma hr (gaussianSlotEquiv (terminalMeanProgram origin))

/-- Exact terminal shift mass, including zero-dimensional physical space. -/
theorem shiftSq_terminal : shiftSq (fun _ : Fin 1 => (-1:ℝ)) = 1 := by
  simp [shiftSq]

/-- Concrete admissibility at the terminal child, with its actual shift budget 1. -/
theorem admissible_terminal (rho r : ℝ) (hrho : 0 ≤ rho) (hr : 0 < r)
    (hsmall : rho ≤ r/2) :
    Admissible rho r 1 (fun _ : Fin 1 => (-1:ℝ)) := by
  refine ⟨hrho, hr, by norm_num, ?_, ?_⟩
  · rw [shiftSq_terminal]
    norm_num
  · simpa using hsmall

end AcceleratedLogConcave.Oracle.TerminalMeanShift
