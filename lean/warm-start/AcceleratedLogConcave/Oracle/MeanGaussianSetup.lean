import AcceleratedLogConcave.Oracle.NoisyLayer
import AcceleratedLogConcave.Conditional.GaussianAssembly

/-!
Executable local Gaussian input assembly. The incoming parent P is retained;
only the n raw auxiliary blocks Z are drawn. The active rows use the literal
positive square root from the manuscript. No comparison coordinate G_E is
sampled or supplied to the program. Probability-law identification is separate.
-/
noncomputable section
namespace AcceleratedLogConcave.Oracle.MeanGaussianSetup
open AffineLowering NoisyLayer Matrix
open AcceleratedLogConcave.Conditional.GaussianAssembly
open scoped BigOperators MatrixOrder

def inputRoot (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt (1 - vecMulVec a a)

def table (a : Fin n → ℝ) : Fin (n*n+n) → ℝ :=
  matrixTable (inputRoot a) a

/-- One closed active coordinate after the raw Gaussian array has been stored. -/
def row (slots : Fin (n*n+n) → Fin C) (P : Ref Γ .point) (i : Fin n) :
    Prog C (replyCtx n Γ) .point :=
  .step [] (.pure (.publicScalar (slots (Fin.natAdd (n*n) i)))) <|
  .step [] (.pure (.smul .here (.there (RefMap.shiftMany n P)))) <|
  affineRow [] .here (List.ofFn fun j : Fin n =>
    (slots (matrixIndex n i j), .there (.there (batchRef j))))

/-- The actual affine instruction row equals the existing retained-input
assembly map for every fixed P and every raw array Z. -/
theorem run_row (a : Fin n → ℝ) (ha : mass a < 1) (P : Ref Γ .point)
    (slots : Fin (n*n+n) → Fin C) (i : Fin n)
    (G : Point d → Point d) (input : Inputs d C)
    (htable : input.coefficient ∘ slots = table a)
    (env : Env d Γ) (Z : Fin n → Point d)
    (tape : Tape d (row slots P i)) :
    run (row slots P i) G input (Env.prepend Z env) tape =
      pointResult (active a (storedPoint env P) Z i) [] := by
  simp only [row, run, evalInstr, evalPure]
  rw [run_affineRow_ofFn]
  have hslot (k : Fin (n*n+n)) : input.coefficient (slots k) = table a k := congrFun htable k
  have hextra : table a (Fin.natAdd (n*n) i) = a i :=
    matrixTable_extra (inputRoot a) a i
  have hentry (j : Fin n) : table a (matrixIndex n i j) = inputRoot a i j :=
    matrixTable_entry (inputRoot a) a i j
  simp only [hslot, hextra, hentry]
  change pointResult (a i • storedPoint (Env.prepend Z env) (RefMap.shiftMany n P) +
    ∑ j, (inputRoot a) i j •
      storedPoint (Env.prepend Z env) (batchRef j)) [] = _
  rw [show storedPoint (Env.prepend Z env) (RefMap.shiftMany n P) =
    storedPoint env P from prepend_shiftMany Z env P]
  simp only [prepend_batchRef]
  exact congrArg (fun v : Point d => pointResult v [])
    (active_eq_sqrt_sum ha (storedPoint env P) Z i).symm

theorem syntaxCount_row (kind : EventKind) (slots : Fin (n*n+n) → Fin C)
    (P : Ref Γ .point) (i : Fin n) :
    syntaxCount kind (row slots P i) = 0 := by
  simp [row, syntaxCount, instructionCount, Instr.eventKind, syntaxCount_affineRow]

/-- Store the raw array and then every active coordinate, keeping old P below
both batches. The continuation can use the first coordinate as G_0 and the
remaining coordinates as the designated active-final P_i. -/
def setup (slots : Fin (n*n+n) → Fin C) (P : Ref Γ .point) (origins : Fin n → Origin)
    (next : Prog C (replyCtx n (replyCtx n Γ)) τ) : Prog C Γ τ :=
  .batch [] (fun i => residualDraw (origins i)) (.batch [] (row slots P) next)

/-- Exactly n new Gaussian blocks, no oracle calls, no comparison residual draw. -/
theorem syntaxCount_setup (kind : EventKind) (slots : Fin (n*n+n) → Fin C)
    (P : Ref Γ .point)
    (origins : Fin n → Origin)
    (next : Prog C (replyCtx n (replyCtx n Γ)) τ) :
    syntaxCount kind (setup slots P origins next) =
      (if kind = .gaussian then n else 0) + syntaxCount kind next := by
  cases kind <;> simp [setup, syntaxCount, residualDraw, syntaxCount_row,
    instructionCount, Instr.eventKind]

end AcceleratedLogConcave.Oracle.MeanGaussianSetup
