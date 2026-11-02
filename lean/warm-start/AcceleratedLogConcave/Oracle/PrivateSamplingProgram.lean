import AcceleratedLogConcave.Oracle.PrivateSamplingFinal
import AcceleratedLogConcave.Oracle.RecursiveMeanFinalState

/-! A finite sampling-only block. Its only recursive suppliers are mean programs.
The public table routing is explicit. Precision selection belongs to the
precision-recursive caller; this module never calls a sampling program. -/
namespace AcceleratedLogConcave.Oracle.PrivateSamplingProgram
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram RecursiveMeanContinuation
open scoped BigOperators

structure Config (n C : ℕ) (c cf : Fin n → ℕ)
    (p : ∀ i, Program (c i) .point) (pf : ∀ i, Program (cf i) .point) where
  mainSlots : Fin (publicSize c p) → Fin C
  mainEquiv : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks
  finalSlots : ∀ i, Fin (childSize (pf i)) → Fin C
  finalEquiv : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks
  directWeight : Fin n → Fin C
  rowWeight : Fin n → Fin C
  noise : Fin C
  invEnd : Fin C
  beta : Fin C
  reserve : Fin C
  positionOrigin : Origin
  initialOrigin : Fin n → Origin
  layerOrigin : ℕ → Origin
  mainDesignated : ℕ → Fin n → Origin
  mainResidual : ℕ → Fin n → Origin
  mainAuxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin
  finalOrigin : Origin
  finalDesignated : Fin n → Origin
  finalAuxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin
  finalResidual : Origin
  finalReserve : Origin
  layers : ℕ

variable {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
  {pf : ∀ i, Program (cf i) .point}

def finish (cfg : Config n C c cf p pf) (old : Fin n → Ref Γ .point)
    (direct : Ref Γ .point) : Prog C Γ .point :=
  PrivateSamplingFinal.code cf pf cfg.finalEquiv cfg.finalSlots cfg.rowWeight
    cfg.beta cfg.reserve old direct cfg.finalOrigin cfg.finalDesignated
    cfg.finalAuxiliary cfg.finalResidual cfg.finalReserve

def body (cfg : Config n C c cf p pf) (direct : Fin n → Ref Γ .point)
    (outputDirect : Ref Γ .point) : Prog C Γ .point :=
  initializeCenters cfg.noise direct [] cfg.initialOrigin
    (iterateThen c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin cfg.mainDesignated
      cfg.mainResidual cfg.mainAuxiliary
      (fun old _ saved => finish cfg old (saved outputDirect)) cfg.layers batchRef
      (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
      (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)))

/-- Actual x instruction and Y₀ draw, then literal x+r aᵢY₀ direct rows and
Y₀/ρₑ output direct term, paid initialization, N layers, and fresh final row. -/
def code (cfg : Config n C c cf p pf) : Program C .point :=
  .step [] .center <|
  .step cfg.positionOrigin .gaussian <|
  .step [] (.pure (.publicScalar cfg.invEnd)) <|
  .step [] (.pure (.smul .here (.there .here))) <|
  .batch [] (fun i => affineRow [] (.there (.there (.there .here)))
    [(cfg.directWeight i, .there (.there .here))])
    (body cfg batchRef (RefMap.shiftMany n .here))

theorem syntaxCount_body (kind : EventKind) (cfg : Config n C c cf p pf)
    (direct : Fin n → Ref Γ .point) (outputDirect : Ref Γ .point) :
    syntaxCount kind (body cfg direct outputDirect) =
      (if kind = .gaussian then n else 0) +
      (cfg.layers * layerInventory kind c p +
        ((if kind = .gaussian then n + ∑ i, (tapeShape (pf i)).gaussianBlocks
          else ∑ i, syntaxCount kind (pf i)) + (if kind = .gaussian then 2 else 0))) := by
  unfold body
  rw [syntaxCount_initialize]
  congr 1
  apply syntaxCount_iterateThen
  intro Δ old direct saved
  exact PrivateSamplingFinal.syntaxCount_code kind cf pf cfg.finalEquiv cfg.finalSlots
    cfg.rowWeight cfg.beta cfg.reserve old (saved outputDirect) cfg.finalOrigin
    cfg.finalDesignated cfg.finalAuxiliary cfg.finalResidual cfg.finalReserve

theorem syntaxCount_code (kind : EventKind) (cfg : Config n C c cf p pf) :
    syntaxCount kind (code cfg) =
      (if kind = .gaussian then 1 else 0) +
      ((if kind = .gaussian then n else 0) +
      (cfg.layers * layerInventory kind c p +
        ((if kind = .gaussian then n + ∑ i, (tapeShape (pf i)).gaussianBlocks
          else ∑ i, syntaxCount kind (pf i)) + (if kind = .gaussian then 2 else 0)))) := by
  simp only [code, syntaxCount, syntaxCount_affineRow, Fin.sum_ofFn,
    Finset.sum_const_zero, zero_add, syntaxCount_body]
  cases kind <;> simp [instructionCount,Instr.eventKind]

/-- Original-gradient work of every execution, including every supplier. -/
theorem queries_code (cfg : Config n C c cf p pf) :
    queryCount (code cfg) = cfg.layers * (∑ i, queryCount (p i)) +
      ∑ i, queryCount (pf i) := by
  change syntaxCount .gradient _ = _
  rw [syntaxCount_code]
  simp [layerInventory, queryCount, syntaxCounts]

/-- Every oracle and tape executes precisely the syntax inventory. -/
theorem executed_queries (cfg : Config n C c cf p pf)
    (G : Point d → Point d) (input : Inputs d C) (tape : Tape d (code cfg)) :
    (traceCounts (run (code cfg) G input Env.empty tape).trace).queries =
      cfg.layers * (∑ i, queryCount (p i)) + ∑ i, queryCount (pf i) := by
  rw [run_counts]
  exact queries_code cfg

end AcceleratedLogConcave.Oracle.PrivateSamplingProgram
