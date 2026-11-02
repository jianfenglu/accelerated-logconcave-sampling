import AcceleratedLogConcave.Oracle.ExecutableShiftWeights
import AcceleratedLogConcave.Oracle.PrivateSamplingProgram
import AcceleratedLogConcave.Oracle.MeanExecutablePrefix
import AcceleratedLogConcave.Oracle.NonterminalMeanBlock

/-! Actual Gaussian-slot shift assembly for sampling and nonterminal mean
programs. These definitions construct coefficients from the literal program
combinators; they do not assert QueryShift. The recursive constructor supplies
computed raw child weights, obtained from the smaller children's shifts.
-/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SourceExecutableShift
open AffineLowering TapeLowering NoisyLayer RecursiveMeanContinuation
open ExecutableShiftWeights

variable {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
  {pf : ∀ i, Program (cf i) .point}

/-- All sampling-final child draws remain present. The ordinary reserve weight
is zero; the containing mean adds its source reserve correction at this slot. -/
def samplingFinal (cfg : PrivateSamplingProgram.Config n C c cf p pf)
    (old : Fin n → Ref Γ .point) (direct : Ref Γ .point)
    (final : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ) (reserve : ℝ) :
    GaussianSlot (PrivateSamplingProgram.finish cfg old direct) → ℝ :=
  Sum.elim (fun s => freshWeights (pf s.1) (cfg.finalEquiv s.1) (cfg.finalSlots s.1)
      (old s.1) (cfg.finalDesignated s.1) (cfg.finalAuxiliary s.1) (final s.1) s.2)
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => reserve) (fun _ => 0)))

/-- The initialization noises stay fixed, as do every layer's center residuals. -/
def samplingBody (cfg : PrivateSamplingProgram.Config n C c cf p pf)
    (direct : Fin n → Ref Γ .point) (outputDirect : Ref Γ .point)
    (main : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (final : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ) (reserve : ℝ) :
    GaussianSlot (PrivateSamplingProgram.body cfg direct outputDirect) → ℝ :=
  initializeWeights cfg.noise direct [] cfg.initialOrigin _
    (iterateWeights c p cfg.mainSlots cfg.mainEquiv cfg.layerOrigin cfg.mainDesignated
      cfg.mainResidual cfg.mainAuxiliary
      (fun old _ saved => PrivateSamplingProgram.finish cfg old (saved outputDirect))
      main (fun old _ saved => samplingFinal cfg old (saved outputDirect) final reserve)
      cfg.layers batchRef
      (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
      (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)))

/-- Literal sampling shift: Y₀ gets `position`; child raw auxiliaries get their
computed source vectors; the residual is fixed and reserve gets its explicit
mean-private correction when present. All deterministic rows carry zero. -/
def sampling (cfg : PrivateSamplingProgram.Config n C c cf p pf)
    (position : ℝ) (main : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (final : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ) (reserve : ℝ) :
    GaussianSlot (PrivateSamplingProgram.code cfg) → ℝ :=
  Sum.elim (fun s => nomatch s)
    (Sum.elim (fun _ => position)
      (Sum.elim (fun s => nomatch s)
        (Sum.elim (fun s => nomatch s)
          (Sum.elim (fun _ => 0)
            (samplingBody cfg batchRef (RefMap.shiftMany n .here) main final reserve)))))

/-- Actual nonterminal mean tail: initialization and active-final slots are
fixed; every synchronous main occurrence carries its computed raw child shift. -/
def meanBlock (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (mainSlots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (ef : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (finalSlots : ∀ i, Fin (childSize (pf i)) → Fin C)
    (correctionSlots : Fin (1+(m+m)) → Fin C) (rhoSlot : Fin C)
    (P : Ref Γ .point) (designated : Fin m → Ref Γ .point)
    (direct : Fin n → Ref Γ .point) (active : Fin m → Fin n)
    (initialOrigin : Fin n → Origin) (outer : ℕ → Origin)
    (mainDesignated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finalOuter : Origin)
    (finalAuxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin)
    (N : ℕ) (raw : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ) :
    GaussianSlot (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots
      correctionSlots rhoSlot P designated direct active initialOrigin outer mainDesignated
      residual auxiliary finalOuter finalAuxiliary N) → ℝ :=
  initializeWeights rhoSlot direct [] initialOrigin _
    (iterateWeights c p mainSlots e outer mainDesignated residual auxiliary
      (fun old _ saved => RetainedMeanFinalBatch.paidCorrection cf pf ef finalSlots
        correctionSlots (saved P) (fun i => old (active i))
        (fun i => saved (designated i)) finalOuter finalAuxiliary)
      raw (fun _ _ _ _ => 0) N batchRef
      (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
      (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)))

/-- The incoming mean's private sampling slot is lowered literally. All local
assembly, conditional-flow and deterministic-direct slots stay fixed. -/
def meanPrefix (M : Numerics.AffineGraph.MeanGeometry order)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin order × M.Kernel)
    (privateC : ℕ) (privateCode : Program privateC .point)
    (privateSlots : Fin privateC → Fin C) (scaleSlot : Fin C)
    (x P : Ref Γ .point)
    (assemblySlots : Fin ((m+1)*(m+1)+(m+1)) → Fin C)
    (assemblyOrigins : Fin (m+1) → Origin) (flowOrigins : Fin h → Origin)
    (directSlots : Fin (n*a) → Fin C)
    (next : Prog C (MeanExecutablePrefix.readyCtx n (m+1) h Γ) τ)
    (privateShift : GaussianSlot privateCode → ℝ) (tail : GaussianSlot next → ℝ) :
    GaussianSlot (MeanExecutablePrefix.code M anchors seeds privateC privateCode privateSlots
      scaleSlot x P assemblySlots assemblyOrigins flowOrigins directSlots next) → ℝ :=
  Sum.elim (fun s => lowerWeights privateSlots privateCode (fun r => nomatch r)
      x P privateShift s.2)
    (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
        (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) tail)))))

end AcceleratedLogConcave.Oracle.SourceExecutableShift
