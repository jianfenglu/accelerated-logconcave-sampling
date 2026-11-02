import AcceleratedLogConcave.Oracle.ExecutableData
import AcceleratedLogConcave.Oracle.NonterminalMeanBlock
import AcceleratedLogConcave.Oracle.PrefixPublicTable
import AcceleratedLogConcave.Oracle.SourceExecutableShift
import AcceleratedLogConcave.Oracle.RecursiveMeanPublicTable

/-! Actual local source mean constructor. Smaller child syntax and the private
sampling syntax are executed in the literal incoming and synchronous block. Public
coefficients and Gaussian-slot weights are computed here; no accuracy, law,
query-shift, or work certificate is a field of the resulting executable data. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SourceMeanExecutable
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open scoped BigOperators

variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (r σ Ds δ t w : ℝ) (main : Fin n → ExecutableData)
  (final : Fin m → ExecutableData) (sampling : ExecutableData)

def rowBound : ℝ := 256*(m:ℝ)^5*(r/σ)*Real.rpow δ (-4*t-w)+4*r^2

def assembly : Fin (m+1) → ℝ :=
  Fin.cases (1/2) (fun i => Numerics.GaussLegendre.weight m i * M.R * Real.sqrt 3 / 4)

def mainTable := RecursiveMeanPublicTable.sourceLayerTable
  (fun i => (main i).size) (fun i => (main i).program)
  (fun i j => M.matrix r σ (nodes i) (nodes j)) r M.R Ds
  (rowBound (m := m) r σ δ t w)
  (fun i => M.radius r (nodes i)) (fun i => (main i).shiftVector)
  (fun i => (main i).coefficient)

def finalTable := RecursiveMeanPublicTable.sourceFinalTable
  (fun i => (final i).size) (fun i => (final i).program) r M.R Ds
  (fun i => (final i).shiftVector) (fun i => (final i).coefficient)

def bodySize : ℕ := 1+(publicSize (fun i => (main i).size) (fun i => (main i).program) +
  (RecursiveMeanPublicTable.finalSize (fun i => (final i).size) (fun i => (final i).program) +
    (1+(m+m))))

def prefixSize : ℕ := PrefixPublicTable.size sampling.size (m+1) n a

def size : ℕ := prefixSize (m := m) (n := n) (a := a) sampling + bodySize main final

def prefixSlot (j : Fin (prefixSize (m := m) (n := n) (a := a) sampling)) :
    Fin (size (a := a) main final sampling) := Fin.castAdd _ j

def bodySlot (j : Fin (bodySize main final)) : Fin (size (a := a) main final sampling) :=
  Fin.natAdd _ j

def table : Fin (size (a := a) main final sampling) → ℝ :=
  Fin.append (PrefixPublicTable.table M nodes anchors r σ sampling.coefficient (assembly M))
    (RecursiveMeanPublicTable.table (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (mainTable M nodes r σ Ds δ t w main) (finalTable M r Ds final) σ
      (Numerics.GaussLegendre.weight m) (fun _ => RecursiveMeanPublicTable.finalWidth M.R σ))

def mainSlot (j : Fin (publicSize (fun i => (main i).size) (fun i => (main i).program))) :
    Fin (size (a := a) main final sampling) := bodySlot (a := a) main final sampling (RecursiveMeanPublicTable.layerSlot j)

def finalSlot (i : Fin m) (j : Fin (childSize (final i).program)) :
    Fin (size (a := a) main final sampling) := bodySlot (a := a) main final sampling
      (RecursiveMeanPublicTable.activeFinalSlot (RecursiveMeanPublicTable.finalSlot
        (fun i => (final i).size) (fun i => (final i).program) i j))

def correctionSlot (j : Fin (1+(m+m))) : Fin (size (a := a) main final sampling) :=
  bodySlot (a := a) main final sampling (RecursiveMeanPublicTable.correctionSlot j)

def rhoSlot : Fin (size (a := a) main final sampling) :=
  bodySlot (a := a) main final sampling RecursiveMeanPublicTable.rhoSlot

def initialOrigin (i : Fin n) : Origin := [⟨.mean,.setup,0,0,i.val⟩]
def layerOrigin (k : ℕ) : Origin := [⟨.mean,.mainLayer,0,k,0⟩]
def mainDesignated (k : ℕ) (i : Fin n) : Origin := [⟨.mean,.mainLayer,0,k,i.val⟩]
def residualOrigin (k : ℕ) (i : Fin n) : Origin := [⟨.mean,.mainLayer,1,k,i.val⟩]
def mainAuxiliary (k : ℕ) (i : Fin n)
    (j : Fin (tapeShape (main i).program).gaussianBlocks) : Origin :=
  [⟨.mean,.mainLayer,j.val,k,i.val⟩]
def finalOrigin : Origin := [⟨.mean,.activeFinal,0,0,0⟩]
def finalAuxiliary (i : Fin m) (j : Fin (tapeShape (final i).program).gaussianBlocks) : Origin :=
  [⟨.mean,.activeFinal,j.val,0,i.val⟩]
def assemblyOrigin (i : Fin (m+1)) : Origin := [⟨.mean,.setup,1,0,i.val⟩]
def flowOrigin (i : Fin h) : Origin := [⟨.mean,.setup,2,0,i.val⟩]

/-- The incoming incoming has stored its direct vector and retained both P and
all designated final inputs; initialization is performed exactly once here. -/
def body (layers : ℕ) : Prog (size (a := a) main final sampling)
    (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]) .point :=
  NonterminalMeanBlock.code (fun i => (main i).size) (fun i => (main i).program)
    (mainSlot (a := a) main final sampling) (fun i => (main i).enumeration)
    (fun i => (final i).size) (fun i => (final i).program)
    (fun i => (final i).enumeration) (finalSlot (a := a) main final sampling)
    (correctionSlot (a := a) main final sampling) (rhoSlot (a := a) main final sampling)
    (MeanExecutablePrefix.saved .here) MeanExecutablePrefix.designated MeanExecutablePrefix.direct
    (fun i => nodes.symm (.center M i)) initialOrigin layerOrigin mainDesignated residualOrigin
    (mainAuxiliary main) finalOrigin (finalAuxiliary final) layers

/-- Actual private call, scale, retained-input split, flow draws and direct rows. -/
def incoming (layers : ℕ) : Prog (size (a := a) main final sampling) [.point,.point] .point :=
  MeanExecutablePrefix.code M anchors seeds sampling.size sampling.program
    (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
    (prefixSlot (a := a) main final sampling PrefixPublicTable.scaleSlot) (.there .here) .here
    (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.assemblySlot)
    assemblyOrigin flowOrigin (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.directSlot)
    (body (a := a) (h := h) M nodes main final sampling layers)

def program (layers : ℕ) : Program (size (a := a) main final sampling) .point :=
  .step [] .center (.step [] .momentum (incoming M nodes anchors seeds main final sampling layers))

/-- Actual normalized direct-center coefficient; the position anchor term of
centerForm includes its outer physical r. -/
def centerShift (i : Fin n) : ℝ :=
  1 - (M.centerForm r σ (nodes i) M.positionAtom / r) / backwardEnd M.R

def mainRaw (i : Fin n) : Fin (tapeShape (main i).program).gaussianBlocks → ℝ :=
  LayerShift.rawShift (RecursiveMeanPublicTable.centerNoise r M.R Ds)
    (M.radius r (nodes i)) r (centerShift M nodes r σ i) (main i).shiftVector

def bodyShift (layers : ℕ) :
    GaussianSlot (body (a := a) (h := h) M nodes main final sampling layers) → ℝ :=
  SourceExecutableShift.meanBlock (fun i => (main i).size) (fun i => (main i).program)
    (mainSlot (a := a) main final sampling) (fun i => (main i).enumeration)
    (fun i => (final i).size) (fun i => (final i).program)
    (fun i => (final i).enumeration) (finalSlot (a := a) main final sampling)
    (correctionSlot (a := a) main final sampling) (rhoSlot (a := a) main final sampling)
    (MeanExecutablePrefix.saved .here) MeanExecutablePrefix.designated MeanExecutablePrefix.direct
    (fun i => nodes.symm (.center M i)) initialOrigin layerOrigin mainDesignated residualOrigin
    (mainAuxiliary main) finalOrigin (finalAuxiliary final) layers (mainRaw M nodes r σ Ds main)

def incomingShift (layers : ℕ) (privateShift : GaussianSlot sampling.program → ℝ) :
    GaussianSlot (incoming M nodes anchors seeds main final sampling layers) → ℝ :=
  SourceExecutableShift.meanPrefix M anchors seeds sampling.size sampling.program
    (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
    (prefixSlot (a := a) main final sampling PrefixPublicTable.scaleSlot) (.there .here) .here
    (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.assemblySlot)
    assemblyOrigin flowOrigin
    (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.directSlot)
    (body (a := a) (h := h) M nodes main final sampling layers) privateShift
    (bodyShift M nodes r σ Ds main final sampling layers)

def shift (layers : ℕ) (privateShift : GaussianSlot sampling.program → ℝ) :
    GaussianSlot (program M nodes anchors seeds main final sampling layers) → ℝ :=
  Sum.elim (fun s => nomatch s)
    (Sum.elim (fun s => nomatch s)
      (incomingShift M nodes anchors seeds r σ Ds main final sampling layers privateShift))

/-- Construct actual syntax, literal public coefficients, and the calculated
Gaussian-slot shift. The private shift is the separately constructed reserve-
augmented shift on this exact sampling program, not a correctness certificate. -/
def build (layers : ℕ) (privateShift : GaussianSlot sampling.program → ℝ) : ExecutableData where
  size := size (a := a) main final sampling
  program := program M nodes anchors seeds main final sampling layers
  coefficient := table M nodes anchors r σ Ds δ t w main final sampling
  shift := shift M nodes anchors seeds r σ Ds main final sampling layers privateShift

@[simp] theorem table_prefix (j) :
    table M nodes anchors r σ Ds δ t w main final sampling (prefixSlot (a := a) main final sampling j) =
      PrefixPublicTable.table M nodes anchors r σ sampling.coefficient (assembly M) j := by
  unfold table prefixSlot
  erw [Fin.append_left]

@[simp] theorem table_body (j) :
    table M nodes anchors r σ Ds δ t w main final sampling (bodySlot (a := a) main final sampling j) =
      RecursiveMeanPublicTable.table (RecursiveMeanPublicTable.centerNoise r M.R Ds)
        (mainTable M nodes r σ Ds δ t w main) (finalTable M r Ds final) σ
        (Numerics.GaussLegendre.weight m) (fun _ => RecursiveMeanPublicTable.finalWidth M.R σ) j := by
  unfold table bodySlot
  erw [Fin.append_right]

@[simp] theorem table_main (j) :
    table M nodes anchors r σ Ds δ t w main final sampling (mainSlot (a := a) main final sampling j) =
      mainTable M nodes r σ Ds δ t w main j := by
  unfold mainSlot
  erw [table_body, RecursiveMeanPublicTable.table_layer]

@[simp] theorem table_final (i : Fin m) (j : Fin (childSize (final i).program)) :
    table M nodes anchors r σ Ds δ t w main final sampling (finalSlot (a := a) main final sampling i j) =
      matrixTable (CovarianceSetup.childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
        (r*M.R) (final i).shiftVector) (final i).coefficient j := by
  unfold finalSlot
  erw [table_body, RecursiveMeanPublicTable.table_final]
  exact RecursiveMeanPublicTable.finalTable_child (fun i => (final i).size)
    (fun i => (final i).program)
    (fun i => CovarianceSetup.childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (r*M.R) (final i).shiftVector) (fun i => (final i).coefficient) i j

@[simp] theorem table_correction (j) :
    table M nodes anchors r σ Ds δ t w main final sampling (correctionSlot (a := a) main final sampling j) =
      RetainedMeanCorrection.table σ (Numerics.GaussLegendre.weight m)
        (fun _ => RecursiveMeanPublicTable.finalWidth M.R σ) j := by
  unfold correctionSlot
  erw [table_body, RecursiveMeanPublicTable.table_correction]

@[simp] theorem table_rho :
    table M nodes anchors r σ Ds δ t w main final sampling (rhoSlot (a := a) main final sampling) =
      RecursiveMeanPublicTable.centerNoise r M.R Ds := by
  unfold rhoSlot
  erw [table_body, RecursiveMeanPublicTable.table_rho]

theorem queries_program (layers : ℕ) :
    queryCount (program M nodes anchors seeds main final sampling layers) =
      queryCount sampling.program + layers*(∑ i, queryCount (main i).program) +
        ∑ i, queryCount (final i).program := by
  simp only [queryCount, syntaxCounts]
  rw [program, syntaxCount, syntaxCount]
  norm_num only [instructionCount, Instr.eventKind]
  rw [incoming, MeanExecutablePrefix.syntaxCount_code]
  simp only [show EventKind.gradient ≠ EventKind.gaussian from by decide, ite_false, add_zero]
  rw [body, NonterminalMeanBlock.queries_code]
  simp [Nat.add_assoc]

/-- Every execution charges the private sampler and every main/final mean child. -/
theorem executed_queries (layers : ℕ) (privateShift : GaussianSlot sampling.program → ℝ)
    (G : Point d → Point d)
    (input : Inputs d (size (a := a) main final sampling))
    (tape : Tape d (build M nodes anchors seeds r σ Ds δ t w main final sampling layers privateShift).program) :
    (traceCounts (run (build M nodes anchors seeds r σ Ds δ t w main final sampling layers privateShift).program
      G input Env.empty tape).trace).queries =
      queryCount sampling.program + layers*(∑ i, queryCount (main i).program) +
        ∑ i, queryCount (final i).program := by
  erw [run_counts]
  exact queries_program M nodes anchors seeds main final sampling layers

end AcceleratedLogConcave.Oracle.SourceMeanExecutable
