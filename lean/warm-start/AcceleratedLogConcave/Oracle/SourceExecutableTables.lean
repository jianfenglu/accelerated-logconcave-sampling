import AcceleratedLogConcave.Oracle.PrivateSamplingProgram
import AcceleratedLogConcave.Oracle.ExecutableData
import AcceleratedLogConcave.Oracle.RecursiveMeanPublicTable

/-! Literal public coefficients and routing for the executed sampling block.
All matrices are computed from source geometry and actual child syntax/shift
arrays. No oracle, tape, realized center or proof certificate enters the table. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SourceExecutableTables
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open scoped BigOperators
variable (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r Ds : ℝ)
  (main final : Fin n → ExecutableData)

def samplingMatrix (i j : Fin n) : ℝ :=
  -(r * S.mesh.location m (e i)) * r * S.row (S.mesh.location m (e i)) (e j)
def samplingNoise : ℝ := RecursiveMeanPublicTable.centerNoise r S.R Ds
def samplingFinalWeight (i : Fin n) : ℝ :=
  -(r / samplingEnd S.τ) * S.row (samplingEnd S.τ) (e i)
def samplingFinalWidth : ℝ := (S.τ / Real.sqrt 2) / (2*r)
def samplingBeta : ℝ := Real.sqrt ((S.τ / Real.sqrt 2)^2 -
  ∑ i, (samplingFinalWeight S e r i)^2 * (samplingFinalWidth S r)^2)

def samplingMainTable := RecursiveMeanPublicTable.sourceLayerTable
  (fun i => (main i).size) (fun i => (main i).program)
  (samplingMatrix S e r) r S.R Ds (r^2)
  (fun i => S.radius r (e i)) (fun i => (main i).shiftVector)
  (fun i => (main i).coefficient)

def samplingFinalTable := RecursiveMeanPublicTable.finalTable
  (fun i => (final i).size) (fun i => (final i).program)
  (fun i => CovarianceSetup.childRoot (samplingNoise S r Ds)
    (S.radius r (e i)) (final i).shiftVector) (fun i => (final i).coefficient)

def samplingScalarTable : Fin (n+(n+4)) → ℝ :=
  Fin.append (fun i => r*S.mesh.location m (e i))
    (Fin.append (samplingFinalWeight S e r)
      (fun i : Fin 4 => if i.val=0 then samplingNoise S r Ds
        else if i.val=1 then (samplingEnd S.τ)⁻¹
        else if i.val=2 then samplingBeta S e r else S.τ/2))

def samplingSize : ℕ := (n+(n+4)) +
  (publicSize (fun i => (main i).size) (fun i => (main i).program) +
    RecursiveMeanPublicTable.finalSize (fun i => (final i).size) (fun i => (final i).program))

def samplingTable : Fin (samplingSize main final) → ℝ :=
  Fin.append (samplingScalarTable S e r Ds)
    (Fin.append (samplingMainTable S e r Ds main) (samplingFinalTable S e r Ds final))

def scalarSlot (j : Fin (n+(n+4))) : Fin (samplingSize main final) := Fin.castAdd _ j
def mainSlot (j : Fin (publicSize (fun i => (main i).size) (fun i => (main i).program))) :
    Fin (samplingSize main final) := Fin.natAdd _ (Fin.castAdd _ j)
def finalSlot (i : Fin n) (j : Fin (childSize (final i).program)) :
    Fin (samplingSize main final) := Fin.natAdd _ (Fin.natAdd _
      (RecursiveMeanPublicTable.finalSlot (fun i => (final i).size)
        (fun i => (final i).program) i j))

@[simp] theorem samplingTable_scalar (j : Fin (n+(n+4))) :
    samplingTable S e r Ds main final (scalarSlot main final j) =
      samplingScalarTable S e r Ds j := by simp [samplingTable,scalarSlot]
@[simp] theorem samplingTable_main (j) :
    samplingTable S e r Ds main final (mainSlot main final j) =
      samplingMainTable S e r Ds main j := by simp [samplingTable,mainSlot]
@[simp] theorem samplingTable_final (i : Fin n) (j : Fin (childSize (final i).program)) :
    samplingTable S e r Ds main final (finalSlot main final i j) =
      matrixTable (CovarianceSetup.childRoot (samplingNoise S r Ds)
        (S.radius r (e i)) (final i).shiftVector) (final i).coefficient j := by
  simp only [samplingTable,finalSlot,Fin.append_right,samplingFinalTable]
  exact RecursiveMeanPublicTable.finalTable_child (fun i => (final i).size)
    (fun i => (final i).program)
    (fun i => CovarianceSetup.childRoot (samplingNoise S r Ds)
      (S.radius r (e i)) (final i).shiftVector) (fun i => (final i).coefficient) i j

/-- Closed fixed-origin sampling syntax configuration with all coefficients
routed to the source table. Every repeated child occurrence remains paid. -/
def samplingConfig (layers : ℕ) :
    PrivateSamplingProgram.Config n (samplingSize main final)
      (fun i => (main i).size) (fun i => (final i).size)
      (fun i => (main i).program) (fun i => (final i).program) where
  mainSlots := mainSlot main final
  mainEquiv i := (main i).enumeration
  finalSlots := finalSlot main final
  finalEquiv i := (final i).enumeration
  directWeight i := scalarSlot main final (Fin.castAdd _ i)
  rowWeight i := scalarSlot main final (Fin.natAdd _ (Fin.castAdd _ i))
  noise := scalarSlot main final (Fin.natAdd _ (Fin.natAdd _ (0 : Fin 4)))
  invEnd := scalarSlot main final (Fin.natAdd _ (Fin.natAdd _ (1 : Fin 4)))
  beta := scalarSlot main final (Fin.natAdd _ (Fin.natAdd _ (2 : Fin 4)))
  reserve := scalarSlot main final (Fin.natAdd _ (Fin.natAdd _ (3 : Fin 4)))
  positionOrigin := [⟨.privateSampling, .setup, 0, 0, 0⟩]
  initialOrigin i := [⟨.privateSampling, .setup, 0, 0, i.val⟩]
  layerOrigin k := [⟨.privateSampling, .mainLayer, 0, k, 0⟩]
  mainDesignated k i := [⟨.privateSampling, .samplingLayer, 0, k, i.val⟩]
  mainResidual k i := [⟨.privateSampling, .samplingLayer, 0, k, i.val⟩]
  mainAuxiliary k i j := [⟨.privateSampling, .samplingLayer, j.val, k, i.val⟩]
  finalOrigin := [⟨.privateSampling, .samplingFinal, 0, 0, 0⟩]
  finalDesignated i := [⟨.privateSampling, .samplingLayer, 1, 0, i.val⟩]
  finalAuxiliary i j := [⟨.privateSampling, .samplingLayer, j.val, 0, i.val⟩]
  finalResidual := [⟨.privateSampling, .samplingFinal, 0, 0, 0⟩]
  finalReserve := [⟨.privateSampling, .samplingFinal, 0, 0, 0⟩]
  layers := layers

end AcceleratedLogConcave.Oracle.SourceExecutableTables
