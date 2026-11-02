import AcceleratedLogConcave.Oracle.MeanGaussianSetup
import AcceleratedLogConcave.Oracle.PrefixDirect

/-! Canonical disjoint public coefficient regions for the executable incoming
mean prefix. All coefficients are fixed from source data and child tables. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.PrefixPublicTable
open AffineLowering
open AcceleratedLogConcave.Numerics.AffineGraph

def size (privateC f n a : ℕ) := privateC + (1 + ((f*f+f) + n*a))

def privateSlot : Fin privateC → Fin (size privateC f n a) := Fin.castAdd _
def scaleSlot : Fin (size privateC f n a) :=
  Fin.natAdd privateC (Fin.castAdd _ (0 : Fin 1))
def assemblySlot : Fin (f*f+f) → Fin (size privateC f n a) :=
  fun k => Fin.natAdd privateC (Fin.natAdd 1 (Fin.castAdd (n*a) k))
def directSlot : Fin (n*a) → Fin (size privateC f n a) :=
  fun k => Fin.natAdd privateC (Fin.natAdd 1 (Fin.natAdd (f*f+f) k))

def table (M : MeanGeometry order) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ : ℝ)
    (privateCoeff : Fin privateC → ℝ) (assembly : Fin f → ℝ) :
    Fin (size privateC f n a) → ℝ :=
  Fin.append privateCoeff (Fin.append (fun _ : Fin 1 => backwardEnd M.R)
    (Fin.append (MeanGaussianSetup.table assembly) (PrefixDirect.table M nodes anchors r σ)))

@[simp] theorem table_private (M : MeanGeometry order) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ : ℝ)
    (privateCoeff : Fin privateC → ℝ) (assembly : Fin f → ℝ) (k : Fin privateC) :
    table M nodes anchors r σ privateCoeff assembly (privateSlot k) = privateCoeff k := by
  simp [table, privateSlot]

@[simp] theorem table_scale (M : MeanGeometry order) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ : ℝ)
    (privateCoeff : Fin privateC → ℝ) (assembly : Fin f → ℝ) :
    table M nodes anchors r σ privateCoeff assembly scaleSlot = backwardEnd M.R := by
  simp [table, scaleSlot]

@[simp] theorem table_assembly (M : MeanGeometry order) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ : ℝ)
    (privateCoeff : Fin privateC → ℝ) (assembly : Fin f → ℝ) (k : Fin (f*f+f)) :
    table M nodes anchors r σ privateCoeff assembly (assemblySlot k) =
      MeanGaussianSetup.table assembly k := by
  simp [table, assemblySlot]

@[simp] theorem table_direct (M : MeanGeometry order) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ : ℝ)
    (privateCoeff : Fin privateC → ℝ) (assembly : Fin f → ℝ) (k : Fin (n*a)) :
    table M nodes anchors r σ privateCoeff assembly (directSlot k) =
      PrefixDirect.table M nodes anchors r σ k := by
  simp [table, directSlot]

end AcceleratedLogConcave.Oracle.PrefixPublicTable
