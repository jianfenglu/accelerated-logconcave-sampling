import AcceleratedLogConcave.Oracle.NoisyLayer
import AcceleratedLogConcave.Oracle.CovarianceSetup
import AcceleratedLogConcave.Oracle.Termination
import AcceleratedLogConcave.Oracle.RetainedMeanCorrection

/-!
Literal source scalar schedule and disjoint table layout for one nonterminal
mean. No certificate (b, s) is a program input. Active-final children are kept
in the layout even when their auxiliary shift vanishes. This module does not
yet construct the recursive children or assert their query-shift invariants.
-/
noncomputable section
namespace AcceleratedLogConcave.Oracle.RecursiveMeanPublicTable
open NoisyLayer TapeLowering AffineLowering Precision
open scoped BigOperators

def centerNoise (r R Ds : ℝ) : ℝ := r*R/(2*Real.sqrt 5*Ds)
def finalNoise (sigma : ℝ) : ℝ := Real.sqrt 3*sigma/2
def finalWidth (R sigma : ℝ) : ℝ := R*finalNoise sigma/2
def mainWidth (n : ℕ) (r R Ds A : ℝ) : ℝ :=
  CovarianceSetup.sigma n (centerNoise r R Ds) A

/-- Every active final supplier gets the source q-t index. -/
def finalIndex (q t : ℝ) : CallIndex := .mean (q-t)
/-- Every main layer supplier gets q-1/4, independently of layer number. -/
def mainIndex (q : ℝ) : CallIndex := .mean (q-1/4)
def privateIndex (q : ℝ) : CallIndex := .sampling (q-1/4)

theorem final_is_workChild (q t : ℝ) (hq : (1/2:ℝ) < q) :
    WorkChild t (finalIndex q t) (.mean q) :=
  ⟨.activeFinal, .activeFinal hq⟩
theorem main_is_workChild (q t : ℝ) (hq : (1/2:ℝ) < q) :
    WorkChild t (mainIndex q) (.mean q) :=
  ⟨.mainLayer, .mainLayer hq⟩
theorem private_is_workChild (q t : ℝ) (hq : (1/2:ℝ) < q) :
    WorkChild t (privateIndex q) (.mean q) :=
  ⟨.privateAnchor, .privateAnchor hq⟩

/-- Each actual final child contributes its entire transform and coefficient table. -/
def finalSize (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point) : ℕ :=
  ∑ i, childSize (pf i)

def finalTable (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (T : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks →
      Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (cf i) → ℝ) : Fin (finalSize cf pf) → ℝ :=
  fun k => let pair := finSigmaFinEquiv.symm k
           matrixTable (T pair.1) (coeff pair.1) pair.2

def finalSlot (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (i : Fin m) (j : Fin (childSize (pf i))) : Fin (finalSize cf pf) :=
  finSigmaFinEquiv ⟨i,j⟩

theorem finalTable_child (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (T : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks →
      Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (cf i) → ℝ) (i : Fin m) (j : Fin (childSize (pf i))) :
    finalTable cf pf T coeff (finalSlot cf pf i j) = matrixTable (T i) (coeff i) j := by
  simp only [finalTable, finalSlot]
  erw [Equiv.symm_apply_apply]

/-- One initialization scalar, full main-layer table, all active-final child
transforms/tables, and the original-input retained correction coefficients. -/
def table (rho : ℝ) (layer : Fin L → ℝ) (final : Fin F → ℝ)
    (sigma : ℝ) (omega width : Fin m → ℝ) :
    Fin (1+(L+(F+(1+(m+m))))) → ℝ :=
  Fin.append (fun _ : Fin 1 => rho)
    (Fin.append layer (Fin.append final (RetainedMeanCorrection.table sigma omega width)))

def rhoSlot : Fin (1+(L+(F+(1+(m+m))))) := Fin.castAdd _ (0 : Fin 1)
def layerSlot (j : Fin L) : Fin (1+(L+(F+(1+(m+m))))) :=
  Fin.natAdd 1 (Fin.castAdd _ j)
def activeFinalSlot (j : Fin F) : Fin (1+(L+(F+(1+(m+m))))) :=
  Fin.natAdd 1 (Fin.natAdd L (Fin.castAdd _ j))
def correctionSlot (j : Fin (1+(m+m))) : Fin (1+(L+(F+(1+(m+m))))) :=
  Fin.natAdd 1 (Fin.natAdd L (Fin.natAdd F j))

@[simp] theorem table_rho (rho : ℝ) (layer : Fin L → ℝ) (final : Fin F → ℝ)
    (sigma : ℝ) (omega width : Fin m → ℝ) :
    table rho layer final sigma omega width rhoSlot = rho := by
  simp [table, rhoSlot]
@[simp] theorem table_layer (rho : ℝ) (layer : Fin L → ℝ) (final : Fin F → ℝ)
    (sigma : ℝ) (omega width : Fin m → ℝ) (j : Fin L) :
    table rho layer final sigma omega width (layerSlot j) = layer j := by
  simp [table, layerSlot]
@[simp] theorem table_final (rho : ℝ) (layer : Fin L → ℝ) (final : Fin F → ℝ)
    (sigma : ℝ) (omega width : Fin m → ℝ) (j : Fin F) :
    table rho layer final sigma omega width (activeFinalSlot j) = final j := by
  simp [table, activeFinalSlot]
@[simp] theorem table_correction (rho : ℝ) (layer : Fin L → ℝ) (final : Fin F → ℝ)
    (sigma : ℝ) (omega width : Fin m → ℝ) (j : Fin (1+(m+m))) :
    table rho layer final sigma omega width (correctionSlot j) =
      RetainedMeanCorrection.table sigma omega width j := by
  simp [table, correctionSlot]


/-- Source-prescribed main layer: covariance roots are computed from public
scalar data and child shifts, never from the current random centers. -/
def sourceLayerTable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (A : CovarianceSetup.Mat n) (r R Ds rowBound : ℝ)
    (radius : Fin n → ℝ)
    (shift : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ) : Fin (publicSize c p) → ℝ :=
  let rho := centerNoise r R Ds
  layerTable c p A (CovarianceSetup.residualRoot A rho rowBound)
    (fun i => CovarianceSetup.childRoot rho (radius i) (shift i)) coeff

/-- Final suppliers use their own radius and shift, not a main-child substitute. -/
def sourceFinalTable (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (r R Ds : ℝ)
    (shift : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (cf i) → ℝ) : Fin (finalSize cf pf) → ℝ :=
  finalTable cf pf
    (fun i => CovarianceSetup.childRoot (centerNoise r R Ds) (r*R) (shift i)) coeff

/-- Distinct table regions cannot alias even if coefficient values coincide. -/
theorem layerSlot_ne_activeFinalSlot (i : Fin L) (j : Fin F) :
    layerSlot (F := F) (m := m) i ≠ activeFinalSlot (L := L) (m := m) j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [layerSlot, activeFinalSlot, Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

end AcceleratedLogConcave.Oracle.RecursiveMeanPublicTable
