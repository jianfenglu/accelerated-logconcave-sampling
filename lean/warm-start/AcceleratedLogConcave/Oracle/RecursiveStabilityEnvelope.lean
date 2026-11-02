import AcceleratedLogConcave.Oracle.FixedTapeStabilityGrowth
import AcceleratedLogConcave.Oracle.RecursiveExecutable
import AcceleratedLogConcave.Numerics.AffineBounds

/-! An explicit finite envelope on the literal recursive parameter updates.
Finite maxima are taken in NNReal, with zero for empty families. No smallness,
oracle outcome, probability law or existential constant enters the definition. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveExecutable
open Numerics.AffineGraph FixedTapeStability
open scoped BigOperators NNReal

/-- Exact finite maximum of two nonnegative families, including empty families. -/
def familyMax {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℝ≥0) (g : β → ℝ≥0) : ℝ≥0 :=
  max (Finset.univ.sup f) (Finset.univ.sup g)

theorem le_familyMax_left {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℝ≥0) (g : β → ℝ≥0) (i : α) : f i ≤ familyMax f g :=
  (Finset.le_sup (Finset.mem_univ i)).trans (le_max_left _ _)

theorem le_familyMax_right {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℝ≥0) (g : β → ℝ≥0) (i : β) : g i ≤ familyMax f g :=
  (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)

theorem familyMax_le_iff {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℝ≥0) (g : β → ℝ≥0) (K : ℝ≥0) :
    familyMax f g ≤ K ↔ (∀ i, f i ≤ K) ∧ (∀ i, g i ≤ K) := by
  simp only [familyMax,max_le_iff,Finset.sup_le_iff,Finset.mem_univ,true_implies]

@[simp] theorem familyMax_zero {α β : Type*} [Fintype α] [Fintype β] :
    familyMax (fun _ : α => 0) (fun _ : β => 0) = 0 := by
  apply le_antisymm _ bot_le
  exact (familyMax_le_iff _ _ 0).mpr ⟨fun _ => le_rfl, fun _ => le_rfl⟩

/-- The actual maximum absolute matrix row mass, not the schedule's upper bound. -/
def actualRowMass {m : ℕ} (M : MeanGeometry m) (r σ : ℝ) : ℝ≥0 :=
  Finset.univ.sup fun i : M.MeanNode =>
    ⟨∑ j, |M.matrix r σ i j|, Finset.sum_nonneg fun j _ => abs_nonneg (M.matrix r σ i j)⟩

theorem row_mass_le_actualRowMass {m : ℕ} (M : MeanGeometry m) (r σ : ℝ)
    (i : M.MeanNode) : (∑ j, |M.matrix r σ i j|) ≤ actualRowMass M r σ := by
  exact_mod_cast (Finset.le_sup (f := fun i : M.MeanNode =>
    (⟨∑ j, |M.matrix r σ i j|, Finset.sum_nonneg fun j _ => abs_nonneg (M.matrix r σ i j)⟩ : ℝ≥0))
    (Finset.mem_univ i))

theorem actualRowMass_le_iff {m : ℕ} (M : MeanGeometry m) (r σ : ℝ) (A : ℝ≥0) :
    actualRowMass M r σ ≤ A ↔ ∀ i : M.MeanNode, (∑ j, |M.matrix r σ i j|) ≤ A := by
  constructor
  · intro hA i
    exact (row_mass_le_actualRowMass M r σ i).trans hA
  · intro hA
    exact Finset.sup_le fun i _ => hA i

variable {m n ms ns : ℕ}

/-- Main and active-final mean envelopes at the exact public widths/precisions. -/
def meanChildEnvelope (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (Ds δ t w : ℝ) (K : ℝ → ℝ → ℝ → ℝ≥0) (r σ q : ℝ) : ℝ≥0 :=
  familyMax
    (fun i : Fin n => K (M.radius r (nodes i))
      (RecursiveMeanPublicTable.mainWidth n r M.R Ds
        (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) (q-1/4))
    (fun _ : Fin m => K (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t))

/-- Sampling main and final children both lose one quarter of precision. -/
def samplingChildEnvelope (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (Ds : ℝ) (K : ℝ → ℝ → ℝ → ℝ≥0) (r q : ℝ) : ℝ≥0 :=
  familyMax
    (fun i : Fin ns => K (S.radius r (snodes i))
      (RecursiveMeanPublicTable.mainWidth ns r S.R Ds (r^2)) (q-1/4))
    (fun i : Fin ns => K (S.radius r (snodes i))
      (SourceExecutableTables.samplingFinalWidth S r) (q-1/4))

variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (Ds δ t w : ℝ) (N : ℕ) (L : ℝ≥0)

/-- Fuel is a numerical truncation parameter. The later stability theorem requires
enough fuel for the actual precision rank. toNNReal only makes this definition
total at negative radii; its truncation disappears at the proved r >= 0 interface. -/
def stabilityEnvelope : ℕ → ℝ → ℝ → ℝ → ℝ≥0
  | 0, _, _, _ => L
  | fuel+1, r, σ, q => if q ≤ 1/2 then L else
      Real.toNNReal (meanGrowth N
        (meanChildEnvelope M nodes Ds δ t w (stabilityEnvelope fuel) r σ q)
        (samplingChildEnvelope S snodes Ds (stabilityEnvelope fuel) r q)
        r (backwardEnd M.R) (actualRowMass M r σ))

@[simp] theorem stabilityEnvelope_zero (r σ q : ℝ) :
    stabilityEnvelope M nodes S snodes Ds δ t w N L 0 r σ q = L := rfl

theorem stabilityEnvelope_of_terminal (fuel : ℕ) (r σ q : ℝ) (hq : q ≤ 1/2) :
    stabilityEnvelope M nodes S snodes Ds δ t w N L fuel r σ q = L := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [stabilityEnvelope,ite_eq_left hq]

theorem coe_stabilityEnvelope_succ (fuel : ℕ) (r σ q : ℝ) (hr : 0 ≤ r) (hq : 1/2 < q) :
    (stabilityEnvelope M nodes S snodes Ds δ t w N L (fuel+1) r σ q : ℝ) =
      meanGrowth N
        (meanChildEnvelope M nodes Ds δ t w
          (stabilityEnvelope M nodes S snodes Ds δ t w N L fuel) r σ q)
        (samplingChildEnvelope S snodes Ds
          (stabilityEnvelope M nodes S snodes Ds δ t w N L fuel) r q)
        r (backwardEnd M.R) (actualRowMass M r σ) := by
  rw [stabilityEnvelope,ite_eq_right (not_le.mpr hq)]
  exact Real.coe_toNNReal _ (meanGrowth_nonneg N (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    hr (NNReal.coe_nonneg _))

/-- A zero normalized terminal constant gives a zero envelope at every finite fuel. -/
theorem stabilityEnvelope_zero_oracle (fuel : ℕ) (r σ q : ℝ) :
    stabilityEnvelope M nodes S snodes Ds δ t w N 0 fuel r σ q = 0 := by
  induction fuel generalizing r σ q with
  | zero => rfl
  | succ fuel ih =>
      simp [stabilityEnvelope,meanChildEnvelope,samplingChildEnvelope,ih]

end AcceleratedLogConcave.Oracle.RecursiveExecutable
