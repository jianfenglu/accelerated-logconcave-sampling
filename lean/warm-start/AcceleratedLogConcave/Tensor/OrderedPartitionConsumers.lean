import AcceleratedLogConcave.Tensor.ActualPartitionTree

/-!

-/
noncomputable section
open scoped BigOperators Classical ContDiff
namespace AcceleratedLogConcave.Tensor.ActualPartitionTree
open EdgeClosure ActualCoefficient
variable {D n : ℕ}

/-- Leaves follow c.emb EXACTLY; then reassociate both ordinary operator slots. -/
def partitionChart (c : OrderedFinpartition n) :
    ((Σ i : Fin c.length, Fin (c.partSize i)) ⊕ (Unit ⊕ Unit)) ≃
      ((Fin n ⊕ Unit) ⊕ Unit) :=
  (Equiv.sumCongr c.equivSigma (Equiv.refl (Unit ⊕ Unit))).trans
    (Equiv.sumAssoc (Fin n) Unit Unit).symm

/-- Three source-fidelity checks expose the actual chart orientation. -/
@[simp] theorem partitionChart_leaf (c : OrderedFinpartition n)
    (i : Fin c.length) (j : Fin (c.partSize i)) :
    partitionChart c (.inl ⟨i,j⟩) = .inl (.inl (c.emb i j)) := rfl

@[simp] theorem partitionChart_input (c : OrderedFinpartition n) :
    partitionChart c (.inr (.inl ())) = .inl (.inr ()) := rfl

@[simp] theorem partitionChart_output (c : OrderedFinpartition n) :
    partitionChart c (.inr (.inr ())) = .inr () := rfl

/-- The final contracted tree is the literal c.compAlongOrderedFinpartition,
not an abstract tensor with a matching cardinality. -/
theorem partition_tree_eq_actual (c : OrderedFinpartition n)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Space D)
      (Space D →L[ℝ] Space D))
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Space D)
      (Space D)) :
    relabel D (partitionChart c)
      (starCoeff (fun i => Fin (c.partSize i)) T operatorReadout V) =
      operatorCoeff (c.compAlongOrderedFinpartition T V) := by
  ext a
  rfl

/-- Explicit chained statement from successive attachments to the actual map. -/
theorem partition_partial_full_eq_actual (c : OrderedFinpartition n)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Space D)
      (Space D →L[ℝ] Space D))
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Space D)
      (Space D)) :
    relabel D (partitionChart c)
      (relabel D (fullChart (fun i => Fin (c.partSize i)))
        (partialCoeff (fun i => Fin (c.partSize i)) T operatorReadout V Finset.univ)) =
      operatorCoeff (c.compAlongOrderedFinpartition T V) := by
  rw [full_eq_star, partition_tree_eq_actual]

/-- Literal complete basis sum for ONE actual partition, preserving c.emb.
Both ordinary root input and root output remain in the external assignment. -/
theorem partition_coefficient_basis_sum (c : OrderedFinpartition n)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Space D)
      (Space D →L[ℝ] Space D))
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Space D)
      (Space D))
    (a : ((Fin n ⊕ Unit) ⊕ Unit) → Fin D) :
    operatorCoeff (c.compAlongOrderedFinpartition T V) a =
      ∑ w : Fin c.length → Fin D,
        (∏ i, inner ℝ (basis D (w i))
          (V i (fun j => basis D (a (.inl (.inl (c.emb i j))))))) *
        inner ℝ (basis D (a (.inr ())))
          ((T (fun i => basis D (w i))) (basis D (a (.inl (.inr ()))))) := by
  rw [← partition_tree_eq_actual]
  exact starCoeff_basis_sum (fun i => Fin (c.partSize i)) T operatorReadout V
    (a ∘ partitionChart c)

/-- Every positive branch has a nonempty exterior; the root retains TWO slots.
This is the desired partition-level all-proper rectangular product budget. -/
theorem partition_allProper (c : OrderedFinpartition n)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Space D)
      (Space D →L[ℝ] Space D))
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Space D)
      (Space D))
    (CT : ℝ) (CV : Fin c.length → ℝ) (hCT : 0 ≤ CT) (hCV : ∀ i, 0 ≤ CV i)
    (hT : AllProper D (operatorCoeff T) CT)
    (hV : ∀ i, AllProper D (vectorCoeff (V i)) (CV i)) :
    AllProper D (operatorCoeff (c.compAlongOrderedFinpartition T V))
      (CT * ∏ i, CV i) := by
  let : ∀ i : Fin c.length, Nonempty (Fin (c.partSize i)) :=
    fun i => ⟨⟨0, c.partSize_pos i⟩⟩
  have hroot : AllProper D (mapCoeff T operatorReadout) CT := by
    rw [← operatorCoeff_relabel]
    exact hT.relabel (Equiv.sumAssoc (Fin c.length) Unit Unit)
  have h := (starCoeff_allProper (fun i => Fin (c.partSize i))
    T operatorReadout V CT CV hCT hCV hroot hV).relabel (partitionChart c)
  rwa [partition_tree_eq_actual] at h

/-- The conclusion is explicitly a rectangular OPERATOR norm, not an HS or
multilinear directional norm. No choice of row/column orientation is assumed. -/
theorem partition_splitNorm_le (c : OrderedFinpartition n)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Space D)
      (Space D →L[ℝ] Space D))
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Space D)
      (Space D))
    (CT : ℝ) (CV : Fin c.length → ℝ) (hCT : 0 ≤ CT) (hCV : ∀ i, 0 ≤ CV i)
    (hT : AllProper D (operatorCoeff T) CT)
    (hV : ∀ i, AllProper D (vectorCoeff (V i)) (CV i))
    (S : Finset ((Fin n ⊕ Unit) ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (operatorCoeff (c.compAlongOrderedFinpartition T V)) ≤
      CT * ∏ i, CV i :=
  partition_allProper c T V CT CV hCT hCV hT hV S hS

/-- Actual U(Y) partition jets: no substitute formal jet tower is introduced.
Endpoint jet budgets are still required and must come from analytic suppliers. -/
theorem actual_composition_partition_allProper
    (U : Space D → (Space D →L[ℝ] Space D)) (Y : Space D → Space D)
    (y : Space D) (c : OrderedFinpartition n)
    (CT : ℝ) (CV : Fin c.length → ℝ) (hCT : 0 ≤ CT) (hCV : ∀ i, 0 ≤ CV i)
    (hT : AllProper D (operatorCoeff (iteratedFDeriv ℝ c.length U (Y y))) CT)
    (hV : ∀ i, AllProper D (vectorCoeff (iteratedFDeriv ℝ (c.partSize i) Y y)) (CV i)) :
    AllProper D (operatorCoeff (c.compAlongOrderedFinpartition
      (iteratedFDeriv ℝ c.length U (Y y))
      (fun i => iteratedFDeriv ℝ (c.partSize i) Y y))) (CT * ∏ i, CV i) :=
  partition_allProper c _ _ CT CV hCT hCV hT hV

/-- The empty ordered partition is unique, including at D=0. -/
theorem zero_partition_unique (c : OrderedFinpartition 0) : c = default :=
  Subsingleton.elim _ _

/-- Empty branch index assignments have ONE member even when D=0. -/
theorem zero_internal_assignment_card (D : ℕ) : Fintype.card (Fin 0 → Fin D) = 1 := by
  simp

/-- n=0 does not drop ordinary input/output: the coefficient stays rank two.
The branch family is empty, so no vector rank-one bound is requested. -/
theorem zero_partition_allProper (c : OrderedFinpartition 0)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Space D)
      (Space D →L[ℝ] Space D))
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Space D)
      (Space D))
    (CT : ℝ) (hCT : 0 ≤ CT) (hT : AllProper D (operatorCoeff T) CT) :
    AllProper D (operatorCoeff (c.compAlongOrderedFinpartition T V)) CT := by
  have hlen : c.length = 0 := by have := c.length_le; omega
  have hV : ∀ i, AllProper D (vectorCoeff (V i)) (1 : ℝ) := by
    intro i
    have hi := i.isLt
    omega
  simpa using partition_allProper c T V CT (fun _ => 1) hCT
    (fun _ => zero_le_one) hT hV

end AcceleratedLogConcave.Tensor.ActualPartitionTree
