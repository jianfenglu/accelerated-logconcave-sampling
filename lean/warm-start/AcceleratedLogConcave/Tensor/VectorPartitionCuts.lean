import AcceleratedLogConcave.Tensor.ActualPartitionTree
import AcceleratedLogConcave.Tensor.ActualCompositionBudget
import AcceleratedLogConcave.Analysis.OrderedSpatialComposition

/-!

-/
noncomputable section
open scoped BigOperators Classical ContDiff
namespace AcceleratedLogConcave.Tensor.ActualPartitionTree
open EdgeClosure ActualCoefficient
open AcceleratedLogConcave.Analysis.SpatialPartition
variable {D n : ℕ}

def vectorPartitionChart (c : OrderedFinpartition n) :
    ((Σ i : Fin c.length, Fin (c.partSize i)) ⊕ Unit) ≃ (Fin n ⊕ Unit) :=
  Equiv.sumCongr c.equivSigma (Equiv.refl Unit)

@[simp] theorem vectorPartitionChart_leaf (c : OrderedFinpartition n)
    (i : Fin c.length) (j : Fin (c.partSize i)) :
    vectorPartitionChart c (.inl ⟨i,j⟩) = .inl (c.emb i j) := rfl

@[simp] theorem vectorPartitionChart_output (c : OrderedFinpartition n) :
    vectorPartitionChart c (.inr ()) = .inr () := rfl

 theorem vector_partition_tree_eq_actual (c : OrderedFinpartition n)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Space D) (Space D))
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Space D) (Space D)) :
    relabel D (vectorPartitionChart c)
      (starCoeff (fun i => Fin (c.partSize i)) T
        (fun a : Unit → Fin D => innerSL ℝ (basis D (a ()))) V) =
      vectorCoeff (c.compAlongOrderedFinpartition T V) := by
  ext a
  rfl

/-- The generic star induction applies with G=Space D and C=Unit. It is NOT
an application of the operator-root consumer or a rank-one norm assertion. -/
theorem vector_partition_allProper (c : OrderedFinpartition n)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Space D) (Space D))
    (V : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Space D) (Space D))
    (CT : ℝ) (CV : Fin c.length → ℝ) (hCT : 0 ≤ CT) (hCV : ∀ i, 0 ≤ CV i)
    (hT : AllProper D (vectorCoeff T) CT)
    (hV : ∀ i, AllProper D (vectorCoeff (V i)) (CV i)) :
    AllProper D (vectorCoeff (c.compAlongOrderedFinpartition T V))
      (CT * ∏ i, CV i) := by
  let : ∀ i : Fin c.length, Nonempty (Fin (c.partSize i)) :=
    fun i => ⟨⟨0, c.partSize_pos i⟩⟩
  have h := (starCoeff_allProper (fun i => Fin (c.partSize i)) T
    (fun a : Unit → Fin D => innerSL ℝ (basis D (a ()))) V
    CT CV hCT hCV hT hV).relabel (vectorPartitionChart c)
  rwa [vector_partition_tree_eq_actual] at h

/-- Linearity here is finite-dimensional coefficient linearity, not an HS estimate. -/
theorem vectorCoeff_finset_sum {I : Type*} [DecidableEq I] (s : Finset I)
    (T : I → ContinuousMultilinearMap ℝ (fun _ : Fin n => Space D) (Space D)) :
    vectorCoeff (∑ i ∈ s, T i) = ∑ i ∈ s, vectorCoeff (T i) := by
  ext a
  rw [coeff_finset_sum_apply]
  change inner ℝ (basis D (a (.inr ())))
    ((∑ i ∈ s, T i) (fun j => basis D (a (.inl j)))) = _
  simp only [sum_apply, inner_sum]
  rfl

/-- Actual forcing uses only positive branches strictly below n. No highest
jet bound, symmetry, distinct-coordinate premise or directional norm appears. -/
theorem spatialForcing_allProper (g f : Space D → Space D) (y : Space D)
    (n : ℕ) (hn : 0 < n) (A P : ℕ → ℝ)
    (hA : ∀ k, 0 ≤ A k) (hP : ∀ k, 0 ≤ P k)
    (hroot : ∀ k, 2 ≤ k → k ≤ n →
      AllProper D (vectorCoeff (iteratedFDeriv ℝ k g (f y))) (A k))
    (hbranch : ∀ j, 1 ≤ j → j < n →
      AllProper D (vectorCoeff (iteratedFDeriv ℝ j f y)) (P j)) :
    AllProper D (vectorCoeff (spatialForcing g f y n hn))
      (∑ c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase
        (OrderedFinpartition.oneBlock n hn), A c.length * ∏ i, P (c.partSize i)) := by
  let s := (Finset.univ : Finset (OrderedFinpartition n)).erase
    (OrderedFinpartition.oneBlock n hn)
  change AllProper D (vectorCoeff (∑ c ∈ s, spatialTerm g f y c)) _
  rw [vectorCoeff_finset_sum]
  intro S hS
  change ‖splitOperatorEquiv D S (∑ c ∈ s, vectorCoeff (spatialTerm g f y c))‖ ≤ _
  rw [map_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c hc
  have hk := spatialForcing_outer_order n hn c hc
  exact vector_partition_allProper c _ _ (A c.length) (fun i => P (c.partSize i))
    (hA _) (fun i => hP _) (hroot _ hk.1 hk.2)
    (fun i => let hj := spatialForcing_support n hn c hc i
      hbranch _ hj.1 hj.2) S hS

/-- n=1 forcing is genuinely zero; no arbitrary empty-family estimate is used. -/
theorem spatialForcing_one (g f : Space D → Space D) (y : Space D) :
    spatialForcing g f y 1 (by omega) = 0 := by
  apply Finset.sum_eq_zero
  intro c hc
  have hk := spatialForcing_outer_order 1 (by omega) c hc
  omega

end AcceleratedLogConcave.Tensor.ActualPartitionTree
