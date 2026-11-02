import AcceleratedLogConcave.Tensor.NetworkAddedEdge
import AcceleratedLogConcave.Tensor.CoordinateReduction

/-! Deterministic recipient graphs with literal directional-derivative endpoints. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction
variable {n D : ℕ} {Edge : Type*} [Fintype Edge]
variable (g : Graph n Edge) (p q : Fin (n+1)) (hne : p ≠ q)

omit [Fintype Edge] in
def recipientGraph : Graph n (Option Edge) :=
  if h : p < q then g.addOrderedEdge p q h
  else g.addOrderedEdge q p (by omega)

omit [Fintype Edge] in
theorem recipientGraph_admissible (hg : g.Admissible) : (g.recipientGraph p q hne).Admissible := by
  unfold recipientGraph
  split_ifs with h
  · exact g.addOrderedEdge_admissible hg p q h
  · exact g.addOrderedEdge_admissible hg q p _

private def transportFamily {g h : Graph n (Option Edge)} (e : g = h)
    (T : g.Tensors D) : h.Tensors D := e ▸ T

private theorem coordinateEval_transportFamily {g h : Graph n (Option Edge)} (e : g = h)
    (T : g.Tensors D) : h.coordinateEval D (transportFamily e T) = g.coordinateEval D T := by
  subst h
  rfl

def recipientPairFamily (T : g.Tensors D) (A : Fin D → Coeff (g.Slot p) D)
    (B : Fin D → Coeff (g.Slot q) D) : (g.recipientGraph p q hne).Tensors D :=
  if h : p < q then transportFamily (by simp [recipientGraph, h]) (g.addedPairFamily p q h T A B)
  else transportFamily (by simp [recipientGraph, h]) (g.addedPairFamily q p (by omega) T B A)

theorem coordinateEval_recipientPairFamily (T : g.Tensors D)
    (A : Fin D → Coeff (g.Slot p) D) (B : Fin D → Coeff (g.Slot q) D) :
    (g.recipientGraph p q hne).coordinateEval D (g.recipientPairFamily p q hne T A B) =
      ∑ c : (Option Edge → Fin D), ∑ k : Fin D,
        A k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) *
        B k (Sum.elim (fun s : g.InPort q => c s.val) (fun s : g.OutPort q => c s.val)) *
        ∏ v ∈ (Finset.univ.erase p).erase q, g.wireValue T c v := by
  unfold recipientPairFamily
  split_ifs with h
  · rw [coordinateEval_transportFamily]
    exact g.coordinateEval_addedPairFamily p q h T A B
  · rw [coordinateEval_transportFamily, g.coordinateEval_addedPairFamily q p]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.erase_right_comm]
    ring

/-- No recipient derivative is postulated: it is the actual scalar coordinate derivative. -/
def recipientDerivativeTensor (T : EuclideanSpace ℝ (Fin D) → g.Tensors D)
    (x : EuclideanSpace ℝ (Fin D)) (k : Fin D) : Coeff (g.Slot q) D :=
  WithLp.toLp 2 (fun a => dir (coordinateDirection D k) (fun y => T y q a) x)

 theorem recipientDerivativeTensor_value (T : EuclideanSpace ℝ (Fin D) → g.Tensors D)
    (x : EuclideanSpace ℝ (Fin D)) (k : Fin D) (c : Option Edge → Fin D) :
    g.recipientDerivativeTensor q T x k
      (Sum.elim (fun s : g.InPort q => c s.val) (fun s : g.OutPort q => c s.val)) =
    dir (coordinateDirection D k) (fun y => g.wireValue (T y) c q) x := rfl

/-- Actual graph realization of one principal-IBP recipient branch. The graph is fixed
by occurrence indices, independent of the spatial integration point. -/
def principalRecipientFamily (T : EuclideanSpace ℝ (Fin D) → g.Tensors D)
    (A : EuclideanSpace ℝ (Fin D) → Fin D → Coeff (g.Slot p) D)
    (x : EuclideanSpace ℝ (Fin D)) : (g.recipientGraph p q hne).Tensors D :=
  g.recipientPairFamily p q hne (T x) (A x) (g.recipientDerivativeTensor q T x)

theorem coordinateEval_principalRecipientFamily (T : EuclideanSpace ℝ (Fin D) → g.Tensors D)
    (A : EuclideanSpace ℝ (Fin D) → Fin D → Coeff (g.Slot p) D)
    (x : EuclideanSpace ℝ (Fin D)) :
    (g.recipientGraph p q hne).coordinateEval D (g.principalRecipientFamily p q hne T A x) =
      ∑ c : (Option Edge → Fin D), ∑ k : Fin D,
        A x k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) *
        dir (coordinateDirection D k) (fun y => g.wireValue (T y) c q) x *
        ∏ v ∈ (Finset.univ.erase p).erase q, g.wireValue (T x) c v := by
  unfold principalRecipientFamily
  rw [g.coordinateEval_recipientPairFamily p q hne]
  rfl

 theorem integral_coordinateEval_principalRecipientFamily
    (μ : Measure (EuclideanSpace ℝ (Fin D))) (T : EuclideanSpace ℝ (Fin D) → g.Tensors D)
    (A : EuclideanSpace ℝ (Fin D) → Fin D → Coeff (g.Slot p) D)
    (hterms : ∀ c : (Option Edge → Fin D), ∀ k : Fin D,
      Integrable (fun x =>
        A x k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) *
        dir (coordinateDirection D k) (fun y => g.wireValue (T y) c q) x *
        ∏ v ∈ (Finset.univ.erase p).erase q, g.wireValue (T x) c v) μ) :
    (∫ x, (g.recipientGraph p q hne).coordinateEval D (g.principalRecipientFamily p q hne T A x) ∂μ) =
      ∑ c : (Option Edge → Fin D), ∑ k : Fin D, ∫ x,
        A x k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) *
        dir (coordinateDirection D k) (fun y => g.wireValue (T y) c q) x *
        ∏ v ∈ (Finset.univ.erase p).erase q, g.wireValue (T x) c v ∂μ := by
  simp_rw [g.coordinateEval_principalRecipientFamily p q hne]
  rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ (fun k _ => hterms c k))]
  exact Finset.sum_congr rfl (fun c _ => integral_finsetSum _ (fun k _ => hterms c k))
end AcceleratedLogConcave.Tensor.Ordered.Graph
