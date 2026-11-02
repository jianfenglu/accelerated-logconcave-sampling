import AcceleratedLogConcave.Tensor.NetworkScorePartition
import AcceleratedLogConcave.Tensor.PolynomialClosure

/-! Literal score-route tensor coordinates, retaining all summed derivative ports. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction
variable {n D : ℕ} {Edge Name : Type*} [Fintype Edge] {σ : CoefficientSignature Name}
variable (g : Graph n Edge) (p : Fin (n+1))

def decoratedScoreRouteTensor {r j : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (i : Fin (r+2))
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+1)))
    (route : List (Fin j) × List (Fin j)) (x : EuclideanSpace ℝ (Fin D)) : Coeff (g.Slot p) D :=
  WithLp.toLp 2 (fun a => ∑ k : Fin D,
    partialAlong (fun u => coordinateDirection D (a (g.decoratedLabelSlot p e u))) route.1
      (dir (coordinateDirection D k) H) x *
    partialAlong (fun u => coordinateDirection D (a (g.decoratedLabelSlot p e u))) route.2
      (sectionValue ρ H E (Fin.insertNth i k (fun u => a (g.adjointFreeSlot p e u)))) x)

variable (part : g.Slot p → Bool)
    (hI : ∃ q : g.InPort p, part (.inl q) = false)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true)

def decoratedScoreChildTensor {L : Type*} (b : Bool)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (labelSlot : L → g.Slot p) (J : List L)
    (x : EuclideanSpace ℝ (Fin D)) :
    Coeff ((g.replaceVertex p part).Slot (splitVertex p p b)) D :=
  WithLp.toLp 2 (fun a =>
    partialAlong (g.childCoordinateDirection p part hI hO b labelSlot a) J
      (dir (coordinateDirection D (a (g.joiningChildSlot p part b))) H) x)

 theorem decoratedScoreChildTensor_value {L : Type*} (b : Bool)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (labelSlot : L → g.Slot p) (J : List L)
    (hlabels : ∀ u ∈ J, part (labelSlot u) = b)
    (x : EuclideanSpace ℝ (Fin D)) (c : Option Edge → Fin D) (k : Fin D) :
    g.decoratedScoreChildTensor p part hI hO b H labelSlot J x
      (Sum.elim (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) =
    partialAlong (fun u => coordinateDirection D (Sum.elim
      (fun q : g.InPort p => c q.val) (fun q : g.OutPort p => c q.val) (labelSlot u))) J
      (dir (coordinateDirection D k) H) x := by
  unfold decoratedScoreChildTensor
  change partialAlong _ J (dir (coordinateDirection D _) H) x = _
  have hjoin : Sum.elim (fun q => extendAssignment c k q.val)
      (fun q => extendAssignment c k q.val) (g.joiningChildSlot p part b) = k := by
    cases b <;> rfl
  rw [hjoin]
  conv_lhs => rw [PolynomialClosure.partialAlong_map_id]
  conv_rhs => rw [PolynomialClosure.partialAlong_map_id]
  have hm := List.map_congr_left (l := J) (fun u hu =>
    g.childCoordinateDirection_value p part hI hO b labelSlot u (hlabels u hu) c k)
  rw [hm]

 theorem decoratedScoreRoute_children_value {r j : ℕ} (b : Bool)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (i : Fin (r+2))
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+1))) (route : List (Fin j) × List (Fin j))
    (hscore : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hop : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (hfree : ∀ u, part (g.adjointFreeSlot p e u) = !b)
    (x : EuclideanSpace ℝ (Fin D)) (c : Option Edge → Fin D) :
    g.decoratedScoreRouteTensor p ρ H E i e route x
      (Sum.elim (fun q => c q.val) (fun q => c q.val)) = ∑ k : Fin D,
    g.decoratedScoreChildTensor p part hI hO b H (g.decoratedLabelSlot p e) route.1 x
      (Sum.elim (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) *
    g.decoratedContractChildTensor p part hI hO (!b) ρ H E i
      (g.adjointFreeSlot p e) hfree (g.decoratedLabelSlot p e) route.2 x
      (Sum.elim (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) := by
  simp_rw [g.decoratedScoreChildTensor_value p part hI hO b H (g.decoratedLabelSlot p e) route.1 hscore]
  simp_rw [g.decoratedContractChildTensor_value p part hI hO (!b) ρ H E i
    (g.adjointFreeSlot p e) hfree (g.decoratedLabelSlot p e) route.2 hop]
  rfl
end AcceleratedLogConcave.Tensor.Ordered.Graph
