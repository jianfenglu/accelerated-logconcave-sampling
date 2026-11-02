import AcceleratedLogConcave.Tensor.NetworkScoreState
import AcceleratedLogConcave.Tensor.NetworkContractStateValue

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {D n : ℕ} {Edge Name : Type*} [Fintype Edge] {σ : CoefficientSignature Name}
variable (g : Graph n Edge) (p : Fin (n+1))

 theorem scoreRoute_child_tensor {j f : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ scoreRoutes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hi : ∃ q : g.InPort p, part (.inl q) = false)
    (ho : ∃ q : g.OutPort p, part (.inr q) = true)
    (hs : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hop : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (hf : ∀ u, part (g.adjointFreeSlot p e u) = !b)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (x : EuclideanSpace ℝ (Fin D)) :
    g.decoratedScoreChildTensor p part hi ho b H (g.decoratedLabelSlot p e) route.1 x =
    scorePortTensor (g.replaceVertex p part) (splitVertex p p b) H
      (g.scoreChildEquiv p part hi ho b (g.scoreRouteSelected p e route hr part b hs hop hf)).symm x := by
  ext c
  unfold decoratedScoreChildTensor scorePortTensor
  dsimp only
  rw [partialAlong_list_positions]
  congr 1
  funext u
  rw [childCoordinateDirection, dite_eq_left (hs _ (List.get_mem ..))]
  rfl

 theorem scoreOperand_child_tensor {j r : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+1)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ scoreRoutes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hi : ∃ q : g.InPort p, part (.inl q) = false)
    (ho : ∃ q : g.OutPort p, part (.inr q) = true)
    (hs : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hop : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (hf : ∀ u, part (g.adjointFreeSlot p e u) = !b)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (i : Fin (r+2)) (x : EuclideanSpace ℝ (Fin D)) :
    g.decoratedContractChildTensor p part hi ho (!b) ρ H E i
      (g.adjointFreeSlot p e) hf (g.decoratedLabelSlot p e) route.2 x =
    (g.replaceVertex p part).decoratedSectionTensor (splitVertex p p (!b)) ρ H E
      (g.decoratedOperandEquiv p part hi ho (!b) i
        (g.scoreOperandSelected p e route hr part b hs hop hf)).symm x := by
  let selected := g.scoreOperandSelected p e route hr part b hs hop hf
  calc
    _ = g.decoratedContractChildTensor p part hi ho (!b) ρ H E i
        (fun u => (selected (.inr u)).val) (fun u => (selected (.inr u)).property)
        (fun u => (selected (.inl u)).val) (List.finRange route.2.length) x := by
      ext c
      unfold decoratedContractChildTensor
      dsimp only
      rw [partialAlong_list_positions]
      rfl
    _ = _ := g.decoratedOperandEquiv_tensor p part hi ho (!b) i selected ρ H E x

namespace ScoreState
variable {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2)) (i : Fin (r+2))
    (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))

theorem ofOrientation_value
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ scoreRoutes (List.finRange J.length))
    (part : S.graph.Slot (parentVertex node E i J before after S) → Bool) (b : Bool)
    (hi : ∃ q : S.graph.InPort (parentVertex node E i J before after S), part (.inl q) = false)
    (ho : ∃ q : S.graph.OutPort (parentVertex node E i J before after S), part (.inr q) = true)
    (hg : (S.graph.replaceVertex (parentVertex node E i J before after S) part).Admissible)
    (hscore : ∀ u ∈ route.1, part (S.graph.decoratedLabelSlot (parentVertex node E i J before after S)
      (parentPorts node E i J before after S) u) = b)
    (hop : ∀ u ∈ route.2, part (S.graph.decoratedLabelSlot (parentVertex node E i J before after S)
      (parentPorts node E i J before after S) u) = !b)
    (hfree : ∀ u, part (S.graph.adjointFreeSlot (parentVertex node E i J before after S)
      (parentPorts node E i J before after S) u) = !b)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    (ofOrientation node E i J before after S hs hinv route hr part b hi ho hg hscore hop hfree).value ρ H x =
      letI := S.edgeFintype
      S.graph.coordinateEval D (S.graph.replaceTensorAt (parentVertex node E i J before after S)
        (S.tensors ρ H x) (S.graph.decoratedScoreRouteTensor (parentVertex node E i J before after S)
          ρ H E i (parentPorts node E i J before after S) route x)) := by
  let _ := S.edgeFintype
  let p := parentVertex node E i J before after S
  let e := parentPorts node E i J before after S
  cases b <;> simp only [ofOrientation]
  all_goals with_unfolding_all rw [SyntaxState.splitOccurrenceNewWire_value]
  all_goals change ((S.graph.replaceVertex p part).coordinateEval D
    (S.graph.replacementFamily p part (S.tensors ρ H x) _ _) = _)
  all_goals with_unfolding_all rw [←replacementFamily_replaceTensorAt S.graph p part (S.tensors ρ H x)
    (S.graph.decoratedScoreRouteTensor p ρ H E i e route x)]
  all_goals symm
  all_goals apply S.graph.coordinateEval_replacementFamily p part
  all_goals intro c
  all_goals unfold wireValue
  all_goals with_unfolding_all rw [replaceTensorAt_same]
  all_goals with_unfolding_all rw [S.graph.decoratedScoreRoute_children_value p part hi ho _
    ρ H E i e route hscore hop hfree x c]
  all_goals apply Finset.sum_congr rfl
  all_goals intro z _
  all_goals erw [transportSyntaxAt_value,transportSyntaxAt_value]
  · erw [scoreChildSyntax_tensor,contractChildSyntax_tensor]
    erw [←S.graph.scoreRoute_child_tensor p e route hr part false hi ho hscore hop hfree H x,
      ←S.graph.scoreOperand_child_tensor p e route hr part false hi ho hscore hop hfree ρ H E i x]
    rfl
  · erw [contractChildSyntax_tensor,scoreChildSyntax_tensor]
    erw [←S.graph.scoreOperand_child_tensor p e route hr part true hi ho hscore hop hfree ρ H E i x,
      ←S.graph.scoreRoute_child_tensor p e route hr part true hi ho hscore hop hfree H x]
    exact mul_comm _ _

end ScoreState

end AcceleratedLogConcave.Tensor.Ordered.Graph
