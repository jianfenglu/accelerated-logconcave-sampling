import AcceleratedLogConcave.Tensor.NetworkContractState
import AcceleratedLogConcave.Tensor.NetworkSyntaxFamilyValue
import AcceleratedLogConcave.Tensor.NetworkContractChildValue

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {D n : ℕ} {Edge : Type*} [Fintype Edge]

theorem transportSyntaxAt_value (g : Graph n Edge) {v w : Fin (n+1)} (h : v = w)
    (P : g.SyntaxAt (σ := σ) v) (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (x : EuclideanSpace ℝ (Fin D))
    (c : Option Edge → Fin D) :
    g.pendingTensor w ρ H (transportSyntaxAt g h P).1 (transportSyntaxAt g h P).2 x
      (Sum.elim (fun q => c q.val) (fun q => c q.val)) =
    g.pendingTensor v ρ H P.1 P.2 x
      (Sum.elim (fun q => c q.val) (fun q => c q.val)) := by
  subst w
  rfl

theorem replacementFamily_replaceTensorAt (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool) (T : g.Tensors D) (C : Coeff (g.Slot p) D)
    (A : Coeff ((g.replaceVertex p part).Slot p.castSucc) D)
    (B : Coeff ((g.replaceVertex p part).Slot p.succ) D) :
    g.replacementFamily p part (g.replaceTensorAt p T C) A B =
      g.replacementFamily p part T A B := by
  funext w
  by_cases h₀ : w = p.castSucc
  · subst w; rw [replacementFamily_left, replacementFamily_left]
  by_cases h₁ : w = p.succ
  · subst w; rw [replacementFamily_right, replacementFamily_right]
  obtain ⟨v,hv,rfl⟩ := ((splitVertex_cover p w).resolve_left h₀).resolve_left h₁
  rw [replacementFamily_other g p part (g.replaceTensorAt p T C) A B v hv,
    replacementFamily_other g p part T A B v hv]
  unfold replacementOtherTensor
  rw [replaceTensorAt_other g p T C v hv]

namespace ContractState
variable {r s : ℕ} (node : NodeAddress) (E : Expr σ (r+2)) (F : Expr σ (s+2))
    (i : Fin (r+2)) (k : Fin (s+2)) (J : List LabelOrigin)
    (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.contract E F i k) J] ++ after))

theorem ofOrientation_value
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ routes (List.finRange J.length))
    (part : S.graph.Slot (parentVertex node E F i k J before after S) → Bool) (b : Bool)
    (hi : ∃ q : S.graph.InPort (parentVertex node E F i k J before after S), part (.inl q) = false)
    (ho : ∃ q : S.graph.OutPort (parentVertex node E F i k J before after S), part (.inr q) = true)
    (hg : (S.graph.replaceVertex (parentVertex node E F i k J before after S) part).Admissible)
    (hlf : ∀ u, part (S.graph.decoratedLeftFreeSlot (parentVertex node E F i k J before after S) (parentPorts node E F i k J before after S) u) = b)
    (hrf : ∀ u, part (S.graph.decoratedRightFreeSlot (parentVertex node E F i k J before after S) (parentPorts node E F i k J before after S) u) = !b)
    (hll : ∀ u ∈ route.1, part (S.graph.decoratedLabelSlot (parentVertex node E F i k J before after S) (parentPorts node E F i k J before after S) u) = b)
    (hrl : ∀ u ∈ route.2, part (S.graph.decoratedLabelSlot (parentVertex node E F i k J before after S) (parentPorts node E F i k J before after S) u) = !b)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    (ofOrientation node E F i k J before after S route hr part b hi ho hg hlf hrf hll hrl).value ρ H x =
      letI := S.edgeFintype
      S.graph.coordinateEval D (S.graph.replaceTensorAt (parentVertex node E F i k J before after S) (S.tensors ρ H x)
        (S.graph.decoratedContractRouteTensor (parentVertex node E F i k J before after S) ρ H E F i k (parentPorts node E F i k J before after S) route x)) := by
  let _ := S.edgeFintype
  let p := parentVertex node E F i k J before after S
  let e := parentPorts node E F i k J before after S
  cases b <;> simp only [ofOrientation]
  all_goals with_unfolding_all rw [SyntaxState.splitOccurrence_value]
  all_goals change ((S.graph.replaceVertex p part).coordinateEval D
      (S.graph.replacementFamily p part (S.tensors ρ H x) _ _) = _)
  all_goals with_unfolding_all rw [← replacementFamily_replaceTensorAt S.graph p part (S.tensors ρ H x)
    (S.graph.decoratedContractRouteTensor p ρ H E F i k e route x)]
  all_goals symm
  all_goals apply S.graph.coordinateEval_replacementFamily p part
  all_goals intro c
  all_goals unfold wireValue
  all_goals with_unfolding_all rw [replaceTensorAt_same]
  all_goals with_unfolding_all rw [S.graph.decoratedRoute_children_value p part hi ho _ ρ H E F i k e route hlf hrf hll hrl x c]
  all_goals apply Finset.sum_congr rfl
  all_goals intro z _
  all_goals erw [transportSyntaxAt_value, transportSyntaxAt_value,
    contractChildSyntax_tensor, contractChildSyntax_tensor]
  · erw [← S.graph.routeLeft_child_tensor p e route hr part false hi ho hlf hrf hll hrl ρ H E i x,
      ← S.graph.routeRight_child_tensor p e route hr part false hi ho hlf hrf hll hrl ρ H F k x]
    rfl
  · erw [← S.graph.routeRight_child_tensor p e route hr part true hi ho hlf hrf hll hrl ρ H F k x,
      ← S.graph.routeLeft_child_tensor p e route hr part true hi ho hlf hrf hll hrl ρ H E i x]
    exact mul_comm _ _

end ContractState
end AcceleratedLogConcave.Tensor.Ordered.Graph
