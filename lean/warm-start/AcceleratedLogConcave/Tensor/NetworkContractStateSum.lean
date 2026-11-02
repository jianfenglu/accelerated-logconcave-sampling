import AcceleratedLogConcave.Tensor.NetworkContractStateValue

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

namespace SyntaxState
variable {s : List (TaggedPending σ)} (S : SyntaxState s)
theorem formulaPorts_tensor {D r : ℕ} (v : Fin (S.n+1)) (a : NodeAddress)
    (E : Expr σ r) (J : List LabelOrigin) (h : S.pending v = .formula a E J)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    letI := S.edgeFintype
    S.tensors ρ H x v = S.graph.decoratedSectionTensor v ρ H E (S.formulaPorts v a E J h) x := by
  let _ := S.edgeFintype
  have gen (q : TaggedPending σ) (e : S.graph.Slot v ≃ pendingPorts q)
      (hq : q = .formula a E J) :
      S.graph.pendingTensor v ρ H q e x = S.graph.decoratedSectionTensor v ρ H E
        (e.trans (Equiv.cast (congrArg pendingPorts hq))) x := by
    subst q
    rfl
  exact gen (S.pending v) (S.ports v) h
end SyntaxState

namespace ContractState
variable {r s : ℕ} (node : NodeAddress) (E : Expr σ (r+2)) (F : Expr σ (s+2))
    (i : Fin (r+2)) (k : Fin (s+2)) (J : List LabelOrigin)
    (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.contract E F i k) J] ++ after))


/-- The graph and all syntax data are chosen before evaluating at a spatial point. -/
def routeState
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ routes (List.finRange J.length)) :
    SyntaxState (before ++
      [.formula (node.child false) E (route.1.map J.get),
       .formula (node.child true) F (route.2.map J.get)] ++ after) :=
  let h := S.graph.exists_decorated_orientation
    (parentVertex node E F i k J before after S) S.admissible
    (parentPorts node E F i k J before after S) route hr
  let part := Classical.choose h
  let b := Classical.choose (Classical.choose_spec h)
  let hs := Classical.choose_spec (Classical.choose_spec h)
  ofOrientation node E F i k J before after S route hr part b
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2

theorem routeState_value {D : ℕ}
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ routes (List.finRange J.length))
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    (routeState node E F i k J before after S route hr).value ρ H x =
      letI := S.edgeFintype
      S.graph.coordinateEval D (S.graph.replaceTensorAt
        (parentVertex node E F i k J before after S) (S.tensors ρ H x)
        (S.graph.decoratedContractRouteTensor (parentVertex node E F i k J before after S)
          ρ H E F i k (parentPorts node E F i k J before after S) route x)) := by
  exact ofOrientation_value node E F i k J before after S route hr _ _ _ _ _ _ _ _ _ ρ H x

/-- The exact sum over route list positions, with the computed full states retained. -/
theorem value_eq_routeState_sum {D : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    (x : EuclideanSpace ℝ (Fin D)) :
    S.value ρ H x = ∑ u : Fin (routes (List.finRange J.length)).length,
      (routeState node E F i k J before after S
        ((routes (List.finRange J.length)).get u) (List.get_mem _ _)).value ρ H x := by
  let _ := S.edgeFintype
  change S.graph.coordinateEval _ (S.tensors ρ H x) = _
  rw [S.graph.coordinateEval_decorated_contract
    (parentVertex node E F i k J before after S) ρ H hρ hH E F i k
    (parentPorts node E F i k J before after S) x (S.tensors ρ H x)
    (S.formulaPorts_tensor _ node (.contract E F i k) J _ ρ H x)]
  apply Finset.sum_congr rfl
  intro u _
  exact (routeState_value node E F i k J before after S _ _ ρ H x).symm

 theorem routeState_taggedStep
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ routes (List.finRange J.length)) :
    TaggedStep (.contract node (route.1.map J.get) (route.2.map J.get))
      (before ++ [.formula (node.child false) E (route.1.map J.get),
        .formula (node.child true) F (route.2.map J.get)] ++ after)
      (before ++ [.formula node (.contract E F i k) J] ++ after) := by
  apply TaggedStep.contract
  have hh := route_map J.get hr
  simpa only [← List.ofFn_eq_map, List.ofFn_get] using hh

end ContractState
end AcceleratedLogConcave.Tensor.Ordered.Graph
