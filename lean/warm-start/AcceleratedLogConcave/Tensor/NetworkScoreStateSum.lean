import AcceleratedLogConcave.Tensor.NetworkScoreStateValue
import AcceleratedLogConcave.Tensor.NetworkContractStateSum
import AcceleratedLogConcave.Tensor.NetworkAdjointDecomposition

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
namespace ScoreState
variable {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2)) (i : Fin (r+2))
    (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)

def routeState
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ scoreRoutes (List.finRange J.length)) :
    SyntaxState (before ++
      [.score node (route.1.map J.get) (by simpa using scoreRoutes_left_ne_nil _ route hr),
       .formula (node.child false) E (route.2.map J.get)] ++ after) :=
  let h := S.graph.exists_score_orientation (parentVertex node E i J before after S)
    S.admissible (parentPorts node E i J before after S) route hr
  let part := Classical.choose h
  let b := Classical.choose (Classical.choose_spec h)
  let hflags := Classical.choose_spec (Classical.choose_spec h)
  ofOrientation node E i J before after S hs hinv route hr part b
    hflags.1 hflags.2.1 hflags.2.2.1 hflags.2.2.2.1 hflags.2.2.2.2.1 hflags.2.2.2.2.2

theorem routeState_value {D : ℕ}
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ scoreRoutes (List.finRange J.length))
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    (routeState node E i J before after S hs hinv route hr).value ρ H x =
      letI := S.edgeFintype
      S.graph.coordinateEval D (S.graph.replaceTensorAt (parentVertex node E i J before after S)
        (S.tensors ρ H x) (S.graph.decoratedScoreRouteTensor (parentVertex node E i J before after S)
          ρ H E i (parentPorts node E i J before after S) route x)) := by
  exact ofOrientation_value node E i J before after S hs hinv route hr _ _ _ _ _ _ _ _ ρ H x

/-- Actual full adjoint value: principal branch plus literal score-state list positions. -/
theorem value_eq_principal_add_routeState_sum {D : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    (x : EuclideanSpace ℝ (Fin D)) :
    S.value ρ H x =
      (letI := S.edgeFintype
       S.graph.coordinateEval D (S.graph.replaceTensorAt (parentVertex node E i J before after S)
         (S.tensors ρ H x) (S.graph.adjointCoordinateTensor (parentVertex node E i J before after S) H
           (S.graph.decoratedAdjointOperandTensor (parentVertex node E i J before after S) ρ H E i
             (parentPorts node E i J before after S)) x))) +
      ∑ u : Fin (scoreRoutes (List.finRange J.length)).length,
        (routeState node E i J before after S hs hinv
          ((scoreRoutes (List.finRange J.length)).get u) (List.get_mem _ _)).value ρ H x := by
  let _ := S.edgeFintype
  change S.graph.coordinateEval _ (S.tensors ρ H x) = _
  rw [S.graph.coordinateEval_decorated_adjoint (parentVertex node E i J before after S)
    ρ H hρ hH E i (parentPorts node E i J before after S) x (S.tensors ρ H x)
    (S.formulaPorts_tensor _ node (.adjoint i E) J _ ρ H x),Fintype.sum_option]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  exact (routeState_value node E i J before after S hs hinv _ _ ρ H x).symm

include i in
theorem routeState_taggedStep
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ scoreRoutes (List.finRange J.length)) :
    TaggedStep (.score node (route.1.map J.get) (route.2.map J.get))
      (before ++ [.score node (route.1.map J.get) (by simpa using scoreRoutes_left_ne_nil _ route hr),
        .formula (node.child false) E (route.2.map J.get)] ++ after)
      (before ++ [.formula node (.adjoint i E) J] ++ after) := by
  apply TaggedStep.score
  have hh := scoreRoute_map J.get hr
  simpa only [←List.ofFn_eq_map,List.ofFn_get] using hh

end ScoreState
end AcceleratedLogConcave.Tensor.Ordered.Graph
