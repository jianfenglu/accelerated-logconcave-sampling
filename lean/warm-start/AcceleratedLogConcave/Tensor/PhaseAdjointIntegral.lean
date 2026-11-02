import AcceleratedLogConcave.Tensor.PhasePrincipalIntegral
import AcceleratedLogConcave.Tensor.NetworkScoreStateSum

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}
namespace PrincipalState
variable {arity : ℕ} (node : NodeAddress) (E : Expr σ (arity+2))
    (i : Fin (arity+2)) (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))

theorem phase_integral_adjoint_eq_children
    (P : PhaseAnalyticEnvironment σ D)
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup) :
    let _ := S.edgeFintype
    let p := ScoreState.parentVertex node E i J before after S
    let ρ := P.coefficients
    let H := P.potential
    (∫ y, S.value ρ H y ∂P.toSmoothGibbsEnvironment.law) =
      (∑ u : Fin (scoreRoutes (List.finRange J.length)).length, ∫ y,
        (ScoreState.routeState node E i J before after S hs hinv
          ((scoreRoutes (List.finRange J.length)).get u) (List.get_mem _ _)).value ρ H y
        ∂P.toSmoothGibbsEnvironment.law) +
      ∑ q : {q : Fin (S.n+1) // q ≠ p}, ∫ y,
        (atRecipient node E i J before after S hs hinv (S.occurrence.symm q.val)
          (phase_recipient_index_ne node E i J before after S q.val q.property)).value ρ H y
        ∂P.toSmoothGibbsEnvironment.law := by
  let _ := S.edgeFintype
  let p := ScoreState.parentVertex node E i J before after S
  let e := ScoreState.parentPorts node E i J before after S
  let ρ := P.coefficients
  let H := P.potential
  let μ := P.toSmoothGibbsEnvironment.law
  let A := S.graph.decoratedAdjointOperandTensor p ρ H E i e
  let principal := fun y => S.graph.coordinateEval D
    (S.graph.replaceTensorAt p (S.tensors ρ H y) (S.graph.adjointCoordinateTensor p H A y))
  let score := fun u : Fin (scoreRoutes (List.finRange J.length)).length =>
    (ScoreState.routeState node E i J before after S hs hinv
      ((scoreRoutes (List.finRange J.length)).get u) (List.get_mem _ _)).value ρ H
  have hiScore (u) : Integrable (score u) μ :=
    P.integrable_value (ScoreState.routeState node E i J before after S hs hinv _ _)
  have hiSum : Integrable (fun y => ∑ u, score u y) μ :=
    integrable_finsetSum _ (fun u _ => hiScore u)
  have hρ := P.coefficient_smooth
  have hH := P.smooth
  have hsplit (y) : S.value ρ H y = principal y + ∑ u, score u y :=
    ScoreState.value_eq_principal_add_routeState_sum node E i J before after S hs hinv ρ H hρ hH y
  have hiPrincipal : Integrable principal μ := by
    apply ((P.integrable_value S).sub hiSum).congr
    filter_upwards [] with y
    have h := hsplit y
    change S.value ρ H y - ∑ u, score u y = principal y
    linarith
  have hintegral : (∫ y, S.value ρ H y ∂μ) = (∫ y, principal y ∂μ) + ∑ u, ∫ y, score u y ∂μ := by
    calc
      _ = ∫ y, principal y + ∑ u, score u y ∂μ := integral_congr_ae (Filter.Eventually.of_forall hsplit)
      _ = (∫ y, principal y ∂μ) + ∫ y, ∑ u, score u y ∂μ := integral_add hiPrincipal hiSum
      _ = _ := by rw [integral_finsetSum _ (fun u _ => hiScore u)]
  change (∫ y, S.value ρ H y ∂μ) = _
  rw [hintegral]
  rw [phase_integral_principal_eq_recipient_states node E i J before after S P hs hinv]
  exact add_comm _ _

end PrincipalState
end AcceleratedLogConcave.Tensor.Ordered.Graph
