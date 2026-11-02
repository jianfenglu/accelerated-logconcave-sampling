import AcceleratedLogConcave.Tensor.NetworkPrincipalActualIntegral
import AcceleratedLogConcave.Tensor.NetworkScoreStateSum

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
open ActualCoefficientIntegrability Conditional
open Analysis.PositiveVarianceSlab
variable {D : ℕ}
namespace PrincipalState
variable {arity : ℕ} (node : NodeAddress) (E : Expr signature (arity+2))
    (i : Fin (arity+2)) (J : List LabelOrigin) (before after : List (TaggedPending signature))
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))

theorem integral_adjoint_eq_actual_children
    {F : EuclideanSpace ℝ (Fin D) → ℝ} (hF : ContDiff ℝ 2 F) {ell b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell * ‖w‖^2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : EuclideanSpace ℝ (Fin D)) (radius : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (left b) (right b))
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup) :
    let _ := S.edgeFintype
    let p := ScoreState.parentVertex node E i J before after S
    let ρ := coefficientEnvironment F x ell radius t
    let H := interpolationPotential F x radius t
    (∫ y, S.value ρ H y ∂interpolationLaw F x radius t) =
      (∑ u : Fin (scoreRoutes (List.finRange J.length)).length, ∫ y,
        (ScoreState.routeState node E i J before after S hs hinv
          ((scoreRoutes (List.finRange J.length)).get u) (List.get_mem _ _)).value ρ H y
        ∂interpolationLaw F x radius t) +
      ∑ q : {q : Fin (S.n+1) // q ≠ p}, ∫ y,
        (atRecipient node E i J before after S hs hinv (S.occurrence.symm q.val)
          (recipient_index_ne node E i J before after S q.val q.property)).value ρ H y
        ∂interpolationLaw F x radius t := by
  let _ := S.edgeFintype
  let p := ScoreState.parentVertex node E i J before after S
  let e := ScoreState.parentPorts node E i J before after S
  let ρ := coefficientEnvironment F x ell radius t
  let H := interpolationPotential F x radius t
  let μ := interpolationLaw F x radius t
  let A := S.graph.decoratedAdjointOperandTensor p ρ H E i e
  let principal := fun y => S.graph.coordinateEval D
    (S.graph.replaceTensorAt p (S.tensors ρ H y) (S.graph.adjointCoordinateTensor p H A y))
  let score := fun u : Fin (scoreRoutes (List.finRange J.length)).length =>
    (ScoreState.routeState node E i J before after S hs hinv
      ((scoreRoutes (List.finRange J.length)).get u) (List.get_mem _ _)).value ρ H
  have hiScore (u) : Integrable (score u) μ :=
    (ScoreState.routeState node E i J before after S hs hinv _ _).integrable_value
      hF hlo hhi hb0 hb1 ht
  have hiSum : Integrable (fun y => ∑ u, score u y) μ :=
    integrable_finsetSum _ (fun u _ => hiScore u)
  have ht' := construction_subset hb0 hb1 ht
  have hρ := coefficient_contDiff hF hlo hhi hb0 hb1 x radius ht
  have hH := contDiff_interpolationPotential hF hlo hhi x radius ht'.1 ht'.2
  have hsplit (y) : S.value ρ H y = principal y + ∑ u, score u y :=
    ScoreState.value_eq_principal_add_routeState_sum node E i J before after S hs hinv ρ H hρ hH y
  have hiPrincipal : Integrable principal μ := by
    apply ((S.integrable_value hF hlo hhi hb0 hb1 ht).sub hiSum).congr
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
  rw [integral_principal_eq_recipient_states node E i J before after S hF hlo hhi hb0 hb1
    x radius ht hs hinv]
  exact add_comm _ _

end PrincipalState
end AcceleratedLogConcave.Tensor.Ordered.Graph
