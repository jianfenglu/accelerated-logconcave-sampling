import AcceleratedLogConcave.Tensor.PhaseAnalyticEnvironment

noncomputable section
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D r s : ℕ}
namespace ContractState

/-- Generic Gibbs finite integral expansion, retaining every positional route.
All child integrability is proved from primitive jets by the analytic environment. -/
theorem phase_integral_eq_routeState_sum
    (node : NodeAddress) (E : Expr σ (r+2)) (F : Expr σ (s+2))
    (i : Fin (r+2)) (k : Fin (s+2)) (J : List LabelOrigin)
    (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.contract E F i k) J] ++ after))
    (P : PhaseAnalyticEnvironment σ D) :
    (∫ y, S.value P.coefficients P.potential y ∂P.toSmoothGibbsEnvironment.law) =
      ∑ u : Fin (routes (List.finRange J.length)).length, ∫ y,
        (routeState node E F i k J before after S
          ((routes (List.finRange J.length)).get u) (List.get_mem _ _)).value
          P.coefficients P.potential y ∂P.toSmoothGibbsEnvironment.law := by
  let child := fun u : Fin (routes (List.finRange J.length)).length =>
    routeState node E F i k J before after S
      ((routes (List.finRange J.length)).get u) (List.get_mem _ _)
  calc
    _ = ∫ y, ∑ u, (child u).value P.coefficients P.potential y
        ∂P.toSmoothGibbsEnvironment.law :=
      integral_congr_ae (Filter.Eventually.of_forall (fun y =>
        value_eq_routeState_sum node E F i k J before after S P.coefficients P.potential
          P.coefficient_smooth P.smooth y))
    _ = _ := integral_finsetSum _ (fun u _ => P.integrable_value (child u))
end ContractState
end AcceleratedLogConcave.Tensor.Ordered.Graph
