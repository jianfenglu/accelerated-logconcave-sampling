import AcceleratedLogConcave.Tensor.NetworkContractStateSum
import AcceleratedLogConcave.Tensor.NetworkActualPending

noncomputable section
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
open ActualCoefficientIntegrability Conditional
open Analysis.PositiveVarianceSlab
variable {D r s : ℕ}
namespace ContractState
variable (node : NodeAddress) (E : Expr signature (r+2)) (G : Expr signature (s+2))
    (i : Fin (r+2)) (k : Fin (s+2)) (J : List LabelOrigin)
    (before after : List (TaggedPending signature))
    (S : SyntaxState (before ++ [.formula node (.contract E G i k) J] ++ after))

/-- Original-data finite integral expansion, retaining every positional route. -/
theorem integral_eq_routeState_sum
    {F : EuclideanSpace ℝ (Fin D) → ℝ} (hF : ContDiff ℝ 2 F) {ell b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell * ‖w‖^2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : EuclideanSpace ℝ (Fin D)) (radius : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (left b) (right b)) :
    let ρ := coefficientEnvironment F x ell radius t
    let H := interpolationPotential F x radius t
    (∫ y, S.value ρ H y ∂interpolationLaw F x radius t) =
      ∑ u : Fin (routes (List.finRange J.length)).length, ∫ y,
        (routeState node E G i k J before after S
          ((routes (List.finRange J.length)).get u) (List.get_mem _ _)).value ρ H y
        ∂interpolationLaw F x radius t := by
  let ρ := coefficientEnvironment F x ell radius t
  let H := interpolationPotential F x radius t
  let μ := interpolationLaw F x radius t
  let child := fun u : Fin (routes (List.finRange J.length)).length =>
    routeState node E G i k J before after S
      ((routes (List.finRange J.length)).get u) (List.get_mem _ _)
  have hi (u) : Integrable ((child u).value ρ H) μ :=
    (child u).integrable_value hF hlo hhi hb0 hb1 ht
  have ht' := construction_subset hb0 hb1 ht
  have hρ := coefficient_contDiff hF hlo hhi hb0 hb1 x radius ht
  have hH := contDiff_interpolationPotential hF hlo hhi x radius ht'.1 ht'.2
  change (∫ y, S.value ρ H y ∂μ) = _
  calc
    _ = ∫ y, ∑ u, (child u).value ρ H y ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun y =>
        value_eq_routeState_sum node E G i k J before after S ρ H hρ hH y))
    _ = _ := integral_finsetSum _ (fun u _ => hi u)

end ContractState
end AcceleratedLogConcave.Tensor.Ordered.Graph
