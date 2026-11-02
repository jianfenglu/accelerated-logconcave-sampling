import AcceleratedLogConcave.Tensor.NetworkActualIBP
import AcceleratedLogConcave.Tensor.NetworkPendingCoordinateValue
import AcceleratedLogConcave.Tensor.ActualScoreTerminal

noncomputable section
open MeasureTheory
open scoped Classical BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords PolynomialClosure
open ActualCoefficientIntegrability Conditional Conditional.Appell
open Analysis.PositiveVarianceSlab
variable {D : ℕ} {F : EuclideanSpace ℝ (Fin D) → ℝ} {ell r t : ℝ}
  {x : EuclideanSpace ℝ (Fin D)}

/-- Every retained score is nonempty, so it is a literal decorated S coefficient. -/
theorem pendingCoordinateValue_actual
    (hH : ContDiff ℝ ∞ (interpolationPotential F x r t))
    (q : TaggedPending signature) (a : pendingPorts q → Fin D) :
    ActualDecoratedCoordinate F x ell r t
      (pendingCoordinateValue (coefficientEnvironment F x ell r t)
        (interpolationPotential F x r t) q a) := by
  cases q with
  | @formula s node e J =>
    refine ⟨s,e,(fun u => a (.inr u)),
      (List.finRange J.length).map (fun u => coordinateDirection D (a (.inl u))), ?_⟩
    exact partialAlong_map_id _ _ _
  | score node J hJ =>
    cases J with
    | nil => exact False.elim (hJ rfl)
    | cons o J =>
      let v := fun u : Fin (J.length+1) => coordinateDirection D (a (.inl u))
      let b : Fin 2 → Fin D := Fin.cases (a (.inl 0)) (fun _ => a (.inr ()))
      refine ⟨2,Expr.coefficient (σ := signature) (Sum.inr ()),b,
        ((List.finRange J.length).map Fin.succ).map v, ?_⟩
      change partialAlong v (List.finRange (J.length+1))
        (dir (coordinateDirection D (a (.inr ()))) _) = _
      rw [List.finRange_succ,nonempty_score_coefficient _ _ _ hH]
      rw [partialAlong_map_id]
      rfl

 theorem pendingTensor_actual {n : ℕ} {Edge : Type*} [Fintype Edge]
    (g : Graph n Edge) (v : Fin (n+1))
    (hH : ContDiff ℝ ∞ (interpolationPotential F x r t))
    (q : TaggedPending signature) (e : g.Slot v ≃ pendingPorts q)
    (a : g.Slot v → Fin D) :
    ActualDecoratedCoordinate F x ell r t
      (fun y => g.pendingTensor v (coefficientEnvironment F x ell r t)
        (interpolationPotential F x r t) q e y a) := by
  have he : (fun y => g.pendingTensor v (coefficientEnvironment F x ell r t)
      (interpolationPotential F x r t) q e y a) =
      pendingCoordinateValue (coefficientEnvironment F x ell r t)
        (interpolationPotential F x r t) q (a ∘ e.symm) := by
    funext y
    exact pendingTensor_coordinateValue _ _ _ _ _ _ _ _
  rw [he]
  exact pendingCoordinateValue_actual hH _ _

 theorem SyntaxState.tensor_actual {s : List (TaggedPending signature)} (S : SyntaxState s)
    (hH : ContDiff ℝ ∞ (interpolationPotential F x r t))
    (v : Fin (S.n+1)) (a : S.graph.Slot v → Fin D) :
    ActualDecoratedCoordinate F x ell r t
      (fun y => S.tensors (coefficientEnvironment F x ell r t)
        (interpolationPotential F x r t) y v a) := by
  let := S.edgeFintype
  have he : (fun y => S.tensors (coefficientEnvironment F x ell r t)
      (interpolationPotential F x r t) y v a) =
      pendingCoordinateValue (coefficientEnvironment F x ell r t)
        (interpolationPotential F x r t) (S.pending v) (a ∘ (S.ports v).symm) := by
    funext y
    exact pendingTensor_coordinateValue _ _ _ _ _ _ _ _
  rw [he]
  exact pendingCoordinateValue_actual hH _ _

/-- Actual whole-network integrability, from original data and literal syntax alone. -/
theorem SyntaxState.integrable_value {s : List (TaggedPending signature)} (S : SyntaxState s)
    (hF : ContDiff ℝ 2 F) {b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell*‖w‖^2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (ht : t ∈ Set.Icc (left b) (right b)) :
    Integrable (S.value (coefficientEnvironment F x ell r t)
      (interpolationPotential F x r t)) (interpolationLaw F x r t) := by
  let := S.edgeFintype
  let := interpolationLaw_isProbabilityMeasure hF hlo x r t
  have ht' := construction_subset hb0 hb1 ht
  have hH := contDiff_interpolationPotential hF hlo hhi x r ht'.1 ht'.2
  have hp := fun v a => S.tensor_actual (ell := ell) hH v a
  have hg := fun v a => ActualDecoratedCoordinate.polynomialJets hF hlo hhi hb0 hb1 x r ht (hp v a)
  have hc := fun v a => (ActualDecoratedCoordinate.contDiff hF hlo hhi hb0 hb1 x r ht (hp v a)).continuous
  unfold SyntaxState.value coordinateEval
  apply integrable_finsetSum
  intro a _
  exact (HasGrowth.prod Finset.univ (fun v _ => hg v _ [])).integrable
    (continuous_finsetProd _ (fun v _ => hc v _)).aestronglyMeasurable
    (interpolationLaw_integrable_norm_pow hF hlo x r t)

end AcceleratedLogConcave.Tensor.Ordered.Graph
