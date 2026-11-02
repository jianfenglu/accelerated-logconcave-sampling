import AcceleratedLogConcave.Tensor.NetworkPrincipalStateValue
import AcceleratedLogConcave.Tensor.NetworkActualPending

noncomputable section
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

/-- Each distinct graph occurrence is its unique original syntax position. -/
theorem recipient_index_ne (q : Fin (S.n+1))
    (hq : q ≠ ScoreState.parentVertex node E i J before after S) :
    forestParentIndex before after (.formula node (.adjoint i E) J) ≠ S.occurrence.symm q := by
  intro h
  apply hq
  have hh := congrArg S.occurrence h
  simpa [ScoreState.parentVertex] using hh.symm

/-- Principal original-law IBP is the sum of the actual retained syntax states.
All analytic obligations are discharged from original data and literal coordinates. -/
theorem integral_principal_eq_recipient_states
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
    (∫ y, S.graph.coordinateEval D (S.graph.replaceTensorAt p (S.tensors ρ H y)
      (S.graph.adjointCoordinateTensor p H
        (S.graph.decoratedAdjointOperandTensor p ρ H E i
          (ScoreState.parentPorts node E i J before after S)) y)) ∂interpolationLaw F x radius t) =
      ∑ q : {q : Fin (S.n+1) // q ≠ p}, ∫ y,
        (atRecipient node E i J before after S hs hinv (S.occurrence.symm q.val)
          (recipient_index_ne node E i J before after S q.val q.property)).value ρ H y
        ∂interpolationLaw F x radius t := by
  let _ := S.edgeFintype
  let p := ScoreState.parentVertex node E i J before after S
  let e := ScoreState.parentPorts node E i J before after S
  let ρ := coefficientEnvironment F x ell radius t
  let H := interpolationPotential F x radius t
  let T := S.tensors ρ H
  let A := S.graph.decoratedAdjointOperandTensor p ρ H E i e
  let U := fun y => S.graph.replaceTensorAt p (T y) (S.graph.adjointCoordinateTensor p H A y)
  have hA : ∀ k a, ActualDecoratedCoordinate F x ell radius t (fun y => A y k a) := by
    intro k a
    refine ⟨arity+2,E,Fin.insertNth i k (fun u => a (S.graph.adjointFreeSlot p e u)),
      (List.finRange J.length).map (fun u => coordinateDirection D (a (S.graph.decoratedLabelSlot p e u))), ?_⟩
    change partialAlong _ _ _ = partialAlong id _ _
    rw [partialAlong_map_directions]
    rfl
  have ht' := construction_subset hb0 hb1 ht
  have hH := contDiff_interpolationPotential hF hlo hhi x radius ht'.1 ht'.2
  have hT : ∀ v, v ≠ p → ∀ a,
      ActualDecoratedCoordinate F x ell radius t (fun y => U y v a) := by
    intro v hv a
    have he : (fun y => U y v a) = (fun y => T y v a) := by
      funext y
      exact congrArg (fun z => z a) (S.graph.replaceTensorAt_other p (T y) _ v hv)
    rw [he]
    exact S.tensor_actual hH v a
  have hp : ∀ y, U y p = S.graph.adjointCoordinateTensor p H A y := by
    intro y
    exact S.graph.replaceTensorAt_same p _ _
  have hi := integral_actual_adjoint_network hF hlo hhi hb0 hb1 x radius ht S.graph p U A hA hT hp
  change (∫ y, S.graph.coordinateEval D (U y) ∂interpolationLaw F x radius t) = _
  rw [hi]
  apply Finset.sum_congr rfl
  intro q _
  apply integral_congr_ae
  filter_upwards [] with y
  rw [atRecipient_value]
  have hn (z : Fin (S.n+1)) (hz : p ≠ z) (he : z = q.val) :
      (S.graph.recipientGraph p z hz).coordinateEval D
        (S.graph.principalRecipientFamily p z hz T A y) =
      (S.graph.recipientGraph p q.val (Ne.symm q.property)).coordinateEval D
        (S.graph.principalRecipientFamily p q.val (Ne.symm q.property) T A y) := by
    subst z
    rfl
  rw [hn _ _ (S.occurrence.apply_symm_apply q.val)]
  change (S.graph.recipientGraph p q.val (Ne.symm q.property)).coordinateEval D
      (S.graph.principalRecipientFamily p q.val (Ne.symm q.property) U A y) =
    (S.graph.recipientGraph p q.val (Ne.symm q.property)).coordinateEval D
      (S.graph.principalRecipientFamily p q.val (Ne.symm q.property) T A y)
  rw [S.graph.principalRecipientFamily_replaceTensorAt_source p q.val (Ne.symm q.property) T
    (fun y => S.graph.adjointCoordinateTensor p H A y) A y]

end PrincipalState
end AcceleratedLogConcave.Tensor.Ordered.Graph
