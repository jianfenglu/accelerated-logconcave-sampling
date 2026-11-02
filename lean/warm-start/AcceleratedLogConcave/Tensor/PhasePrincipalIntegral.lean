import AcceleratedLogConcave.Tensor.NetworkPrincipalStateValue
import AcceleratedLogConcave.Tensor.PhaseAnalyticEnvironment

noncomputable section
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}
namespace PrincipalState
variable {arity : ℕ} (node : NodeAddress) (E : Expr σ (arity+2))
    (i : Fin (arity+2)) (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))

/-- Each distinct graph occurrence is its unique original syntax position. -/
theorem phase_recipient_index_ne (q : Fin (S.n+1))
    (hq : q ≠ ScoreState.parentVertex node E i J before after S) :
    forestParentIndex before after (.formula node (.adjoint i E) J) ≠ S.occurrence.symm q := by
  intro h
  apply hq
  have hh := congrArg S.occurrence h
  simpa [ScoreState.parentVertex] using hh.symm

/-- Principal original-law IBP is the sum of the actual retained syntax states.
All analytic obligations are discharged from original data and literal coordinates. -/
theorem phase_integral_principal_eq_recipient_states
    (P : PhaseAnalyticEnvironment σ D)
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup) :
    let _ := S.edgeFintype
    let p := ScoreState.parentVertex node E i J before after S
    let ρ := P.coefficients
    let H := P.potential
    (∫ y, S.graph.coordinateEval D (S.graph.replaceTensorAt p (S.tensors ρ H y)
      (S.graph.adjointCoordinateTensor p H
        (S.graph.decoratedAdjointOperandTensor p ρ H E i
          (ScoreState.parentPorts node E i J before after S)) y)) ∂P.toSmoothGibbsEnvironment.law) =
      ∑ q : {q : Fin (S.n+1) // q ≠ p}, ∫ y,
        (atRecipient node E i J before after S hs hinv (S.occurrence.symm q.val)
          (phase_recipient_index_ne node E i J before after S q.val q.property)).value ρ H y
        ∂P.toSmoothGibbsEnvironment.law := by
  let _ := S.edgeFintype
  let p := ScoreState.parentVertex node E i J before after S
  let e := ScoreState.parentPorts node E i J before after S
  let ρ := P.coefficients
  let H := P.potential
  let T := S.tensors ρ H
  let A := S.graph.decoratedAdjointOperandTensor p ρ H E i e
  let U := fun y => S.graph.replaceTensorAt p (T y) (S.graph.adjointCoordinateTensor p H A y)
  have hA (k : Fin D) (a : S.graph.Slot p → Fin D) :
      ContDiff ℝ ∞ (fun y => A y k a) := by
    exact contDiff_partialAlong _ _
      (contDiff_section ρ H P.coefficient_smooth P.smooth E _)
  have hAp (k : Fin D) (a : S.graph.Slot p → Fin D) :
      PolynomialClosure.HasPolynomialJets (fun y => A y k a) := by
    exact P.decorated_expression_jets E _ _ _
  have he (v : Fin (S.n+1)) (hv : v ≠ p) (a : S.graph.Slot v → Fin D) :
      (fun y => U y v a) = (fun y => T y v a) := by
    funext y
    exact congrArg (fun z => z a) (S.graph.replaceTensorAt_other p (T y) _ v hv)
  have hT : ∀ v, v ≠ p → ∀ a, ContDiff ℝ ∞ (fun y => U y v a) := by
    intro v hv a
    rw [he v hv a]
    exact P.tensor_smooth S v a
  have hTp : ∀ v, v ≠ p → ∀ a,
      PolynomialClosure.HasPolynomialJets (fun y => U y v a) := by
    intro v hv a
    rw [he v hv a]
    exact P.tensor_polynomial_jets S v a
  have hp : ∀ y, U y p = S.graph.adjointCoordinateTensor p H A y := by
    intro y
    exact S.graph.replaceTensorAt_same p _ _
  have hi := P.toSmoothGibbsEnvironment.integral_adjoint_network S.graph p U A hA hAp hT hTp hp
  change (∫ y, S.graph.coordinateEval D (U y) ∂P.toSmoothGibbsEnvironment.law) = _
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
