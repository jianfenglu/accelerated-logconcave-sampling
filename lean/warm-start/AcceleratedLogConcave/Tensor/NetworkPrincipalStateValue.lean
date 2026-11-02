import AcceleratedLogConcave.Tensor.NetworkPrincipalState
import AcceleratedLogConcave.Tensor.NetworkIBPFamilyValue

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}
namespace PrincipalState
variable {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2)) (i : Fin (r+2))
    (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))

theorem atRecipient_value
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (iq : Fin (before ++ [TaggedPending.formula node (.adjoint i E) J] ++ after).length)
    (hne : forestParentIndex before after (.formula node (.adjoint i E) J) ≠ iq)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    let _ := S.edgeFintype
    let p := ScoreState.parentVertex node E i J before after S
    let q := S.occurrence iq
    (atRecipient node E i J before after S hs hinv iq hne).value ρ H x =
      (S.graph.recipientGraph p q (fun h => hne (S.occurrence.injective h))).coordinateEval D
        (S.graph.principalRecipientFamily p q (fun h => hne (S.occurrence.injective h))
          (S.tensors ρ H)
          (S.graph.decoratedAdjointOperandTensor p ρ H E i
            (ScoreState.parentPorts node E i J before after S)) x) := by
  let _ := S.edgeFintype
  let p := ScoreState.parentVertex node E i J before after S
  let q := S.occurrence iq
  have hpq : p ≠ q := fun h => hne (S.occurrence.injective h)
  let e := ScoreState.parentPorts node E i J before after S
  let P : ∀ v, S.graph.SyntaxAt (σ := σ) v := fun v => ⟨S.pending v, S.ports v⟩
  let A := S.graph.ibpOperandSyntax p q hpq node E i J e
  let B := S.graph.ibpRecipientSyntax p q hpq (.ibp node) (P q).1 (P q).2
  change (S.graph.recipientGraph p q hpq).coordinateEval D
    (fun v => (S.graph.recipientGraph p q hpq).pendingTensor v ρ H
      (S.graph.ibpSyntaxFamily p q hpq P A B v).1
      (S.graph.ibpSyntaxFamily p q hpq P A B v).2 x) = _
  rw [S.graph.ibpSyntaxFamily_tensors p q hpq node E i J e P ρ H x]
  rfl

end PrincipalState
end AcceleratedLogConcave.Tensor.Ordered.Graph
