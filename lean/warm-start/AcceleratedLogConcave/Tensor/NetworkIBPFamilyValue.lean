import AcceleratedLogConcave.Tensor.NetworkIBPFamily
import AcceleratedLogConcave.Tensor.NetworkIBPEndpointValues

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {n D : ℕ} {Edge : Type*} [Fintype Edge] (g : Graph n Edge)
    (p q : Fin (n+1)) (hne : p ≠ q)

/-- The entire literal principal child tensor family is the previously verified
actual IBP family. No endpoint or global evaluation equality is assumed. -/
theorem ibpSyntaxFamily_tensors {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2))
    (i : Fin (r+2)) (J : List LabelOrigin)
    (e : g.Slot p ≃ (Fin J.length ⊕ Fin (r+1)))
    (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    (fun v => (g.recipientGraph p q hne).pendingTensor v ρ H
      (g.ibpSyntaxFamily p q hne P
        (g.ibpOperandSyntax p q hne node E i J e)
        (g.ibpRecipientSyntax p q hne (.ibp node) (P q).1 (P q).2) v).1
      (g.ibpSyntaxFamily p q hne P
        (g.ibpOperandSyntax p q hne node E i J e)
        (g.ibpRecipientSyntax p q hne (.ibp node) (P q).1 (P q).2) v).2 x) =
    g.principalRecipientFamily p q hne
      (fun y v => g.pendingTensor v ρ H (P v).1 (P v).2 y)
      (g.decoratedAdjointOperandTensor p ρ H E i e) x := by
  funext v
  by_cases hp : v = p
  · subst v
    rw [ibpSyntaxFamily_source]
    ext a
    rw [ibpOperandSyntax_value]
    unfold principalRecipientFamily
    rw [recipientPairFamily_source_apply]
  by_cases hq : v = q
  · subst v
    rw [ibpSyntaxFamily_target]
    ext a
    rw [ibpRecipientSyntax_value]
    unfold principalRecipientFamily
    rw [recipientPairFamily_target_apply]
    rfl
  rw [ibpSyntaxFamily_other g p q hne P _ _ v hp hq]
  ext a
  unfold principalRecipientFamily
  rw [recipientPairFamily_other_apply g p q hne _ _ _ v hp hq]
  rw [pendingTensor_coordinateValue, pendingTensor_coordinateValue]
  rfl

end AcceleratedLogConcave.Tensor.Ordered.Graph
