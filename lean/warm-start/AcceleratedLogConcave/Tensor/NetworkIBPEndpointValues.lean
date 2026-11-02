import AcceleratedLogConcave.Tensor.NetworkIBPEndpointSyntax
import AcceleratedLogConcave.Tensor.NetworkRecipientValues

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {n D : ℕ} {Edge : Type*} [Fintype Edge] (g : Graph n Edge)
    (p q : Fin (n+1)) (hne : p ≠ q)

theorem ibpOperandSyntax_value {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2))
    (i : Fin (r+2)) (J : List LabelOrigin)
    (e : g.Slot p ≃ (Fin J.length ⊕ Fin (r+1)))
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D))
    (a : (g.recipientGraph p q hne).Slot p → Fin D) :
    (g.recipientGraph p q hne).pendingTensor p ρ H
      (g.ibpOperandSyntax p q hne node E i J e).1
      (g.ibpOperandSyntax p q hne node E i J e).2 x a =
    g.decoratedAdjointOperandTensor p ρ H E i e x
      (a (g.recipientSourcePorts p q hne (.inr ())))
      (fun u => a (g.recipientSourcePorts p q hne (.inl u))) := by
  rw [pendingTensor_coordinateValue]
  let old : (Fin J.length ⊕ Fin (r+1)) → Fin D :=
    fun u => a (g.recipientSourcePorts p q hne (.inl (e.symm u)))
  let k := a (g.recipientSourcePorts p q hne (.inr ()))
  have hc : a ∘ (g.ibpOperandSyntax p q hne node E i J e).2.symm =
      Sum.elim old (fun _ => k) ∘ adjointOperandPorts J.length r i := by
    funext u
    change a (g.recipientSourcePorts p q hne
      ((Equiv.sumCongr e (Equiv.refl Unit)).symm (adjointOperandPorts J.length r i u))) =
      Sum.elim old (fun _ => k) (adjointOperandPorts J.length r i u)
    generalize adjointOperandPorts J.length r i u = w
    cases w <;> rfl
  rw [hc]
  change pendingCoordinateValue ρ H (.formula (node.child false) E J)
    (Sum.elim old (fun _ => k) ∘ adjointOperandPorts J.length r i) x = _
  rw [pendingCoordinateValue_adjoint_operand]
  rfl

 theorem ibpRecipientSyntax_value (fresh : LabelOrigin) (Q : TaggedPending σ)
    (e : g.Slot q ≃ pendingPorts Q)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D))
    (a : (g.recipientGraph p q hne).Slot q → Fin D) :
    (g.recipientGraph p q hne).pendingTensor q ρ H
      (g.ibpRecipientSyntax p q hne fresh Q e).1
      (g.ibpRecipientSyntax p q hne fresh Q e).2 x a =
    dir (coordinateDirection D (a (g.recipientTargetPorts p q hne (.inr ()))))
      (fun y => g.pendingTensor q ρ H Q e y
        (fun u => a (g.recipientTargetPorts p q hne (.inl u)))) x := by
  rw [pendingTensor_coordinateValue]
  change pendingCoordinateValue ρ H (Q.decorate fresh)
    (a ∘ (g.ibpRecipientSyntax p q hne fresh Q e).2.symm) x = _
  rw [pendingCoordinateValue_decorate]
  have hport (u : pendingPorts Q ⊕ Unit) :
      (g.ibpRecipientSyntax p q hne fresh Q e).2.symm (decoratePortEquiv fresh Q u) =
      g.recipientTargetPorts p q hne ((Equiv.sumCongr e (Equiv.refl Unit)).symm u) := by
    change g.recipientTargetPorts p q hne ((Equiv.sumCongr e (Equiv.refl Unit)).symm
      ((decoratePortEquiv fresh Q).symm (decoratePortEquiv fresh Q u))) = _
    rw [Equiv.symm_apply_apply]
  change dir (coordinateDirection D
      (a ((g.ibpRecipientSyntax p q hne fresh Q e).2.symm (decoratePortEquiv fresh Q (.inr ())))))
      (pendingCoordinateValue ρ H Q (fun u => a ((g.ibpRecipientSyntax p q hne fresh Q e).2.symm
        (decoratePortEquiv fresh Q (.inl u))))) x = _
  simp only [hport]
  have hv : (fun y => g.pendingTensor q ρ H Q e y
      (fun u => a (g.recipientTargetPorts p q hne (.inl u)))) =
      pendingCoordinateValue ρ H Q (fun u => a (g.recipientTargetPorts p q hne (.inl (e.symm u)))) := by
    funext y
    rw [pendingTensor_coordinateValue]
    rfl
  rw [hv]
  rfl

end AcceleratedLogConcave.Tensor.Ordered.Graph
