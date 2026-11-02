import AcceleratedLogConcave.Tensor.NetworkRecipientSlots
import AcceleratedLogConcave.Tensor.NetworkPendingCoordinateValue

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge)
    (p q : Fin (n+1)) (hne : p ≠ q)

/-- Actual operand syntax and all ordered ports for the principal IBP source. -/
def ibpOperandSyntax {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2))
    (i : Fin (r+2)) (J : List LabelOrigin)
    (e : g.Slot p ≃ (Fin J.length ⊕ Fin (r+1))) :
    (g.recipientGraph p q hne).SyntaxAt (σ := σ) p :=
  ⟨.formula (node.child false) E J,
    (g.recipientSourcePorts p q hne).symm.trans
      ((Equiv.sumCongr e (Equiv.refl Unit)).trans (adjointOperandPorts J.length r i).symm)⟩

/-- The actual recipient acquires the fresh origin at the head, not at the tail. -/
def ibpRecipientSyntax (o : LabelOrigin) (Q : TaggedPending σ)
    (e : g.Slot q ≃ pendingPorts Q) :
    (g.recipientGraph p q hne).SyntaxAt (σ := σ) q :=
  ⟨Q.decorate o, (g.recipientTargetPorts p q hne).symm.trans
    ((Equiv.sumCongr e (Equiv.refl Unit)).trans (decoratePortEquiv o Q))⟩

def ibpOtherSyntax (v : Fin (n+1)) (hvp : v ≠ p) (hvq : v ≠ q)
    (Q : TaggedPending σ) (e : g.Slot v ≃ pendingPorts Q) :
    (g.recipientGraph p q hne).SyntaxAt (σ := σ) v :=
  ⟨Q, (g.recipientOtherPorts p q hne v hvp hvq).symm.trans e⟩

theorem ibpOperandSyntax_origin {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2))
    (i : Fin (r+2)) (J : List LabelOrigin)
    (e : g.Slot p ≃ (Fin J.length ⊕ Fin (r+1)))
    (wire : LabelOrigin → Option (Option Edge))
    (he : ∀ u : Fin J.length,
      oldWire (Sum.elim Subtype.val Subtype.val (e.symm (.inl u))) = wire (J.get u)) :
    ∀ u o, pendingPortOrigin (g.ibpOperandSyntax p q hne node E i J e).1 u = some o →
      Sum.elim Subtype.val Subtype.val
        ((g.ibpOperandSyntax p q hne node E i J e).2.symm u) = wire o := by
  intro u o hu
  change (Fin J.length ⊕ Fin (r+2)) at u
  cases u with
  | inl u =>
    have ho : J.get u = o := Option.some.inj hu
    subst o
    change Sum.elim Subtype.val Subtype.val
      (g.recipientSourcePorts p q hne (.inl (e.symm (.inl u)))) = _
    exact (g.recipientSourcePorts_wire p q hne (.inl (e.symm (.inl u)))).trans (he u)
  | inr u => cases hu

 theorem ibpRecipientSyntax_origin (fresh : LabelOrigin) (Q : TaggedPending σ)
    (e : g.Slot q ≃ pendingPorts Q) (wire : LabelOrigin → Option (Option Edge))
    (hf : wire fresh = some none)
    (he : ∀ u o, pendingPortOrigin Q u = some o →
      oldWire (Sum.elim Subtype.val Subtype.val (e.symm u)) = wire o) :
    ∀ u o, pendingPortOrigin (g.ibpRecipientSyntax p q hne fresh Q e).1 u = some o →
      Sum.elim Subtype.val Subtype.val
        ((g.ibpRecipientSyntax p q hne fresh Q e).2.symm u) = wire o := by
  intro u o hu
  obtain ⟨a, rfl⟩ := (decoratePortEquiv fresh Q).surjective u
  cases a with
  | inl a =>
    have horigin : pendingPortOrigin Q a = some o := by
      rw [← decoratePortEquiv_old_origin fresh Q a]
      exact hu
    change Sum.elim Subtype.val Subtype.val
      (g.recipientTargetPorts p q hne ((Equiv.sumCongr e (Equiv.refl Unit)).symm
        ((decoratePortEquiv fresh Q).symm (decoratePortEquiv fresh Q (.inl a))))) = _
    rw [Equiv.symm_apply_apply]
    exact (g.recipientTargetPorts_wire p q hne (.inl (e.symm a))).trans (he a o horigin)
  | inr a =>
    cases a
    have ho : fresh = o := by
      apply Option.some.inj
      exact (decoratePortEquiv_fresh_origin fresh Q).symm.trans hu
    subst o
    change Sum.elim Subtype.val Subtype.val
      (g.recipientTargetPorts p q hne ((Equiv.sumCongr e (Equiv.refl Unit)).symm
        ((decoratePortEquiv fresh Q).symm (decoratePortEquiv fresh Q (.inr ()))))) = _
    rw [Equiv.symm_apply_apply]
    exact (g.recipientTargetPorts_wire p q hne (.inr ())).trans hf.symm

 theorem ibpOtherSyntax_origin (v : Fin (n+1)) (hvp : v ≠ p) (hvq : v ≠ q)
    (Q : TaggedPending σ) (e : g.Slot v ≃ pendingPorts Q)
    (wire : LabelOrigin → Option (Option Edge))
    (he : ∀ u o, pendingPortOrigin Q u = some o →
      oldWire (Sum.elim Subtype.val Subtype.val (e.symm u)) = wire o) :
    ∀ u o, pendingPortOrigin (g.ibpOtherSyntax p q hne v hvp hvq Q e).1 u = some o →
      Sum.elim Subtype.val Subtype.val
        ((g.ibpOtherSyntax p q hne v hvp hvq Q e).2.symm u) = wire o := by
  intro u o hu
  exact (g.recipientOtherPorts_wire p q hne v hvp hvq (e.symm u)).trans (he u o hu)

end AcceleratedLogConcave.Tensor.Ordered.Graph
