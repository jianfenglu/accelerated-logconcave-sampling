import AcceleratedLogConcave.Tensor.NetworkAddedSlots
import AcceleratedLogConcave.Tensor.NetworkRecipient

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge)
    (p q : Fin (n+1)) (hne : p ≠ q)

private def portWire {n : ℕ} {Edge : Type*} {g : Graph n Edge} {v : Fin (n+1)} : g.Slot v → Option Edge :=
  Sum.elim Subtype.val Subtype.val

private def graphSlotEquiv {n : ℕ} {Edge : Type*} {g h : Graph n Edge}
    (eq : g = h) {v : Fin (n+1)} : g.Slot v ≃ h.Slot v := eq ▸ Equiv.refl _

private theorem graphSlotEquiv_wire {n : ℕ} {Edge : Type*} {g h : Graph n Edge}
    (eq : g = h) {v : Fin (n+1)} (u : g.Slot v) :
    portWire (graphSlotEquiv eq u) = portWire u := by subst h; rfl

/-- Fixed endpoint inventory for the adjoint operand, independently of vertex order. -/
def recipientSourcePorts : (g.Slot p ⊕ Unit) ≃ (g.recipientGraph p q hne).Slot p := by
  by_cases h : p < q
  · exact (g.addedSourceSlotEquiv p q h).trans (graphSlotEquiv (by simp [recipientGraph, h]))
  · exact (g.addedTargetSlotEquiv q p (by omega)).trans
      (graphSlotEquiv (by simp [recipientGraph, h]))

/-- Fixed endpoint inventory for the differentiated recipient. -/
def recipientTargetPorts : (g.Slot q ⊕ Unit) ≃ (g.recipientGraph p q hne).Slot q := by
  by_cases h : p < q
  · exact (g.addedTargetSlotEquiv p q h).trans (graphSlotEquiv (by simp [recipientGraph, h]))
  · exact (g.addedSourceSlotEquiv q p (by omega)).trans
      (graphSlotEquiv (by simp [recipientGraph, h]))

/-- All untouched occurrences retain precisely their old coordinate inventory. -/
def recipientOtherPorts (v : Fin (n+1)) (hvp : v ≠ p) (hvq : v ≠ q) :
    g.Slot v ≃ (g.recipientGraph p q hne).Slot v := by
  by_cases h : p < q
  · exact (g.addedOtherSlotEquiv p q h v hvp hvq).trans
      (graphSlotEquiv (by simp [recipientGraph, h]))
  · exact (g.addedOtherSlotEquiv q p (by omega) v hvq hvp).trans
      (graphSlotEquiv (by simp [recipientGraph, h]))

theorem recipientSourcePorts_wire (u : g.Slot p ⊕ Unit) :
    portWire (g.recipientSourcePorts p q hne u) =
      Sum.elim (fun a => oldWire (portWire a)) (fun _ => some none) u := by
  unfold recipientSourcePorts
  split_ifs with h
  all_goals simp only [Equiv.trans_apply, graphSlotEquiv_wire]
  all_goals cases u with
  | inl a => cases a <;> rfl
  | inr a => cases a; rfl

theorem recipientTargetPorts_wire (u : g.Slot q ⊕ Unit) :
    portWire (g.recipientTargetPorts p q hne u) =
      Sum.elim (fun a => oldWire (portWire a)) (fun _ => some none) u := by
  unfold recipientTargetPorts
  split_ifs with h
  all_goals simp only [Equiv.trans_apply, graphSlotEquiv_wire]
  all_goals cases u with
  | inl a => cases a <;> rfl
  | inr a => cases a; rfl

theorem recipientOtherPorts_wire (v : Fin (n+1)) (hvp : v ≠ p) (hvq : v ≠ q)
    (u : g.Slot v) :
    portWire (g.recipientOtherPorts p q hne v hvp hvq u) = oldWire (portWire u) := by
  unfold recipientOtherPorts
  split_ifs <;> simp only [Equiv.trans_apply, graphSlotEquiv_wire]
  all_goals cases u <;> rfl

end AcceleratedLogConcave.Tensor.Ordered.Graph
