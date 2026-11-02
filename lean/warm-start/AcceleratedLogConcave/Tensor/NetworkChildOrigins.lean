import AcceleratedLogConcave.Tensor.NetworkRouteSlots
import AcceleratedLogConcave.Tensor.NetworkSyntaxState

noncomputable section
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool)
    (hi : ∃ q : g.InPort p, part (.inl q) = false)
    (ho : ∃ q : g.OutPort p, part (.inr q) = true)

theorem inheritedChildSlot_wire (b : Bool) (z : g.Slot p) (hz : part z = b) :
    Sum.elim Subtype.val Subtype.val (g.inheritedChildSlot p part hi ho b z hz) =
      oldWire (Sum.elim Subtype.val Subtype.val z) := by
  cases z <;> rfl

/-- The child derivative positions keep the parent's origin wire exactly. -/
theorem decoratedOperandEquiv_origin {a r : ℕ} (b : Bool) (i : Fin (r+2))
    (selected : (Fin a ⊕ Fin (r+1)) ≃ {z : g.Slot p // part z = b})
    (origin : Fin a → LabelOrigin) (wire : LabelOrigin → Option Edge)
    (h : ∀ u, Sum.elim Subtype.val Subtype.val (selected (.inl u)).val = wire (origin u))
    (u : Fin a) :
    Sum.elim Subtype.val Subtype.val
      (g.decoratedOperandEquiv p part hi ho b i selected (.inl u)) =
      oldWire (wire (origin u)) := by
  rw [decoratedOperandEquiv_derivative, inheritedChildSlot_wire, h]

end AcceleratedLogConcave.Tensor.Ordered.Graph
