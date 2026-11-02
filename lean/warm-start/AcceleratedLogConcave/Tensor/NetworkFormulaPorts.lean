import AcceleratedLogConcave.Tensor.NetworkSyntaxState

noncomputable section
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
namespace SyntaxState
variable {s : List (TaggedPending σ)} (S : SyntaxState s)

/-- Extract the actual parent slots from its retained literal formula identity. -/
def formulaPorts {r : ℕ} (v : Fin (S.n+1)) (a : NodeAddress) (E : Expr σ r)
    (J : List LabelOrigin) (h : S.pending v = .formula a E J) :
    S.graph.Slot v ≃ (Fin J.length ⊕ Fin r) :=
  (S.ports v).trans (Equiv.cast (congrArg pendingPorts h))

theorem formulaPorts_origin {r : ℕ} (v : Fin (S.n+1)) (a : NodeAddress) (E : Expr σ r)
    (J : List LabelOrigin) (h : S.pending v = .formula a E J) (u : Fin J.length) :
    Sum.elim Subtype.val Subtype.val ((S.formulaPorts v a E J h).symm (.inl u)) =
      S.originWire (J.get u) := by
  change Sum.elim Subtype.val Subtype.val
    ((S.ports v).symm ((Equiv.cast (congrArg pendingPorts h)).symm (.inl u))) = _
  apply S.origin_spec
  have transport (q : TaggedPending σ) (hq : q = .formula a E J) :
      pendingPortOrigin q ((Equiv.cast (congrArg pendingPorts hq)).symm (.inl u)) =
        some (J.get u) := by
    subst q
    rfl
  exact transport (S.pending v) h

end SyntaxState
end AcceleratedLogConcave.Tensor.Ordered.Graph
