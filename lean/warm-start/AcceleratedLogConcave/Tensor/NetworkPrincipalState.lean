import AcceleratedLogConcave.Tensor.NetworkIBPState
import AcceleratedLogConcave.Tensor.NetworkScoreState

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
namespace PrincipalState
variable {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2)) (i : Fin (r+2))
    (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))

/-- Actual principal IBP child at a distinct recipient occurrence. -/
def atRecipient
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (iq : Fin (before ++ [TaggedPending.formula node (.adjoint i E) J] ++ after).length)
    (hne : forestParentIndex before after (.formula node (.adjoint i E) J) ≠ iq) :
    SyntaxState (ibpForest (before ++ [.formula node (.adjoint i E) J] ++ after)
      (forestParentIndex before after (.formula node (.adjoint i E) J)) iq
      (.formula (node.child false) E J) ((S.pending (S.occurrence iq)).decorate (.ibp node))) := by
  let ip := forestParentIndex before after (.formula node (.adjoint i E) J)
  let p := S.occurrence ip
  let q := S.occurrence iq
  have hpq : p ≠ q := fun h => hne (S.occurrence.injective h)
  let e := ScoreState.parentPorts node E i J before after S
  let A := S.graph.ibpOperandSyntax p q hpq node E i J e
  let B := S.graph.ibpRecipientSyntax p q hpq (.ibp node) (S.pending q) (S.ports q)
  let wire := scoreOriginWire node S.originWire
  have hOld : ∀ v u o, pendingPortOrigin (S.pending v) u = some o →
      oldWire (S.originWire o) = wire o := by
    intro v u o hu
    simp only [wire, scoreOriginWire, ite_eq_right
      (S.adjoint_origin_fresh node E i J before after hs hinv v u o hu)]
  have hA : ∀ u o, pendingPortOrigin A.1 u = some o →
      Sum.elim Subtype.val Subtype.val (A.2.symm u) = wire o := by
    apply S.graph.ibpOperandSyntax_origin
    intro u
    erw [S.formulaPorts_origin _ node (.adjoint i E) J _ u]
    have hf : J.get u ≠ .ibp node :=
      adjoint_pendingPortOrigin_ne node E i J before after hs hinv
        (.formula node (.adjoint i E) J) (by simp) (.inl u) (J.get u) rfl
    simp only [wire, scoreOriginWire, ite_eq_right hf]
  have hB : ∀ u o, pendingPortOrigin B.1 u = some o →
      Sum.elim Subtype.val Subtype.val (B.2.symm u) = wire o := by
    apply S.graph.ibpRecipientSyntax_origin
    · simp [wire, scoreOriginWire]
    · intro u o hu
      rw [S.origin_spec q u o hu]
      exact hOld q u o hu
  exact S.ibpAt ip iq hne _ _ A B rfl rfl wire hOld hA hB

end PrincipalState
end AcceleratedLogConcave.Tensor.Ordered.Graph
