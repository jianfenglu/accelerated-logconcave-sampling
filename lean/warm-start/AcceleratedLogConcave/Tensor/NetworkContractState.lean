import AcceleratedLogConcave.Tensor.NetworkSyntaxSplitState
import AcceleratedLogConcave.Tensor.NetworkContractChildSyntax
import AcceleratedLogConcave.Tensor.NetworkFormulaPorts

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

 def transportSyntaxAt {n : ℕ} {Edge : Type*} (g : Graph n Edge)
    {v w : Fin (n+1)} (h : v = w) (P : g.SyntaxAt (σ := σ) v) : g.SyntaxAt (σ := σ) w := h ▸ P

 theorem transportSyntaxAt_fst {n : ℕ} {Edge : Type*} (g : Graph n Edge)
    {v w : Fin (n+1)} (h : v = w) (P : g.SyntaxAt (σ := σ) v) :
    (transportSyntaxAt g h P).1 = P.1 := by subst w; rfl

 theorem transportSyntaxAt_origin {n : ℕ} {Edge : Type*} (g : Graph n Edge)
    {v w : Fin (n+1)} (h : v = w) (P : g.SyntaxAt (σ := σ) v)
    (wire : LabelOrigin → Option Edge)
    (hP : ∀ u o, pendingPortOrigin P.1 u = some o →
      Sum.elim Subtype.val Subtype.val (P.2.symm u) = wire o) :
    ∀ u o, pendingPortOrigin (transportSyntaxAt g h P).1 u = some o →
      Sum.elim Subtype.val Subtype.val ((transportSyntaxAt g h P).2.symm u) = wire o := by
  subst w
  exact hP

namespace ContractState
variable {r s : ℕ} (node : NodeAddress) (E : Expr σ (r+2)) (F : Expr σ (s+2))
    (i : Fin (r+2)) (k : Fin (s+2)) (J : List LabelOrigin)
    (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.contract E F i k) J] ++ after))

def parentVertex := S.occurrence (forestParentIndex before after (.formula node (.contract E F i k) J))

def parentPorts : S.graph.Slot (parentVertex node E F i k J before after S) ≃
    (Fin J.length ⊕ Fin (r+s+2)) :=
  S.formulaPorts _ node (.contract E F i k) J (by
    rw [parentVertex, S.occurrence_spec]
    simp [forestParentIndex])

/-- Computed state with the orientation and all child data retained as arguments. -/
def ofOrientation
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ routes (List.finRange J.length))
    (part : S.graph.Slot (parentVertex node E F i k J before after S) → Bool) (b : Bool)
    (hi : ∃ q : S.graph.InPort (parentVertex node E F i k J before after S), part (.inl q) = false)
    (ho : ∃ q : S.graph.OutPort (parentVertex node E F i k J before after S), part (.inr q) = true)
    (hg : (S.graph.replaceVertex (parentVertex node E F i k J before after S) part).Admissible)
    (hlf : ∀ u, part (S.graph.decoratedLeftFreeSlot (parentVertex node E F i k J before after S) (parentPorts node E F i k J before after S) u) = b)
    (hrf : ∀ u, part (S.graph.decoratedRightFreeSlot (parentVertex node E F i k J before after S) (parentPorts node E F i k J before after S) u) = !b)
    (hll : ∀ u ∈ route.1, part (S.graph.decoratedLabelSlot (parentVertex node E F i k J before after S) (parentPorts node E F i k J before after S) u) = b)
    (hrl : ∀ u ∈ route.2, part (S.graph.decoratedLabelSlot (parentVertex node E F i k J before after S) (parentPorts node E F i k J before after S) u) = !b) :
    SyntaxState (before ++
      [.formula (node.child false) E (route.1.map J.get),
       .formula (node.child true) F (route.2.map J.get)] ++ after) := by
  let p := parentVertex node E F i k J before after S
  let e := parentPorts node E F i k J before after S
  let L := S.graph.contractChildSyntax p part hi ho J rfl route.1 (node.child false) E b i
    (S.graph.routeLeftSelected p e route hr part b hlf hrf hll hrl)
  let R := S.graph.contractChildSyntax p part hi ho J rfl route.2 (node.child true) F (!b) k
    (S.graph.routeRightSelected p e route hr part b hlf hrf hll hrl)
  have hL : ∀ u o, pendingPortOrigin L.1 u = some o →
      Sum.elim Subtype.val Subtype.val (L.2.symm u) = oldWire (S.originWire o) := by
    apply S.graph.contractChildSyntax_origin
    intro u
    rw [routeLeftSelected_derivative]
    exact S.formulaPorts_origin _ node (.contract E F i k) J _ (route.1.get u)
  have hR : ∀ u o, pendingPortOrigin R.1 u = some o →
      Sum.elim Subtype.val Subtype.val (R.2.symm u) = oldWire (S.originWire o) := by
    apply S.graph.contractChildSyntax_origin
    intro u
    rw [routeRightSelected_derivative]
    exact S.formulaPorts_origin _ node (.contract E F i k) J _ (route.2.get u)
  cases b
  · let A := transportSyntaxAt _ (splitVertex_parent_false p) L
    let B := transportSyntaxAt _ (splitVertex_parent_true p) R
    exact S.splitOccurrence before after _ _ _ part false hg A B
      (by rw [transportSyntaxAt_fst]; rfl) (by rw [transportSyntaxAt_fst]; rfl)
      (transportSyntaxAt_origin _ _ L _ hL) (transportSyntaxAt_origin _ _ R _ hR)
  · let A := transportSyntaxAt _ (splitVertex_parent_false p) R
    let B := transportSyntaxAt _ (splitVertex_parent_true p) L
    exact S.splitOccurrence before after _ _ _ part true hg A B
      (by rw [transportSyntaxAt_fst]; rfl) (by rw [transportSyntaxAt_fst]; rfl)
      (transportSyntaxAt_origin _ _ R _ hR) (transportSyntaxAt_origin _ _ L _ hL)


include i k S in
/-- Each actual positional contraction route has a fully retained syntax state. -/
theorem route_state_exists
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ routes (List.finRange J.length)) :
    Nonempty (SyntaxState (before ++
      [.formula (node.child false) E (route.1.map J.get),
       .formula (node.child true) F (route.2.map J.get)] ++ after)) := by
  let p := parentVertex node E F i k J before after S
  let e := parentPorts node E F i k J before after S
  obtain ⟨part,b,hi,ho,hg,hlf,hrf,hll,hrl⟩ :=
    S.graph.exists_decorated_orientation p S.admissible e route hr
  exact ⟨ofOrientation node E F i k J before after S route hr part b hi ho hg hlf hrf hll hrl⟩

end ContractState
end AcceleratedLogConcave.Tensor.Ordered.Graph
