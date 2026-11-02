import AcceleratedLogConcave.Tensor.NetworkScoreStateFreshness
import AcceleratedLogConcave.Tensor.NetworkScoreStateChild
import AcceleratedLogConcave.Tensor.NetworkScoreStateSplit
import AcceleratedLogConcave.Tensor.NetworkContractState

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

theorem transportSyntaxAt_origin_newWire {n : ℕ} {Edge : Type*} (g : Graph n Edge)
    {v w : Fin (n+1)} (h : v=w) (P : g.SyntaxAt (σ := σ) v)
    (wire : LabelOrigin → Option Edge)
    (hP : ∀ u o, pendingPortOrigin P.1 u = some o →
      Sum.elim Subtype.val Subtype.val (P.2.symm u) = wire o) :
    ∀ u o, pendingPortOrigin (transportSyntaxAt g h P).1 u = some o →
      Sum.elim Subtype.val Subtype.val ((transportSyntaxAt g h P).2.symm u) = wire o := by
  subst w
  exact hP

namespace ScoreState
variable {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2)) (i : Fin (r+2))
    (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))

def parentVertex := S.occurrence (forestParentIndex before after (.formula node (.adjoint i E) J))

def parentPorts : S.graph.Slot (parentVertex node E i J before after S) ≃
    (Fin J.length ⊕ Fin (r+1)) :=
  S.formulaPorts _ node (.adjoint i E) J (by
    rw [parentVertex,S.occurrence_spec]
    simp [forestParentIndex])

def ofOrientation
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ scoreRoutes (List.finRange J.length))
    (part : S.graph.Slot (parentVertex node E i J before after S) → Bool) (b : Bool)
    (hi : ∃ q : S.graph.InPort (parentVertex node E i J before after S), part (.inl q) = false)
    (ho : ∃ q : S.graph.OutPort (parentVertex node E i J before after S), part (.inr q) = true)
    (hg : (S.graph.replaceVertex (parentVertex node E i J before after S) part).Admissible)
    (hscore : ∀ u ∈ route.1, part (S.graph.decoratedLabelSlot (parentVertex node E i J before after S)
      (parentPorts node E i J before after S) u) = b)
    (hop : ∀ u ∈ route.2, part (S.graph.decoratedLabelSlot (parentVertex node E i J before after S)
      (parentPorts node E i J before after S) u) = !b)
    (hfree : ∀ u, part (S.graph.adjointFreeSlot (parentVertex node E i J before after S)
      (parentPorts node E i J before after S) u) = !b) :
    SyntaxState (before ++
      [.score node (route.1.map J.get) (by simpa using scoreRoutes_left_ne_nil _ route hr),
       .formula (node.child false) E (route.2.map J.get)] ++ after) := by
  let p := parentVertex node E i J before after S
  let e := parentPorts node E i J before after S
  let L := S.graph.scoreChildSyntax p part hi ho J rfl route.1
    (scoreRoutes_left_ne_nil _ route hr) node b
    (S.graph.scoreRouteSelected p e route hr part b hscore hop hfree) (σ := σ)
  let R := S.graph.contractChildSyntax p part hi ho J rfl route.2 (node.child false) E (!b) i
    (S.graph.scoreOperandSelected p e route hr part b hscore hop hfree)
  let wire := scoreOriginWire node S.originWire
  have hJfresh (u : Fin J.length) : J.get u ≠ .ibp node :=
    adjoint_pendingPortOrigin_ne node E i J before after hs hinv
      (.formula node (.adjoint i E) J) (by simp) (.inl u) (J.get u) rfl
  have hOld : ∀ v u o, pendingPortOrigin (S.pending v) u = some o →
      oldWire (S.originWire o) = wire o := by
    intro v u o hu
    simp only [wire,scoreOriginWire,ite_eq_right
      (S.adjoint_origin_fresh node E i J before after hs hinv v u o hu)]
  have hL : ∀ u o, pendingPortOrigin L.1 u = some o →
      Sum.elim Subtype.val Subtype.val (L.2.symm u) = wire o := by
    apply S.graph.scoreChildSyntax_origin
    · intro u
      exact hJfresh _
    · intro u
      rw [scoreRouteSelected_apply]
      exact S.formulaPorts_origin _ node (.adjoint i E) J _ (route.1.get u)
  have hRold : ∀ u o, pendingPortOrigin R.1 u = some o →
      Sum.elim Subtype.val Subtype.val (R.2.symm u) = oldWire (S.originWire o) := by
    apply S.graph.contractChildSyntax_origin
    intro u
    rw [scoreOperandSelected_derivative]
    exact S.formulaPorts_origin _ node (.adjoint i E) J _ (route.2.get u)
  have hR : ∀ u o, pendingPortOrigin R.1 u = some o →
      Sum.elim Subtype.val Subtype.val (R.2.symm u) = wire o := by
    intro u o hu
    rw [hRold u o hu]
    have hn : o ≠ .ibp node := by
      change Fin (route.2.map J.get).length ⊕ Fin (r+2) at u
      cases u with
      | inr v => cases hu
      | inl v =>
        have he : o = J.get (route.2.get (Fin.cast (List.length_map _) v)) := by
          simpa [R,contractChildSyntax,pendingPortOrigin] using hu.symm
        rw [he]
        exact hJfresh _
    simp only [wire,scoreOriginWire,ite_eq_right hn]
  cases b
  · let A := transportSyntaxAt _ (splitVertex_parent_false p) L
    let B := transportSyntaxAt _ (splitVertex_parent_true p) R
    exact S.splitOccurrenceNewWire before after _ _ _ part false hg A B
      (by rw [transportSyntaxAt_fst]; rfl) (by rw [transportSyntaxAt_fst]; rfl)
      wire hOld (transportSyntaxAt_origin_newWire _ _ L _ hL)
      (transportSyntaxAt_origin_newWire _ _ R _ hR)
  · let A := transportSyntaxAt _ (splitVertex_parent_false p) R
    let B := transportSyntaxAt _ (splitVertex_parent_true p) L
    exact S.splitOccurrenceNewWire before after _ _ _ part true hg A B
      (by rw [transportSyntaxAt_fst]; rfl) (by rw [transportSyntaxAt_fst]; rfl)
      wire hOld (transportSyntaxAt_origin_newWire _ _ R _ hR)
      (transportSyntaxAt_origin_newWire _ _ L _ hL)

include i S in
theorem route_state_exists
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (route : List (Fin J.length) × List (Fin J.length))
    (hr : route ∈ scoreRoutes (List.finRange J.length)) :
    Nonempty (SyntaxState (before ++
      [.score node (route.1.map J.get) (by simpa using scoreRoutes_left_ne_nil _ route hr),
       .formula (node.child false) E (route.2.map J.get)] ++ after)) := by
  let p := parentVertex node E i J before after S
  let e := parentPorts node E i J before after S
  obtain ⟨part,b,hi,ho,hg,hscore,hop,hfree⟩ := S.graph.exists_score_orientation p S.admissible e route hr
  exact ⟨ofOrientation node E i J before after S hs hinv route hr part b hi ho hg hscore hop hfree⟩

end ScoreState
end AcceleratedLogConcave.Tensor.Ordered.Graph
