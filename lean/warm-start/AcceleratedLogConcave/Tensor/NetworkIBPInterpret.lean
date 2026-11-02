import AcceleratedLogConcave.Tensor.NetworkIBPForest
import AcceleratedLogConcave.Tensor.ReductionExpansion

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

private theorem get_tag_injective {s : List (TaggedPending σ)}
    (hn : (s.map TaggedPending.tag).Nodup) :
    Function.Injective (fun u : Fin s.length => (s.get u).tag) := by
  intro u v h
  exact recipient_index_unique s hn u v h

/-- The two-position state update is the existing literal event interpreter. -/
theorem ibpForest_eq_interpret {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2))
    (i : Fin (r+2)) (J : List LabelOrigin) (s : List (TaggedPending σ))
    (ip iq : Fin s.length) (hne : ip ≠ iq)
    (hp : s.get ip = .formula node (.adjoint i E) J)
    (hn : (s.map TaggedPending.tag).Nodup) :
    ibpForest s ip iq (.formula (node.child false) E J) ((s.get iq).decorate (.ibp node)) =
      interpretEvent (.ibp node (s.get iq).tag) s := by
  let f : Fin s.length → TaggedPending σ := fun u =>
    if u = iq then (s.get iq).decorate (.ibp node)
    else if u = ip then .formula (node.child false) E J else s.get u
  have htag : (s.get iq).tag ≠ .formula node := by
    intro h
    apply hne
    exact (get_tag_injective hn (h.trans (congrArg TaggedPending.tag hp).symm)).symm
  have hlocal (u : Fin s.length) :
      interpretPending (.ibp node (s.get iq).tag) (s.get u) = [f u] := by
    by_cases huq : u = iq
    · subst u
      simp only [interpretPending, Event.node, ite_eq_right htag, ite_true, f]
    by_cases hup : u = ip
    · subst u
      simp only [interpretPending, Event.node, hp, TaggedPending.tag, ite_true, eventRedex, f, ite_eq_right hne]
    have ha : (s.get u).tag ≠ .formula node := by
      intro h
      exact hup (get_tag_injective hn (h.trans (congrArg TaggedPending.tag hp).symm))
    have hb : (s.get u).tag ≠ (s.get iq).tag := fun h => huq (get_tag_injective hn h)
    simp only [interpretPending, Event.node, ite_eq_right ha, ite_eq_right hb, f, ite_eq_right huq, ite_eq_right hup]
  have hinterp : interpretEvent (.ibp node (s.get iq).tag) s = List.ofFn f := by
    unfold interpretEvent
    conv_lhs => arg 2; rw [← List.ofFn_get s]
    rw [List.ofFn_eq_map, List.flatMap_map]
    simp_rw [hlocal]
    rw [← List.map_eq_flatMap]
    exact List.ofFn_eq_map.symm
  rw [hinterp]
  apply List.ext_getElem
  · simp [ibpForest_length]
  · intro u hu hv
    have hh := ibpForest_get s ip iq (.formula (node.child false) E J)
      ((s.get iq).decorate (.ibp node)) ⟨u, by simpa [ibpForest] using hu⟩
    simpa [f] using hh

 theorem ibpForest_taggedStep {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2))
    (i : Fin (r+2)) (J : List LabelOrigin) (s : List (TaggedPending σ))
    (ip iq : Fin s.length) (hne : ip ≠ iq)
    (hp : s.get ip = .formula node (.adjoint i E) J)
    (hn : (s.map TaggedPending.tag).Nodup) :
    TaggedStep (.ibp node (s.get iq).tag)
      (ibpForest s ip iq (.formula (node.child false) E J) ((s.get iq).decorate (.ibp node))) s := by
  have htag : (s.get iq).tag ≠ .formula node := by
    intro h
    exact hne (get_tag_injective hn (h.trans (congrArg TaggedPending.tag hp).symm)).symm
  obtain ⟨t, ht⟩ := ibp_step_of_recipient node E i J
    (hp ▸ List.get_mem s ip) (List.get_mem s iq) htag
  rw [ibpForest_eq_interpret node E i J s ip iq hne hp hn, ht.interpret hn]
  exact ht

end AcceleratedLogConcave.Tensor.Ordered.Graph
