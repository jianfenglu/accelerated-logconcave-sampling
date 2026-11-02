import AcceleratedLogConcave.Tensor.NetworkIBPInterpret

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

/-- Distinct occurrence tags separate the selected redex from every other occurrence. -/
theorem other_tag_ne_selected (before after : List (TaggedPending σ)) (p : TaggedPending σ)
    (hn : ((before ++ [p] ++ after).map TaggedPending.tag).Nodup) :
    ∀ q ∈ before ++ after, q.tag ≠ p.tag := by
  have h : ((before.map TaggedPending.tag ++ [p.tag]) ++ after.map TaggedPending.tag).Nodup := by
    simpa only [List.map_append,List.map_cons,List.map_nil] using hn
  have hl := (List.nodup_append.mp (List.nodup_append.mp h).1).2.2
  have hr := (List.nodup_append.mp h).2.2
  intro q hq he
  rcases List.mem_append.mp hq with hq | hq
  · exact hl p.tag (List.mem_map.mpr ⟨q,hq,he⟩) p.tag (by simp) rfl
  · exact hr p.tag (by simp) p.tag (List.mem_map.mpr ⟨q,hq,he⟩) rfl

/-- The existing local event list is exactly the selected occurrence's event list.
This preserves its order and every positional route, without a cardinality argument. -/
theorem localEvents_selected (before after : List (TaggedPending σ)) (p : TaggedPending σ)
    (node : NodeAddress) (hp : p.activeNode = some node)
    (hf : firstNonterminal (before ++ [p] ++ after) = some node)
    (hn : ((before ++ [p] ++ after).map TaggedPending.tag).Nodup) :
    localEvents (before ++ [p] ++ after) = pendingEvents (before ++ [p] ++ after) p := by
  let s := before ++ [p] ++ after
  let f := fun q : TaggedPending σ =>
    if q.activeNode = firstNonterminal s then pendingEvents s q else []
  have ho := other_tag_ne_selected before after p hn
  have hz (q : TaggedPending σ) (hq : q ∈ before ++ after) : f q = [] := by
    have hne : q.activeNode ≠ firstNonterminal s := by
      intro he
      have hqa : q.activeNode = some node := he.trans hf
      exact ho q hq ((TaggedPending.activeNode_tag hqa).trans
        (TaggedPending.activeNode_tag hp).symm)
    exact ite_eq_right hne
  have hb : before.flatMap f = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro q hq
    exact hz q (List.mem_append_left _ hq)
  have ha : after.flatMap f = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro q hq
    exact hz q (List.mem_append_right _ hq)
  change (before ++ [p] ++ after).flatMap f = _
  rw [List.flatMap_append,List.flatMap_append,hb,ha]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.nil_append]
  exact ite_eq_left (hp.trans hf.symm)

/-- An existing exhaustive tree node has exactly the canonical event/target list,
up to order. This uses its supplied completeness and uniqueness, not a new count. -/
theorem expansion_edges_perm_next {s : List (TaggedPending σ)}
    (edges : List (Event × List (TaggedPending σ)))
    (legal : ∀ edge ∈ edges, CanonicalStep edge.1 edge.2 s)
    (complete : ∀ event target, CanonicalStep event target s → (event,target) ∈ edges)
    (unique : (edges.map Prod.fst).Nodup)
    (hn : (s.map TaggedPending.tag).Nodup) (hi : (originInventory s).Nodup) :
    edges.Perm (nextBranches s) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
    (List.Nodup.of_map Prod.fst unique)
    (List.Nodup.of_map Prod.fst (nextBranches_unique hn hi))
  ext edge
  simp only [List.mem_toFinset]
  constructor
  · intro h
    exact nextBranches_complete hn (legal edge h)
  · intro h
    exact complete edge.1 edge.2 (nextBranches_legal hn edge h)

end AcceleratedLogConcave.Tensor.Ordered.Graph
