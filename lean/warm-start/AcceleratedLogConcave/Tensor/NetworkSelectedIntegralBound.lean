import AcceleratedLogConcave.Tensor.NetworkConstructorIntegralBound

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords ActualCoefficientIntegrability Conditional
open Analysis.PositiveVarianceSlab
variable {D : ℕ}

private theorem filter_other_occurrences (before after : List (TaggedPending signature))
    (p : TaggedPending signature)
    (hn : ((before ++ [p] ++ after).map TaggedPending.tag).Nodup) :
    (before ++ [p] ++ after).filter (fun q => q.tag != p.tag) = before ++ after := by
  have ho := other_tag_ne_selected before after p hn
  have hb : before.filter (fun q => q.tag != p.tag) = before := by
    apply List.filter_eq_self.mpr
    intro q hq
    simpa using ho q (List.mem_append_left _ hq)
  have ha : after.filter (fun q => q.tag != p.tag) = after := by
    apply List.filter_eq_self.mpr
    intro q hq
    simpa using ho q (List.mem_append_right _ hq)
  rw [List.filter_append,List.filter_append,hb,ha]
  simp


/-- Actual local induction inequality for the existing scheduler and its literal
ordered event list. The bound premise is precisely the child induction hypothesis. -/
theorem SyntaxState.integral_le_local_event_costs
    {s : List (TaggedPending signature)} (S : SyntaxState s)
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    {t : ℝ} (ht : t ∈ Set.Icc (left d.b) (right d.b))
    (hs : (forestSupport s).Nodup) (hinv : (originInventory s).Nodup)
    (hm : IsMaterialForest s) (ha : firstNonterminal s ≠ none)
    (cost : Event → ℝ)
    (ih : ∀ event target, CanonicalStep event target s →
      ∀ child : SyntaxState target, |child.actualIntegral d t| ≤ cost event) :
    |S.actualIntegral d t| ≤ ((localEvents s).map cost).sum := by
  cases hf : firstNonterminal s with
  | none => exact False.elim (ha hf)
  | some node =>
    obtain ⟨before,p,after,rfl,hp⟩ := firstNonterminal_decompose hf
    have hn := liveTags_nodup_of_support _ hs
    rw [localEvents_selected before after p node hp hf hn]
    cases p with
    | score a J h => simp [TaggedPending.activeNode] at hp
    | formula a e J =>
      have hmat : IsMaterialExpression e := hm (.formula a e J) (by simp)
      cases e with
      | coefficient c => simp [TaggedPending.activeNode] at hp
      | derivative e => exact False.elim hmat
      | permute perm e =>
        have he : a = node := Option.some.inj hp
        subst node
        simpa [pendingEvents] using integral_permute_le_event_cost d t a perm e J
          before after S hn hf cost ih
      | contract e f i k =>
        have he : a = node := Option.some.inj hp
        subst node
        simpa only [pendingEvents,List.map_map,Function.comp_def] using integral_contract_le_event_costs d ht a e f i k J
          before after S hf cost ih
      | adjoint i e =>
        have he : a = node := Option.some.inj hp
        subst node
        have hfilter := filter_other_occurrences before after (.formula a (.adjoint i e) J) hn
        change (before ++ [TaggedPending.formula a (.adjoint i e) J] ++ after).filter
          (fun q => q.tag != OccurrenceTag.formula a) = before ++ after at hfilter
        simp only [pendingEvents,List.map_append,List.sum_append,List.map_map,Function.comp_def]
        rw [hfilter]
        exact integral_adjoint_le_event_costs d ht a e i J before after S hs hinv hf cost ih

end AcceleratedLogConcave.Tensor.Ordered.Graph
