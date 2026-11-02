import AcceleratedLogConcave.Tensor.PhaseConstructorIntegralBound
import AcceleratedLogConcave.Tensor.NetworkLocalDerivativeIntegral

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

private theorem filter_other_occurrences (before after : List (TaggedPending σ))
    (p : TaggedPending σ)
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
theorem SyntaxState.phase_integral_le_local_event_costs
    {s : List (TaggedPending σ)} (S : SyntaxState s)
    (P : PhaseAnalyticEnvironment σ D)
    (hs : (forestSupport s).Nodup) (hinv : (originInventory s).Nodup)
    (ha : firstNonterminal s ≠ none)
    (cost : Event → ℝ)
    (ih : ∀ event target, CanonicalStep event target s →
      ∀ child : SyntaxState target, |child.phaseIntegral P| ≤ cost event) :
    |S.phaseIntegral P| ≤ ((localEvents s).map cost).sum := by
  cases hf : firstNonterminal s with
  | none => exact False.elim (ha hf)
  | some node =>
    obtain ⟨before,p,after,rfl,hp⟩ := firstNonterminal_decompose hf
    have hn := liveTags_nodup_of_support _ hs
    rw [localEvents_selected before after p node hp hf hn]
    cases p with
    | score a J h => simp [TaggedPending.activeNode] at hp
    | formula a e J =>
      cases e with
      | coefficient c => simp [TaggedPending.activeNode] at hp
      | derivative e =>
        have he : a = node := Option.some.inj hp
        subst node
        simp only [pendingEvents,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
        apply integral_derivative_le a e J before after S (liveTags_nodup_of_support _ hs) hinv
          P.coefficients P.potential P.toSmoothGibbsEnvironment.law (cost (.derivative a))
        intro child
        exact ih _ _ ⟨TaggedStep.derivative a e J before after,hf⟩ child
      | permute perm e =>
        have he : a = node := Option.some.inj hp
        subst node
        simpa [pendingEvents] using phase_integral_permute_le_event_cost P a perm e J
          before after S hn hf cost ih
      | contract e f i k =>
        have he : a = node := Option.some.inj hp
        subst node
        simpa only [pendingEvents,List.map_map,Function.comp_def] using phase_integral_contract_le_event_costs P a e f i k J
          before after S hf cost ih
      | adjoint i e =>
        have he : a = node := Option.some.inj hp
        subst node
        have hfilter := filter_other_occurrences before after (.formula a (.adjoint i e) J) hn
        change (before ++ [TaggedPending.formula a (.adjoint i e) J] ++ after).filter
          (fun q => q.tag != OccurrenceTag.formula a) = before ++ after at hfilter
        simp only [pendingEvents,List.map_append,List.sum_append,List.map_map,Function.comp_def]
        rw [hfilter]
        exact phase_integral_adjoint_le_event_costs P a e i J before after S hs hinv hf cost ih

end AcceleratedLogConcave.Tensor.Ordered.Graph
