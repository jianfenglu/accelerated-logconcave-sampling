import AcceleratedLogConcave.Tensor.NetworkIBPInterpret
import AcceleratedLogConcave.Tensor.PhaseContractIntegral
import AcceleratedLogConcave.Tensor.PhaseAdjointIntegral
import AcceleratedLogConcave.Tensor.NetworkLocalPermutationIntegral
import AcceleratedLogConcave.Tensor.NetworkOccurrenceSum

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

/-- Actual integral of a generic literal phase network. -/
def SyntaxState.phaseIntegral {s : List (TaggedPending σ)} (S : SyntaxState s)
    (P : PhaseAnalyticEnvironment σ D) : ℝ :=
  ∫ y, S.value P.coefficients P.potential y ∂P.toSmoothGibbsEnvironment.law

private theorem sum_list_positions {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ u : Fin l.length, f (l.get u) := by
  rw [← List.sum_ofFn]
  congr 1
  ext u
  simp

private theorem route_cost_positions (node : NodeAddress) (J : List LabelOrigin) (cost : Event → ℝ) :
    ((routes J).map (fun q => cost (.contract node q.1 q.2))).sum =
      ∑ u : Fin (routes (List.finRange J.length)).length,
        cost (.contract node (((routes (List.finRange J.length)).get u).1.map J.get)
          (((routes (List.finRange J.length)).get u).2.map J.get)) := by
  have hr := routes_map_exact J.get (List.finRange J.length)
  simp only [← List.ofFn_eq_map,List.ofFn_get] at hr
  rw [hr,List.map_map,sum_list_positions]
  rfl

/-- Contraction consumes exactly its existing canonical event costs. -/
theorem phase_integral_contract_le_event_costs
    (P : PhaseAnalyticEnvironment σ D)
    {r q : ℕ} (node : NodeAddress) (E : Expr σ (r+2)) (G : Expr σ (q+2))
    (i : Fin (r+2)) (k : Fin (q+2)) (J : List LabelOrigin)
    (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.contract E G i k) J] ++ after))
    (hf : firstNonterminal (before ++ [.formula node (.contract E G i k) J] ++ after) = some node)
    (cost : Event → ℝ)
    (ih : ∀ event target, CanonicalStep event target
      (before ++ [.formula node (.contract E G i k) J] ++ after) →
      ∀ child : SyntaxState target, |child.phaseIntegral P| ≤ cost event) :
    |S.phaseIntegral P| ≤ ((routes J).map (fun route => cost (.contract node route.1 route.2))).sum := by
  let child := fun u : Fin (routes (List.finRange J.length)).length =>
    ContractState.routeState node E G i k J before after S
      ((routes (List.finRange J.length)).get u) (List.get_mem _ _)
  have he : S.phaseIntegral P = ∑ u, (child u).phaseIntegral P :=
    ContractState.phase_integral_eq_routeState_sum node E G i k J before after S
      P
  rw [he,route_cost_positions]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro u _
  apply ih _ _ ⟨ContractState.routeState_taggedStep node E G i k J before after
    ((routes (List.finRange J.length)).get u) (List.get_mem _ _),hf⟩ (child u)

/-- Canonical permutation consumes its single existing event cost. -/
theorem phase_integral_permute_le_event_cost
    (P : PhaseAnalyticEnvironment σ D)
    {r : ℕ} (node : NodeAddress) (perm : Equiv.Perm (Fin r)) (E : Expr σ r)
    (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.permute perm E) J] ++ after))
    (hn : ((before ++ [TaggedPending.formula node (.permute perm E) J] ++ after).map TaggedPending.tag).Nodup)
    (hf : firstNonterminal (before ++ [.formula node (.permute perm E) J] ++ after) = some node)
    (cost : Event → ℝ)
    (ih : ∀ event target, CanonicalStep event target
      (before ++ [.formula node (.permute perm E) J] ++ after) →
      ∀ child : SyntaxState target, |child.phaseIntegral P| ≤ cost event) :
    |S.phaseIntegral P| ≤ cost (.permute node) := by
  apply integral_permutation_le node perm E J before after S hn
    P.coefficients P.potential P.toSmoothGibbsEnvironment.law (cost (.permute node))
  intro child
  exact ih _ _ ⟨TaggedStep.permute node perm E J before after,hf⟩ child

/-- The actual retained recipient forest is the existing canonical IBP target. -/
theorem PrincipalState.phase_atRecipient_taggedStep {r : ℕ} (node : NodeAddress)
    (E : Expr σ (r+2)) (i : Fin (r+2)) (J : List LabelOrigin)
    (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))
    (iq : Fin (before ++ [TaggedPending.formula node (.adjoint i E) J] ++ after).length)
    (hne : forestParentIndex before after (.formula node (.adjoint i E) J) ≠ iq)
    (hn : ((before ++ [TaggedPending.formula node (.adjoint i E) J] ++ after).map TaggedPending.tag).Nodup) :
    TaggedStep (.ibp node (S.pending (S.occurrence iq)).tag)
      (ibpForest (before ++ [.formula node (.adjoint i E) J] ++ after)
        (forestParentIndex before after (.formula node (.adjoint i E) J)) iq
        (.formula (node.child false) E J) ((S.pending (S.occurrence iq)).decorate (.ibp node)))
      (before ++ [.formula node (.adjoint i E) J] ++ after) := by
  rw [S.occurrence_spec]
  exact ibpForest_taggedStep node E i J _ _ iq hne (by simp [forestParentIndex]) hn

private theorem score_cost_positions (node : NodeAddress) (J : List LabelOrigin) (cost : Event → ℝ) :
    ((scoreRoutes J).map (fun q => cost (.score node q.1 q.2))).sum =
      ∑ u : Fin (scoreRoutes (List.finRange J.length)).length,
        cost (.score node (((scoreRoutes (List.finRange J.length)).get u).1.map J.get)
          (((scoreRoutes (List.finRange J.length)).get u).2.map J.get)) := by
  have hr := scoreRoutes_map_exact J.get (List.finRange J.length)
  simp only [← List.ofFn_eq_map,List.ofFn_get] at hr
  rw [hr,List.map_map,sum_list_positions]
  rfl

/-- Adjoint consumes its literal score routes and one IBP event per other occurrence. -/
theorem phase_integral_adjoint_le_event_costs
    (P : PhaseAnalyticEnvironment σ D)
    {r : ℕ} (node : NodeAddress) (E : Expr σ (r+2)) (i : Fin (r+2))
    (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hf : firstNonterminal (before ++ [.formula node (.adjoint i E) J] ++ after) = some node)
    (cost : Event → ℝ)
    (ih : ∀ event target, CanonicalStep event target
      (before ++ [.formula node (.adjoint i E) J] ++ after) →
      ∀ child : SyntaxState target, |child.phaseIntegral P| ≤ cost event) :
    |S.phaseIntegral P| ≤
      ((scoreRoutes J).map (fun route => cost (.score node route.1 route.2))).sum +
      ((before ++ after).map (fun q => cost (.ibp node q.tag))).sum := by
  let p := ScoreState.parentVertex node E i J before after S
  let scores := fun u : Fin (scoreRoutes (List.finRange J.length)).length =>
    ScoreState.routeState node E i J before after S hs hinv
      ((scoreRoutes (List.finRange J.length)).get u) (List.get_mem _ _)
  let principals := fun q : {q : Fin (S.n+1) // q ≠ p} =>
    PrincipalState.atRecipient node E i J before after S hs hinv (S.occurrence.symm q.val)
      (PrincipalState.phase_recipient_index_ne node E i J before after S q.val q.property)
  have he : S.phaseIntegral P = (∑ u, (scores u).phaseIntegral P) +
      ∑ q, (principals q).phaseIntegral P :=
    PrincipalState.phase_integral_adjoint_eq_children node E i J before after S
      P hs hinv
  have hscore (u) : |(scores u).phaseIntegral P| ≤
      cost (.score node (((scoreRoutes (List.finRange J.length)).get u).1.map J.get)
        (((scoreRoutes (List.finRange J.length)).get u).2.map J.get)) :=
    ih _ _ ⟨ScoreState.routeState_taggedStep node E i J before after _ (List.get_mem _ _),hf⟩ (scores u)
  have hprincipal (q : {q : Fin (S.n+1) // q ≠ p}) :
      |(principals q).phaseIntegral P| ≤ cost (.ibp node (S.pending q.val).tag) := by
    have hh := ih _ _ ⟨PrincipalState.phase_atRecipient_taggedStep node E i J before after S
      (S.occurrence.symm q.val)
      (PrincipalState.phase_recipient_index_ne node E i J before after S q.val q.property)
      (liveTags_nodup_of_support _ hs),hf⟩ (principals q)
    simpa only [Equiv.apply_symm_apply] using hh
  rw [he]
  calc
    _ ≤ |∑ u, (scores u).phaseIntegral P| + |∑ q, (principals q).phaseIntegral P| := abs_add_le _ _
    _ ≤ (∑ u, |(scores u).phaseIntegral P|) + ∑ q, |(principals q).phaseIntegral P| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ u : Fin (scoreRoutes (List.finRange J.length)).length,
        cost (.score node (((scoreRoutes (List.finRange J.length)).get u).1.map J.get)
          (((scoreRoutes (List.finRange J.length)).get u).2.map J.get))) +
        ∑ q : {q : Fin (S.n+1) // q ≠ p}, cost (.ibp node (S.pending q.val).tag) :=
      add_le_add (Finset.sum_le_sum (fun u _ => hscore u))
        (Finset.sum_le_sum (fun q _ => hprincipal q))
    _ = _ := by
      rw [← score_cost_positions]
      have hp := SyntaxState.sum_other_occurrences before after (.formula node (.adjoint i E) J) S
        (fun q => cost (.ibp node q.tag))
      simpa only [p,ScoreState.parentVertex,List.map_append,List.sum_append] using congrArg
        (fun z => ((scoreRoutes J).map (fun route => cost (.score node route.1 route.2))).sum + z) hp

end AcceleratedLogConcave.Tensor.Ordered.Graph
