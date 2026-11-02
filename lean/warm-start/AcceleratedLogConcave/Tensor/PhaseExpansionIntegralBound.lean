import AcceleratedLogConcave.Tensor.PhaseSelectedIntegralBound
import AcceleratedLogConcave.Tensor.PhasePrimitiveBudgets
import AcceleratedLogConcave.Tensor.PhaseBudgetAggregation

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

/-- Finite literal branch sums, with repetitions preserved. -/
theorem phase_list_sum_flatMap {K : Type*} (l : List K) (f : K → List ℝ) :
    (l.flatMap f).sum = (l.map (fun k => (f k).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]


/-- Direct absolute-integral induction on the existing, literal expansion tree.
No new reduction tree, route count, or terminal-state certificate is assumed. -/
theorem phase_expansion_integral_abs_bound
    (P : PhaseAnalyticEnvironment σ D) {c R : ℝ}
    (hb : PhasePrimitiveBudgets P.coefficients P.potential c R)
    [MeasureTheory.IsProbabilityMeasure P.toSmoothGibbsEnvironment.law]
    {L V : Type*} (values : OriginValues L V)
    {s : List (TaggedPending σ)} (tree : ExpansionTree s) :
    ∀ (S : SyntaxState s), (forestSupport s).Nodup → (originInventory s).Nodup →
    |S.phaseIntegral P| ≤ (D:ℝ) *
      (tree.branches.map (fun run => PhaseBudget.budgetProduct c R
        (eraseForest values run.2))).sum := by
  let budget := fun s : List (TaggedPending σ) => PhaseBudget.budgetProduct c R (eraseForest values s)
  induction tree with
  | leaf terminal =>
    intro S _ _
    simpa only [SyntaxState.phaseIntegral,ExpansionTree.branches,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,phaseBudgetProduct,PhaseBudget.budgetProduct]
      using hb.terminal_integral_bound P S values terminal
  | @node s active edges legal complete unique child ih =>
    intro S hs hinv
    let childCost := fun edge : {edge // edge ∈ edges} =>
      (D:ℝ) * ((child edge.val edge.property).branches.map (fun run => budget run.2)).sum
    let cost := fun event : Event => ∑ j : Fin edges.length,
      if (edges.get j).1 = event then childCost ⟨edges.get j,List.get_mem _ _⟩ else 0
    have hinj : Function.Injective (fun j : Fin edges.length => (edges.get j).1) := by
      intro i j he
      have hh : (edges.map Prod.fst).get ⟨i.val,by simpa only [List.length_map] using i.isLt⟩ =
          (edges.map Prod.fst).get ⟨j.val,by simpa only [List.length_map] using j.isLt⟩ := by simpa using he
      have hv := congrArg Fin.val (unique.injective_get hh)
      exact Fin.ext hv
    have hcost (j : Fin edges.length) :
        cost (edges.get j).1 = childCost ⟨edges.get j,List.get_mem _ _⟩ := by
      dsimp only [cost]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        apply ite_eq_right
        intro he
        exact hk (hinj he)
      · simp
    have hcost_mem (edge : Event × List (TaggedPending σ)) (he : edge ∈ edges) :
        cost edge.1 = childCost ⟨edge,he⟩ := by
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp he
      subst edge
      exact hcost j
    have hlocal := S.phase_integral_le_local_event_costs P hs hinv active cost
      (fun event target step C => by
        have he := complete event target step
        rw [hcost_mem (event,target) he]
        exact ih (event,target) he C (step.legal.support_nodup hs)
          (step.legal.inventory_nodup hinv))
    have hn := liveTags_nodup_of_support s hs
    have hp := (expansion_edges_perm_next edges legal complete unique hn hinv).map Prod.fst
    have hevents : (localEvents s).Perm (edges.map Prod.fst) := by
      simp only [nextBranches,List.map_map] at hp
      change (edges.map Prod.fst).Perm ((localEvents s).map id) at hp
      rw [List.map_id] at hp
      exact hp.symm
    have hsum : ((localEvents s).map cost).sum = (edges.attach.map childCost).sum := by
      calc
        _ = ((edges.map Prod.fst).map cost).sum := (hevents.map cost).sum_eq
        _ = (edges.attach.map (fun edge => cost edge.val.1)).sum := by
          have hh := List.attach_map_val (l := edges) (f := fun edge => cost edge.1)
          simpa only [List.map_map,Function.comp_def] using congrArg List.sum hh.symm
        _ = _ := by
          congr 1
          apply List.map_congr_left
          intro edge _
          exact hcost_mem edge.val edge.property
    rw [hsum] at hlocal
    convert hlocal using 1
    simp only [ExpansionTree.branches,List.map_flatMap,phase_list_sum_flatMap,
      List.map_map,Function.comp_def]
    exact (List.sum_map_mul_left edges.attach (fun edge =>
      ((child edge.val edge.property).branches.map (fun run => budget run.2)).sum) (D:ℝ)).symm

end AcceleratedLogConcave.Tensor.Ordered.Graph
