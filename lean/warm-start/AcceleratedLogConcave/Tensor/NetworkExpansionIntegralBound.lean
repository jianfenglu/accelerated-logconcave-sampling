import AcceleratedLogConcave.Tensor.NetworkSelectedIntegralBound
import AcceleratedLogConcave.Tensor.NetworkTerminalIntegral

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords ActualCoefficientIntegrability Conditional
open Analysis.PositiveVarianceSlab
variable {D : ℕ}

/-- Direct absolute-integral induction on the existing, literal expansion tree.
No new reduction tree, route count, or terminal-state certificate is assumed. -/
theorem expansion_integral_abs_bound
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (hsmall : d.r^2*d.ell ≤ 1/2)
    {L V : Type*} (values : OriginValues L V)
    {t : ℝ} (ht : t ∈ Set.Icc (left d.b) (right d.b))
    {s : List (TaggedPending signature)} (tree : ExpansionTree s) :
    ∀ (S : SyntaxState s), (forestSupport s).Nodup → (originInventory s).Nodup → IsMaterialForest s →
    |S.actualIntegral d t| ≤ (D:ℝ) *
      (tree.branches.map (fun run => budgetProduct (Real.sqrt (conditionalVariance t))
        (eraseForest values run.2))).sum := by
  let R := Real.sqrt (conditionalVariance t)
  let budget := fun s : List (TaggedPending signature) => budgetProduct R (eraseForest values s)
  have ht' := construction_subset d.hb0 d.hb1 ht
  induction tree with
  | leaf terminal =>
    intro S _ _ _
    simpa only [SyntaxState.actualIntegral,ExpansionTree.branches,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      using S.terminal_integral_abs_bound d hsmall values terminal ⟨ht'.1,ht'.2⟩
  | @node s active edges legal complete unique child ih =>
    intro S hs hinv hm
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
    have hcost_mem (edge : Event × List (TaggedPending signature)) (he : edge ∈ edges) :
        cost edge.1 = childCost ⟨edge,he⟩ := by
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp he
      subst edge
      exact hcost j
    have hlocal := S.integral_le_local_event_costs d ht hs hinv hm active cost
      (fun event target step C => by
        have he := complete event target step
        rw [hcost_mem (event,target) he]
        exact ih (event,target) he C (step.legal.support_nodup hs)
          (step.legal.inventory_nodup hinv) (taggedStep_isMaterial step.legal hm))
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
    simp only [ExpansionTree.branches,List.map_flatMap,JetCalculus.list_sum_flatMap,
      List.map_map,Function.comp_def]
    exact (List.sum_map_mul_left edges.attach (fun edge =>
      ((child edge.val edge.property).branches.map (fun run => budget run.2)).sum) (D:ℝ)).symm

end AcceleratedLogConcave.Tensor.Ordered.Graph
