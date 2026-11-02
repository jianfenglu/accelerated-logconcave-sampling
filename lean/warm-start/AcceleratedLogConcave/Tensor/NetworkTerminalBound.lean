import AcceleratedLogConcave.Tensor.NetworkTerminalVertex

noncomputable section
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords ActualCoefficientIntegrability Conditional

/-- Ordered graph vertices count exactly the retained forest occurrences. -/
theorem SyntaxState.prod_pending {s : List (TaggedPending signature)} (S : SyntaxState s)
    (f : TaggedPending signature → ℝ) :
    (∏ v, f (S.pending v)) = (s.map f).prod := by
  rw [← S.occurrence.prod_comp (fun v => f (S.pending v))]
  simp_rw [S.occurrence_spec]
  rw [← List.prod_ofFn]
  change (List.ofFn (f ∘ s.get)).prod = _
  rw [← List.map_ofFn,List.ofFn_get]

/-- Terminal actual network bound with precisely one physical dimension factor. -/
theorem SyntaxState.terminal_abs_bound {D : ℕ} {s : List (TaggedPending signature)}
    (S : SyntaxState s) (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (hsmall : d.r^2*d.ell ≤ 1/2) {L V : Type*} (values : OriginValues L V)
    (hterminal : ∀ q ∈ eraseForest values s, q.Terminal)
    {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D)) :
    |S.value (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) y| ≤
      (D:ℝ) * budgetProduct (Real.sqrt (conditionalVariance t)) (eraseForest values s) := by
  let := S.edgeFintype
  have hq (v : Fin (S.n+1)) : ((S.pending v).erase values).Terminal := by
    apply hterminal
    apply List.mem_map.mpr
    refine ⟨S.pending v,?_,rfl⟩
    obtain ⟨i,rfl⟩ := S.occurrence.surjective v
    rw [S.occurrence_spec]
    exact List.get_mem _ _
  have h := S.graph.orderedContraction_bound D S.admissible
    (S.tensors (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) y)
    (fun v => (2:ℝ)^((S.pending v).erase values).sizeBudget *
      (((S.pending v).erase values).sizeBudget.factorial : ℝ) *
      (Real.sqrt (conditionalVariance t)) ^ (-(((S.pending v).erase values).smoothingBudget : ℝ)))
    (fun v A hA => pendingTensor_terminal_bound S.graph v d hsmall values (S.pending v)
      (hq v) (S.ports v) ht y A hA)
  rw [S.prod_pending (fun q => (2:ℝ)^(q.erase values).sizeBudget *
    ((q.erase values).sizeBudget.factorial : ℝ) *
    (Real.sqrt (conditionalVariance t)) ^ (-((q.erase values).smoothingBudget : ℝ)))] at h
  simpa [SyntaxState.value,budgetProduct,eraseForest,List.map_map,Function.comp_def] using h

end AcceleratedLogConcave.Tensor.Ordered.Graph
