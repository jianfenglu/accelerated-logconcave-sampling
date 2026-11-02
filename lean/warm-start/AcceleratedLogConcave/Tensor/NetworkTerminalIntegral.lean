import AcceleratedLogConcave.Tensor.NetworkTerminalBound

noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords ActualCoefficientIntegrability Conditional

/-- The canonical expansion-tree leaf supplies terminality, not a new analytic premise. -/
theorem SyntaxState.terminal_integral_abs_bound {D : ℕ} {s : List (TaggedPending signature)}
    (S : SyntaxState s) (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (hsmall : d.r^2*d.ell ≤ 1/2) {L V : Type*} (values : OriginValues L V)
    (hleaf : ∀ q ∈ s, q.activeNode = none)
    {t : ℝ} (ht : -1<t ∧ t<1) :
    |∫ y, S.value (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) y ∂interpolationLaw d.F d.x d.r t| ≤
      (D:ℝ) * budgetProduct (Real.sqrt (conditionalVariance t)) (eraseForest values s) := by
  let := interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r t
  have hterminal : ∀ q ∈ eraseForest values s, q.Terminal := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact p.terminal_erase values (hleaf p hp)
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using
    (norm_integral_le_of_norm_le_const (μ := interpolationLaw d.F d.x d.r t)
      (f := S.value (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t))
      (Filter.Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using S.terminal_abs_bound d hsmall values hterminal ht y)))

end AcceleratedLogConcave.Tensor.Ordered.Graph
