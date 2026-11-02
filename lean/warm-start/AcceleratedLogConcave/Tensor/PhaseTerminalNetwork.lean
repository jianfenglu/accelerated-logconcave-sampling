import AcceleratedLogConcave.Tensor.NetworkTerminalBound

/-! Dimension-sharp terminal contraction for an arbitrary phase environment.
The hypotheses are rectangular split bounds of the actual terminal primitive
jets. No expression moment or reduction integral equality is postulated. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

theorem SyntaxState.phase_prod_pending {s : List (TaggedPending σ)} (S : SyntaxState s)
    (f : TaggedPending σ → ℝ) :
    (∏ v, f (S.pending v)) = (s.map f).prod := by
  rw [← S.occurrence.prod_comp (fun v => f (S.pending v))]
  simp_rw [S.occurrence_spec]
  rw [← List.prod_ofFn]
  change (List.ofFn (f ∘ s.get)).prod = _
  rw [← List.map_ofFn,List.ofFn_get]

/-- The coefficient-jet budget with a free universal factorial constant. -/
def phaseBudgetProduct {L V : Type*} (c R : ℝ) (s : List (Pending σ L V)) : ℝ :=
  (s.map (fun p => c^p.sizeBudget * (p.sizeBudget.factorial : ℝ) *
    R^(-(p.smoothingBudget : ℝ)))).prod

/-- An admissible terminal network pays a single ambient dimension, irrespective
of intermediate tensor ranks. The selected split is always nonempty and proper. -/
theorem SyntaxState.phase_terminal_abs_bound
    {s : List (TaggedPending σ)} (S : SyntaxState s)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    {L V : Type*} (values : OriginValues L V) (c R : ℝ)
    (_hleaf : ∀ p ∈ s, p.activeNode = none)
    (hprimitive : let _ := S.edgeFintype; ∀ (v : Fin (S.n+1)) (A : Finset (S.graph.Slot v)),
      NontrivialSplit A → ∀ y,
      splitNorm D A (S.graph.pendingTensor v ρ H (S.pending v) (S.ports v) y) ≤
        c^((S.pending v).erase values).sizeBudget *
          (((S.pending v).erase values).sizeBudget.factorial : ℝ) *
          R^(-(((S.pending v).erase values).smoothingBudget : ℝ)))
    (y : EuclideanSpace ℝ (Fin D)) :
    |S.value ρ H y| ≤ (D : ℝ) * phaseBudgetProduct c R (eraseForest values s) := by
  let := S.edgeFintype
  have h := S.graph.orderedContraction_bound D S.admissible (S.tensors ρ H y)
    (fun v => c^((S.pending v).erase values).sizeBudget *
      (((S.pending v).erase values).sizeBudget.factorial : ℝ) *
      R^(-(((S.pending v).erase values).smoothingBudget : ℝ)))
    (fun v A hA => hprimitive v A hA y)
  rw [S.phase_prod_pending (fun p => c^(p.erase values).sizeBudget *
    ((p.erase values).sizeBudget.factorial : ℝ) *
    R^(-((p.erase values).smoothingBudget : ℝ)))] at h
  simpa [SyntaxState.value,phaseBudgetProduct,eraseForest,List.map_map,Function.comp_def]
    using h

/-- Probability integration introduces no additional dimension or tail factor.
The graph already supplies the only dimension cost. -/
theorem SyntaxState.phase_terminal_integral_abs_bound
    {s : List (TaggedPending σ)} (S : SyntaxState s)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin D))) [IsProbabilityMeasure μ]
    {L V : Type*} (values : OriginValues L V) (c R : ℝ)
    (hleaf : ∀ p ∈ s, p.activeNode = none)
    (hprimitive : let _ := S.edgeFintype; ∀ (v : Fin (S.n+1)) (A : Finset (S.graph.Slot v)),
      NontrivialSplit A → ∀ y,
      splitNorm D A (S.graph.pendingTensor v ρ H (S.pending v) (S.ports v) y) ≤
        c^((S.pending v).erase values).sizeBudget *
          (((S.pending v).erase values).sizeBudget.factorial : ℝ) *
          R^(-(((S.pending v).erase values).smoothingBudget : ℝ))) :
    |∫ y, S.value ρ H y ∂μ| ≤ (D : ℝ) * phaseBudgetProduct c R (eraseForest values s) := by
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one]
    using norm_integral_le_of_norm_le_const (μ := μ) (f := S.value ρ H)
      (Filter.Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using
          S.phase_terminal_abs_bound ρ H values c R hleaf hprimitive y))
end AcceleratedLogConcave.Tensor.Ordered.Graph
