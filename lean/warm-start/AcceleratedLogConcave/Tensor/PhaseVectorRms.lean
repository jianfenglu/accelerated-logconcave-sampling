import AcceleratedLogConcave.Tensor.PhaseVectorSquare
import AcceleratedLogConcave.Tensor.PhaseExpansionIntegralBound

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

/-- Literal branch-count and primitive-budget factor, including one dimension. -/
def phaseRmsNumeric (D : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  (D : ℝ) * ((2*n : ℕ) : ℝ)^(2*n) * c^(2*n) * ((2*n).factorial : ℝ)

private theorem budget_nonneg {L V : Type*} (values : OriginValues L V) (c R : ℝ) (hc : 0 ≤ c)
    (hR : 0 ≤ R) (s : List (TaggedPending σ)) :
    0 ≤ PhaseBudget.budgetProduct c R (eraseForest values s) := by
  unfold PhaseBudget.budgetProduct
  apply List.prod_nonneg
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  positivity

/-- Only the initial non-admissible vector square is outside SyntaxState. Its
first canonical child is already admissible and bounded by the original tree's
literal branch sum, without constructing or counting a new expansion. -/
private theorem first_child_integral_bound {D : ℕ}
    (P : PhaseAnalyticEnvironment σ D) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (_hR1 : R ≤ 1)
    (hprim : PhasePrimitiveBudgets P.coefficients P.potential c R)
    [IsProbabilityMeasure P.toSmoothGibbsEnvironment.law]
    {L V : Type*} (values : OriginValues L V)
    {s target : List (TaggedPending σ)} {event : Event}
    (tree : ExpansionTree s) (step : CanonicalStep event target s)
    (S : SyntaxState target) (hs : (forestSupport s).Nodup)
    (hi : (originInventory s).Nodup) :
    |S.phaseIntegral P| ≤ (D:ℝ) *
      (tree.branches.map (fun run => PhaseBudget.budgetProduct c R
        (eraseForest values run.2))).sum := by
  let budget := fun s : List (TaggedPending σ) => PhaseBudget.budgetProduct c R (eraseForest values s)
  have hb : ∀ s, 0 ≤ budget s := fun s => budget_nonneg values c R (by linarith) hR.le s
  cases tree with
  | leaf terminal =>
    have hnone := (firstNonterminal_eq_none s).mpr terminal
    rw [step.scheduled] at hnone
    contradiction
  | node active edges legal complete unique child =>
    have he := complete event target step
    have hchild := phase_expansion_integral_abs_bound P hprim values (child (event,target) he) S
      (step.legal.support_nodup hs) (step.legal.inventory_nodup hi)
    let cost := fun edge : {edge // edge ∈ edges} =>
      ((child edge.val edge.property).branches.map (fun run => budget run.2)).sum
    have hn : ∀ edge, 0 ≤ cost edge := by
      intro edge
      apply List.sum_nonneg
      intro x hx
      obtain ⟨run,_,rfl⟩ := List.mem_map.mp hx
      exact hb _
    have hc : cost ⟨(event,target),he⟩ ≤ (edges.attach.map cost).sum := by
      apply List.single_le_sum
      · intro x hx
        obtain ⟨edge,_,rfl⟩ := List.mem_map.mp hx
        exact hn edge
      · exact List.mem_map.mpr ⟨⟨(event,target),he⟩,by simp,rfl⟩
    have h := hchild.trans (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg D))
    convert h using 1
    simp only [ExpansionTree.branches,List.map_flatMap,phase_list_sum_flatMap,
      List.map_map,Function.comp_def]
    rfl

/-- Rank-one outer-adjoint RMS has the same single-dimension whole-expression
budget as the matrix supplier. All original branches and endpoints are retained. -/
theorem phase_adjoint_integral_norm_sq_le {D : ℕ}
    (P : PhaseAnalyticEnvironment σ D) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hprim : PhasePrimitiveBudgets P.coefficients P.potential c R)
    [IsProbabilityMeasure P.toSmoothGibbsEnvironment.law]
    (E : Expr σ 2) (i : Fin 2)
    :
    (∫ y, ‖Expr.evaluate P.coefficients
      P.potential (.adjoint i E) y‖^2
      ∂P.toSmoothGibbsEnvironment.law) ≤
      phaseRmsNumeric D c (Expr.adjoint i E).size *
        R^(-2*((Expr.adjoint i E).weight:ℝ)) := by
  let e : Expr σ 1 := .adjoint i E
  let values : OriginValues Unit Unit := ⟨fun _ => (),fun _ => ()⟩
  let s := initialTwoFormulas e e 0 0
  have hs := initialTwoFormulas_support_nodup e e 0 0
  have hi := initialTwoFormulas_inventory_nodup e e 0 0
  let tree := ExpansionTree.build s hs hi
  have step : CanonicalStep (.ibp ⟨0,[]⟩ (.formula ⟨1,[]⟩))
      (vectorAdjointChildForest E i) s := ⟨vectorAdjointChildState_step E i,rfl⟩
  have h := first_child_integral_bound P hc hR hR1 hprim values tree step
    (vectorAdjointChildState E i) hs hi
  have hb := PhaseBudget.ReductionRecords.terminalBranches_budgetProduct_sum_le e 0 values
    c R hc hR hR1
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg D : (0:ℝ) ≤ D)
  have hcombined := h.trans hm
  rw [phase_integral_vectorAdjoint_eq_child P E i]
  apply (le_abs_self _).trans
  convert hcombined using 1
  all_goals simp only [SyntaxState.phaseIntegral,phaseRmsNumeric,Nat.cast_zero,add_zero,neg_mul]
  all_goals ring


private theorem rank_one_integral_norm_sq_le {D : ℕ}
    (P : PhaseAnalyticEnvironment σ D) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hprim : PhasePrimitiveBudgets P.coefficients P.potential c R)
    [IsProbabilityMeasure P.toSmoothGibbsEnvironment.law]
    {r : ℕ} (e : Expr σ r) :
    r = 1 →
    (∫ y, ‖Expr.evaluate P.coefficients
      P.potential e y‖^2 ∂P.toSmoothGibbsEnvironment.law) ≤
      phaseRmsNumeric D c e.size * R^(-2*(e.weight:ℝ)) := by
  induction e with
  | coefficient c =>
    intro hr
    have h := σ.two_le_arity c
    omega
  | @permute r p E ih =>
    intro hr
    subst r
    have hp : p = Equiv.refl (Fin 1) := by
      apply Equiv.ext
      intro i
      exact Subsingleton.elim _ _
    subst p
    have hv (y : EuclideanSpace ℝ (Fin D)) :
        Expr.evaluate P.coefficients
          P.potential (.permute (Equiv.refl _) E) y =
        Expr.evaluate P.coefficients
          P.potential E y := by
      ext a
      rfl
    simpa only [hv,Expr.size,Expr.weight] using ih rfl
  | contract E F i j ihE ihF =>
    intro hr
    omega
  | derivative E ih =>
    intro hr
    have hp := E.arity_pos
    omega
  | @adjoint r i E ih =>
    intro hr
    have hz : r = 0 := by omega
    subst r
    exact phase_adjoint_integral_norm_sq_le P hc hR hR1 hprim E i

/-- Generic Gibbs RMS supplier for any connected rank-one expression.
Primitive phase budgets and the concrete source identification remain separate. Rank one excludes coefficient, contract and derivative roots; its only
remaining unary permutations are trivial on Fin 1. -/
theorem phase_expression_vector_integral_norm_sq_le {D : ℕ}
    (P : PhaseAnalyticEnvironment σ D) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hprim : PhasePrimitiveBudgets P.coefficients P.potential c R)
    [IsProbabilityMeasure P.toSmoothGibbsEnvironment.law]
    (e : Expr σ 1)
    :
    (∫ y, ‖Expr.evaluate P.coefficients
      P.potential e y‖^2 ∂P.toSmoothGibbsEnvironment.law) ≤
      phaseRmsNumeric D c e.size * R^(-2*(e.weight:ℝ)) :=
  rank_one_integral_norm_sq_le P hc hR hR1 hprim e rfl

/-- Explicit requested universal majorant. The potential and dimension occur
only through actual evaluation/law and the single displayed dimension factor. -/
theorem phase_expression_vector_integral_norm_sq_le_Q {D : ℕ}
    (P : PhaseAnalyticEnvironment σ D) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hprim : PhasePrimitiveBudgets P.coefficients P.potential c R)
    [IsProbabilityMeasure P.toSmoothGibbsEnvironment.law]
    (e : Expr σ 1) :
    (∫ y, ‖Expr.evaluate P.coefficients P.potential e y‖^2
      ∂P.toSmoothGibbsEnvironment.law) ≤
      (D : ℝ) * PhaseBudget.Q c e.size * R^(-2*(e.weight : ℝ)) := by
  apply (phase_expression_vector_integral_norm_sq_le P hc hR hR1 hprim e).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h := mul_le_mul_of_nonneg_left (PhaseBudget.twoCopy_numeric_le_Q hc e.size)
    (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
  simpa only [phaseRmsNumeric, mul_assoc] using h
end AcceleratedLogConcave.Tensor.Ordered.Graph
