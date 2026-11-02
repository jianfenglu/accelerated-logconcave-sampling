import AcceleratedLogConcave.Tensor.NetworkVectorAdjointState
import AcceleratedLogConcave.Tensor.NetworkExpressionRms

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords ActualCoefficientIntegrability Conditional
open Analysis.PositiveVarianceSlab

private theorem budget_nonneg {L V : Type*} (values : OriginValues L V) (R : ℝ)
    (hR : 0 ≤ R) (s : List (TaggedPending signature)) :
    0 ≤ budgetProduct R (eraseForest values s) := by
  unfold budgetProduct
  apply List.prod_nonneg
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  positivity

/-- Only the initial non-admissible vector square is outside SyntaxState. Its
first canonical child is already admissible and bounded by the original tree's
literal branch sum, without constructing or counting a new expansion. -/
private theorem first_child_integral_bound {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (hsmall : d.r^2*d.ell ≤ 1/2)
    {L V : Type*} (values : OriginValues L V) {t : ℝ}
    (ht : t ∈ Set.Icc (left d.b) (right d.b))
    {s target : List (TaggedPending signature)} {event : Event}
    (tree : ExpansionTree s) (step : CanonicalStep event target s)
    (S : SyntaxState target) (hs : (forestSupport s).Nodup)
    (hi : (originInventory s).Nodup) (hm : IsMaterialForest s) :
    |S.actualIntegral d t| ≤ (D:ℝ) *
      (tree.branches.map (fun run => budgetProduct (Real.sqrt (conditionalVariance t))
        (eraseForest values run.2))).sum := by
  let budget := fun s : List (TaggedPending signature) => budgetProduct (Real.sqrt (conditionalVariance t)) (eraseForest values s)
  have hb : ∀ s, 0 ≤ budget s := fun s => budget_nonneg values _ (Real.sqrt_nonneg _) s
  cases tree with
  | leaf terminal =>
    have hnone := (firstNonterminal_eq_none s).mpr terminal
    rw [step.scheduled] at hnone
    contradiction
  | node active edges legal complete unique child =>
    have he := complete event target step
    have hchild := expansion_integral_abs_bound d hsmall values ht (child (event,target) he) S
      (step.legal.support_nodup hs) (step.legal.inventory_nodup hi)
      (taggedStep_isMaterial step.legal hm)
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
    simp only [ExpansionTree.branches,List.map_flatMap,JetCalculus.list_sum_flatMap,
      List.map_map,Function.comp_def]
    rfl

/-- Rank-one outer-adjoint RMS has the same single-dimension whole-expression
budget as the matrix supplier. All original branches and endpoints are retained. -/
theorem adjoint_integral_norm_sq_le {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (hsmall : d.r^2*d.ell ≤ 1/2)
    (E : Expr signature 2) (i : Fin 2) (he : IsMaterialExpression E)
    {t : ℝ} (ht : t ∈ Set.Icc (left d.b) (right d.b)) :
    (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) (.adjoint i E) y‖^2
      ∂interpolationLaw d.F d.x d.r t) ≤
      materialRmsNumeric D (Expr.adjoint i E).size *
        (Real.sqrt (conditionalVariance t))^(-2*((Expr.adjoint i E).weight:ℝ)) := by
  let e : Expr signature 1 := .adjoint i E
  let values : OriginValues Unit Unit := ⟨fun _ => (),fun _ => ()⟩
  let s := initialTwoFormulas e e 0 0
  have hs := initialTwoFormulas_support_nodup e e 0 0
  have hi := initialTwoFormulas_inventory_nodup e e 0 0
  let tree := ExpansionTree.build s hs hi
  have step : CanonicalStep (.ibp ⟨0,[]⟩ (.formula ⟨1,[]⟩))
      (vectorAdjointChildForest E i) s := ⟨vectorAdjointChildState_step E i,rfl⟩
  have h := first_child_integral_bound d hsmall values ht tree step
    (vectorAdjointChildState E i) hs hi (initialTwoFormulas_isMaterial e e he he 0 0)
  have ht' := construction_subset d.hb0 d.hb1 ht
  have hv : 0 < conditionalVariance t := conditionalVariance_pos ht'.1 ht'.2
  have hR1 : Real.sqrt (conditionalVariance t) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    simp only [conditionalVariance]
    nlinarith [sq_nonneg t]
  have hb := terminalBranches_budgetProduct_sum_le e 0 values
    (Real.sqrt (conditionalVariance t)) (Real.sqrt_pos.mpr hv) hR1
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg D : (0:ℝ) ≤ D)
  have hcombined := h.trans hm
  rw [integral_vectorAdjoint_eq_child d E i ht]
  apply (le_abs_self _).trans
  convert hcombined using 1
  all_goals simp only [SyntaxState.actualIntegral,materialRmsNumeric,Nat.cast_zero,add_zero,neg_mul]
  all_goals ring


private theorem rank_one_integral_norm_sq_le {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (hsmall : d.r^2*d.ell ≤ 1/2)
    {t : ℝ} (ht : t ∈ Set.Icc (left d.b) (right d.b)) {r : ℕ} (e : Expr signature r) :
    IsMaterialExpression e → r = 1 →
    (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) e y‖^2 ∂interpolationLaw d.F d.x d.r t) ≤
      materialRmsNumeric D e.size * (Real.sqrt (conditionalVariance t))^(-2*(e.weight:ℝ)) := by
  induction e with
  | coefficient c =>
    intro _ hr
    have h := signature.two_le_arity c
    omega
  | @permute r p E ih =>
    intro he hr
    subst r
    have hp : p = Equiv.refl (Fin 1) := by
      apply Equiv.ext
      intro i
      exact Subsingleton.elim _ _
    subst p
    have hv (y : EuclideanSpace ℝ (Fin D)) :
        Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
          (interpolationPotential d.F d.x d.r t) (.permute (Equiv.refl _) E) y =
        Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
          (interpolationPotential d.F d.x d.r t) E y := by
      ext a
      rfl
    simpa only [hv,Expr.size,Expr.weight] using ih he rfl
  | contract E F i j ihE ihF =>
    intro _ hr
    omega
  | derivative E ih =>
    intro he
    exact False.elim he
  | @adjoint r i E ih =>
    intro he hr
    have hz : r = 0 := by omega
    subst r
    exact adjoint_integral_norm_sq_le d hsmall E i he ht

/-- Complete original-data RMS supplier for the concrete rank-one material
receiver. Rank one excludes coefficient, contract and derivative roots; its only
remaining unary permutations are trivial on Fin 1. -/
theorem expression_vector_integral_norm_sq_le {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (hsmall : d.r^2*d.ell ≤ 1/2)
    (e : Expr signature 1) (he : IsMaterialExpression e)
    {t : ℝ} (ht : t ∈ Set.Icc (left d.b) (right d.b)) :
    (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) e y‖^2 ∂interpolationLaw d.F d.x d.r t) ≤
      materialRmsNumeric D e.size * (Real.sqrt (conditionalVariance t))^(-2*(e.weight:ℝ)) :=
  rank_one_integral_norm_sq_le d hsmall ht e he rfl

end AcceleratedLogConcave.Tensor.Ordered.Graph
