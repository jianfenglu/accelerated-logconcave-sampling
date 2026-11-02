import AcceleratedLogConcave.Tensor.MaterialExpressionStep

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff RealInnerProductSpace BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.CoupledVelocityPolynomial CoordinateReduction Kinetic AdjointReduction

private theorem finset_list_sum {K U : Type*} [Fintype K] (l : List U) (f : K → U → ℝ) :
    (∑ k, (l.map (f k)).sum) = (l.map (fun u => ∑ k, f k u)).sum := by
  induction l with
  | nil => simp
  | cons u l ih => simp [ih,Finset.sum_add_distrib]

theorem materialDerivative_row_coordinate {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature (r+2)) (he : IsMaterialExpression e)
    (i : Fin (r+2)) (a : Fin (r+1) → Fin D)
    {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D)) (k : Fin D) :
    inner ℝ (coordinateDirection D k)
      (materialDerivative d.materialVelocity (materialExpressionRow d e i a) (t,y)) =
      materialDerivative d.materialVelocity
        (materialExpressionValue d e (Fin.insertNth i k a)) (t,y) := by
  have hd := ((contDiffOn_materialExpressionRow d e he i a).contDiffAt
    ((isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
  have hc := (innerSL ℝ (coordinateDirection D k)).hasFDerivAt.comp (t,y) hd.hasFDerivAt
  have hfun : (fun p => inner ℝ (coordinateDirection D k) (materialExpressionRow d e i a p)) =
      materialExpressionValue d e (Fin.insertNth i k a) := by
    funext p
    exact materialExpressionRow_coordinate d e i a p k
  change HasFDerivAt (fun p => inner ℝ (coordinateDirection D k) (materialExpressionRow d e i a p)) _ (t,y) at hc
  rw [hfun] at hc
  unfold materialDerivative
  rw [hc.fderiv]
  rfl

/-- The actual leaf identity in the literal monomial-list representation. -/
theorem materialExpressionStep_coefficient_evaluate {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (n : ℕ)
    (a : Fin (n+2) → Fin D) {t : ℝ} (ht : -1<t ∧ t<1)
    (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (materialExpressionValue d (.coefficient (Sum.inl n)) a) (t,y) =
      ((materialExpressionStep (d.ell*d.r^2) (.coefficient (Sum.inl n))).map
        (fun u => u.value d a (t,y))).sum := by
  rw [show materialExpressionValue d (.coefficient (Sum.inl n)) a =
    (fun p => coefficientEnvironment d.F d.x d.ell d.r p.1 (Sum.inl n) p.2 a) from rfl,
    material_coefficient_leaf_expansion d n ht y]
  simp only [materialExpressionStep,List.map_cons,List.sum_cons,List.map_map,
    Function.comp_def,MaterialTerm.value,pow_zero,pow_one,mul_one]
  congr 1
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  change (2*d.ell*d.r^2*t) * ((materialRouteFactorialWeight u.val / ((n+1).factorial:ℝ)) * _) = _
  dsimp [materialExpressionValue]
  ring

private theorem list_sum_get {U : Type*} (l : List U) (f : U → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  rw [← List.sum_ofFn]
  congr 1
  rw [List.ofFn_comp',List.ofFn_get]

/-- Finite-linearity of the principal adjoint branch, consuming the actual
child derivative representation. The final structural induction supplies hrep. -/
theorem material_adjoint_principal_of_rep {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature (r+2)) (he : IsMaterialExpression e)
    (i : Fin (r+2)) (a : Fin (r+1) → Fin D)
    (ts : List (MaterialTerm (r+2)))
    (hterms : ∀ u ∈ ts, IsMaterialExpression u.expression)
    {t : ℝ} (ht : -1<t ∧ t<1)
    (hrep : ∀ z b, materialDerivative d.materialVelocity (materialExpressionValue d e b) (t,z) =
      (ts.map (fun u => u.value d b (t,z))).sum)
    (y : EuclideanSpace ℝ (Fin D)) :
    d.spacetimeAdjoint (materialDerivative d.materialVelocity (materialExpressionRow d e i a)) (t,y) =
      (ts.map (fun u => u.coefficient*t^u.degree*
        materialExpressionValue d (.adjoint i u.expression) a (t,y))).sum := by
  let row := materialExpressionRow d e i a
  let W (j : Fin ts.length) := materialExpressionRow d (ts.get j).expression i a
  let c (j : Fin ts.length) := (ts.get j).coefficient*t^(ts.get j).degree
  have hW (j : Fin ts.length) := contDiffOn_materialExpressionRow d (ts.get j).expression
    (hterms _ (List.get_mem _ _)) i a
  have hr := contDiffOn_materialExpressionRow d e he i a
  have hD := (hr.fderiv_of_isOpen (isOpen_openDomain _) (m := ∞) (by simp)).clm_apply
    d.contDiffOn_materialVelocity
  have hd := (hD.contDiffAt ((isOpen_openDomain _).mem_nhds
    (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
  change DifferentiableAt ℝ (materialDerivative d.materialVelocity row) (t,y) at hd
  have hfield : (fun z => materialDerivative d.materialVelocity row (t,z)) =
      fun z => ∑ j : Fin ts.length, c j • W j (t,z) := by
    funext z
    ext k
    have hi (v : EuclideanSpace ℝ (Fin D)) : inner ℝ (coordinateDirection D k) v = v k := by
      simpa [coordinateDirection,EuclideanSpace.single] using
        EuclideanSpace.inner_single_left k (1:ℝ) v
    rw [←hi,←hi,inner_sum]
    simp_rw [inner_smul_right]
    change inner ℝ (coordinateDirection D k)
      (materialDerivative d.materialVelocity (materialExpressionRow d e i a) (t,z)) = _
    rw [materialDerivative_row_coordinate d e he i a ht z k,hrep,list_sum_get]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [c,W,MaterialTerm.value]
    rw [materialExpressionRow_coordinate]
  rw [d.spacetimeAdjoint_eq_weightedAdjoint hd,hfield]
  have hslice (j : Fin ts.length) : DifferentiableAt ℝ (fun z => W j (t,z)) y := by
    have hh := ((hW j).contDiffAt ((isOpen_openDomain _).mem_nhds
      (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
    exact hh.comp y (((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) y)).differentiableAt)
  rw [Conditional.weightedAdjoint_finsetSum Finset.univ _
    (fun j z => c j • W j (t,z)) (fun j _ => (hslice j).const_smul (c j)),list_sum_get]
  apply Finset.sum_congr rfl
  intro j _
  rw [Conditional.weightedAdjoint_smul (differentiableAt_const _) (hslice j)]
  simp only [fderiv_fun_const,Pi.zero_apply,zero_apply,sub_zero]
  have hj := ((hW j).contDiffAt ((isOpen_openDomain _).mem_nhds
    (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
  rw [← d.spacetimeAdjoint_eq_weightedAdjoint hj,
    ← materialExpressionValue_adjoint d (ts.get j).expression
      (hterms _ (List.get_mem _ _)) i a ht y]

private theorem finset_list_product_left {K U : Type*} [Fintype K]
    (l : List U) (c : U → ℝ) (f : U → K → ℝ) (g : K → ℝ) :
    (∑ k, (l.map (fun u => c u*f u k)).sum * g k) =
      (l.map (fun u => c u * ∑ k, f u k*g k)).sum := by
  simp_rw [← List.sum_map_mul_right]
  rw [finset_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem finset_list_product_right {K U : Type*} [Fintype K]
    (l : List U) (c : U → ℝ) (f : K → ℝ) (g : U → K → ℝ) :
    (∑ k, f k * (l.map (fun u => c u*g u k)).sum) =
      (l.map (fun u => c u * ∑ k, f k*g u k)).sum := by
  simp_rw [← List.sum_map_mul_left]
  rw [finset_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Every actual material-generated expression differentiates to the exact
finite monomial list. No final analytic or representation premise is added. -/
theorem materialExpressionStep_evaluate {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature r) (he : IsMaterialExpression e) :
    ∀ {t : ℝ}, -1<t ∧ t<1 → ∀ y a,
    materialDerivative d.materialVelocity (materialExpressionValue d e a) (t,y) =
      ((materialExpressionStep (d.ell*d.r^2) e).map (fun u => u.value d a (t,y))).sum := by
  induction e with
  | coefficient c =>
    cases c with
    | inl n => exact fun ht y a => materialExpressionStep_coefficient_evaluate d n a ht y
    | inr x => exact False.elim he
  | permute π e ih =>
    intro t ht y a
    simpa only [materialExpressionStep,List.map_map,Function.comp_def,
      MaterialTerm.mapExpr,MaterialTerm.value,material_expression_permute,
      materialExpressionValue,Expr.evaluate]
      using ih he ht y (a ∘ π)
  | contract e f i j ihe ihf =>
    intro t ht y a
    rw [material_expression_contract d e f i j a (t,y)
      (fun b => differentiableAt_materialExpressionValue d e he.1 b ht y)
      (fun b => differentiableAt_materialExpressionValue d f he.2 b ht y)]
    simp_rw [ihe he.1 ht y,ihf he.2 ht y]
    rw [Finset.sum_add_distrib]
    simp only [materialExpressionStep,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    congr 1
    · exact finset_list_product_left (materialExpressionStep (d.ell*d.r^2) e) (fun u => u.coefficient*t^u.degree)
        (fun u k => materialExpressionValue d u.expression (leftAssignment i a k) (t,y))
        (fun k => materialExpressionValue d f (rightAssignment j a k) (t,y))
    · exact finset_list_product_right (materialExpressionStep (d.ell*d.r^2) f) (fun u => u.coefficient*t^u.degree)
        (fun k => materialExpressionValue d e (leftAssignment i a k) (t,y))
        (fun u k => materialExpressionValue d u.expression (rightAssignment j a k) (t,y))
  | derivative e ih => exact False.elim he
  | adjoint i e ih =>
    intro t ht y a
    rw [material_expression_adjoint_correction d e he i a ht y,
      material_adjoint_principal_of_rep d e he i a _
        (materialExpressionStep_isMaterial _ e he) ht (fun z b => ih he ht z b) y]
    simp only [materialExpressionStep,List.map_append,List.sum_append,List.map_map,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      Function.comp_def,MaterialTerm.mapExpr,MaterialTerm.value,pow_one]

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
