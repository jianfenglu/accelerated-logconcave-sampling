import AcceleratedLogConcave.Tensor.MaterialStepSemantics

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.CoupledVelocityPolynomial

/-- Differentiate the recorded scalar monomial together with its actual
expression. The scalar time direction is exactly one in the original flow. -/
theorem materialDerivative_term {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (u : MaterialTerm r) (hu : IsMaterialExpression u.expression)
    (a : Fin r → Fin D) {t : ℝ} (ht : -1<t ∧ t<1)
    (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (u.value d a) (t,y) =
      (u.coefficient*(u.degree:ℝ)*t^(u.degree-1)) * materialExpressionValue d u.expression a (t,y) +
      (u.coefficient*t^u.degree) *
        materialDerivative d.materialVelocity (materialExpressionValue d u.expression a) (t,y) := by
  have he := differentiableAt_materialExpressionValue d u.expression hu a ht y
  have hc := ((hasFDerivAt_fst (𝕜 := ℝ) (p := (t,y))).pow u.degree).const_mul u.coefficient
  have hh := hc.mul he.hasFDerivAt
  change HasFDerivAt (u.value d a) _ (t,y) at hh
  unfold materialDerivative
  rw [hh.fderiv]
  simp [PositiveVarianceFlowData.materialVelocity,smul_eq_mul]
  ring

/-- Exact term differentiation: one scalar derivative and the explicit
one-step expression alternatives. Zero scalar coefficients are retained. -/
def materialTermStep (l : ℝ) {r : ℕ} (u : MaterialTerm r) : List (MaterialTerm r) :=
  ⟨u.coefficient*(u.degree:ℝ),u.degree-1,u.expression⟩ ::
    (materialExpressionStep l u.expression).map (fun v =>
      ⟨u.coefficient*v.coefficient,u.degree+v.degree,v.expression⟩)

def materialIterate (l : ℝ) {r : ℕ} (e : Expr signature r) : ℕ → List (MaterialTerm r)
  | 0 => [⟨1,0,e⟩]
  | k+1 => (materialIterate l e k).flatMap (materialTermStep l)

theorem materialTermStep_evaluate {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (u : MaterialTerm r) (hu : IsMaterialExpression u.expression)
    (a : Fin r → Fin D) {t : ℝ} (ht : -1<t ∧ t<1)
    (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (u.value d a) (t,y) =
      ((materialTermStep (d.ell*d.r^2) u).map (fun v => v.value d a (t,y))).sum := by
  rw [materialDerivative_term d u hu a ht y,materialExpressionStep_evaluate d u.expression hu ht y a]
  simp only [materialTermStep,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,MaterialTerm.value,pow_add]
  congr 1
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro v hv
  ring

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
