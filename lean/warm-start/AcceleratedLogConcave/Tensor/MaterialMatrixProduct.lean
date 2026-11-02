import AcceleratedLogConcave.Tensor.MaterialTrajectory

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis

/-- Literal matrix composition, output slot first and input slot second. -/
def materialMatrixProduct (e f : Expr signature 2) : Expr signature 2 :=
  .contract e f (1:Fin 2) (0:Fin 2)

theorem materialMatrixProduct_evaluate {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e f : Expr signature 2) (a : Fin 2 → Fin D) (p : ℝ × EuclideanSpace ℝ (Fin D)) :
    materialExpressionValue d (materialMatrixProduct e f) a p =
      ∑ i : Fin D, materialExpressionValue d e ![a 0,i] p *
        materialExpressionValue d f ![i,a 1] p := by
  change (∑ i : Fin D, _ * _) = _
  apply Finset.sum_congr rfl
  intro i _
  congr 1 <;> apply congrArg (fun b => materialExpressionValue d _ b p) <;>
    funext j <;> fin_cases j <;> rfl

theorem operator_coordinate_mul {D : ℕ}
    (A B : EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D))
    (a : Fin 2 → Fin D) :
    inner ℝ (coordinateDirection D (a 0)) ((A*B) (coordinateDirection D (a 1))) =
      ∑ i : Fin D, inner ℝ (coordinateDirection D (a 0)) (A (coordinateDirection D i)) *
        inner ℝ (coordinateDirection D i) (B (coordinateDirection D (a 1))) := by
  let b := EuclideanSpace.basisFun (Fin D) ℝ
  have hb (i : Fin D) : b i = coordinateDirection D i := by
    simp [b,EuclideanSpace.basisFun_apply,coordinateDirection,EuclideanSpace.single]
  change inner ℝ _ (A (B _)) = _
  nth_rw 1 [← b.sum_repr' (B (coordinateDirection D (a 1)))]
  rw [map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul,inner_smul_right,hb]
  ring

def materialTermProduct (u v : MaterialTerm 2) : MaterialTerm 2 :=
  ⟨u.coefficient*v.coefficient,u.degree+v.degree,materialMatrixProduct u.expression v.expression⟩

def materialTermsProduct (us vs : List (MaterialTerm 2)) : List (MaterialTerm 2) :=
  us.flatMap (fun u => vs.map (materialTermProduct u))

theorem materialTermProduct_value {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (u v : MaterialTerm 2) (a : Fin 2 → Fin D) (p : ℝ × EuclideanSpace ℝ (Fin D)) :
    (materialTermProduct u v).value d a p =
      ∑ i : Fin D, u.value d ![a 0,i] p * v.value d ![i,a 1] p := by
  unfold MaterialTerm.value materialTermProduct
  rw [materialMatrixProduct_evaluate,pow_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem materialTermsProduct_value {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (us vs : List (MaterialTerm 2)) (a : Fin 2 → Fin D) (p : ℝ × EuclideanSpace ℝ (Fin D)) :
    materialTermsValue d (materialTermsProduct us vs) a p =
      ∑ i : Fin D, materialTermsValue d us ![a 0,i] p *
        materialTermsValue d vs ![i,a 1] p := by
  have hmap (u : MaterialTerm 2) :
      materialTermsValue d (vs.map (materialTermProduct u)) a p =
        ∑ i : Fin D, u.value d ![a 0,i] p * materialTermsValue d vs ![i,a 1] p := by
    induction vs with
    | nil => simp [materialTermsValue]
    | cons v vs ih =>
      simp only [List.map_cons,materialTermsValue,List.sum_cons] at ih ⊢
      rw [materialTermProduct_value,ih]
      simp only [mul_add,Finset.sum_add_distrib]
  induction us with
  | nil => simp [materialTermsProduct,materialTermsValue]
  | cons u us ih =>
    change materialTermsValue d ((vs.map (materialTermProduct u)) ++ materialTermsProduct us vs) a p = _
    have happ : materialTermsValue d ((vs.map (materialTermProduct u)) ++ materialTermsProduct us vs) a p =
      materialTermsValue d (vs.map (materialTermProduct u)) a p +
        materialTermsValue d (materialTermsProduct us vs) a p := by
      simp [materialTermsValue]
    rw [happ,hmap,ih]
    simp only [materialTermsValue,List.map_cons,List.sum_cons,add_mul,Finset.sum_add_distrib]

theorem materialTermsProduct_mass (us vs : List (MaterialTerm 2)) :
    materialMass (materialTermsProduct us vs) = materialMass us*materialMass vs := by
  unfold materialTermsProduct
  rw [materialMass_flatMap]
  have h (u : MaterialTerm 2) : materialMass (vs.map (materialTermProduct u)) =
      |u.coefficient| * materialMass vs := by
    simp only [materialMass,List.map_map,Function.comp_def,materialTermProduct,abs_mul]
    exact List.sum_map_mul_left _ _ _
  simp only [h]
  exact List.sum_map_mul_right _ _ _

theorem materialTermsProduct_isMaterial (us vs : List (MaterialTerm 2))
    (hu : ∀ u ∈ us, IsMaterialExpression u.expression)
    (hv : ∀ v ∈ vs, IsMaterialExpression v.expression) :
    ∀ w ∈ materialTermsProduct us vs, IsMaterialExpression w.expression := by
  intro w hw
  obtain ⟨u,hu',hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨v,hv',rfl⟩ := List.mem_map.mp hw
  exact ⟨hu u hu',hv v hv'⟩

theorem materialTermsProduct_size_degree (us vs : List (MaterialTerm 2))
    (s₁ s₂ k₁ k₂ : ℕ)
    (hu : ∀ u ∈ us, u.expression.size ≤ s₁ ∧ u.degree ≤ k₁)
    (hv : ∀ v ∈ vs, v.expression.size ≤ s₂ ∧ v.degree ≤ k₂) :
    ∀ w ∈ materialTermsProduct us vs,
      w.expression.size ≤ s₁+s₂+1 ∧ w.degree ≤ k₁+k₂ := by
  intro w hw
  obtain ⟨u,hu',hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨v,hv',rfl⟩ := List.mem_map.mp hw
  have h₁ := hu u hu'
  have h₂ := hv v hv'
  change u.expression.size+v.expression.size+1 ≤ _ ∧ u.degree+v.degree ≤ _
  omega

theorem materialTermsProduct_weight (us vs : List (MaterialTerm 2))
    (s₁ s₂ : ℝ≥0)
    (hu : ∀ u ∈ us, u.expression.weight ≤ s₁)
    (hv : ∀ v ∈ vs, v.expression.weight ≤ s₂) :
    ∀ w ∈ materialTermsProduct us vs, w.expression.weight ≤ s₁+s₂ := by
  intro w hw
  obtain ⟨u,hu',hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨v,hv',rfl⟩ := List.mem_map.mp hw
  exact add_le_add (hu u hu') (hv v hv')

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
