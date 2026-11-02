import AcceleratedLogConcave.Tensor.MaterialWordMass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open WithLp Conditional Analysis Analysis.PositiveVarianceSlab Analysis.OrderedJacobianWords Set

def materialWordsTerms (l : ℝ) (m : ℕ) : List (MaterialTerm 2) :=
  (words m).flatMap (fun w => (materialWordTerms l w).map
    (fun u => ⟨l^w.length*u.coefficient,u.degree,u.expression⟩))

theorem materialWordsTerms_value {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (m : ℕ)
    (a : Fin 2 → Fin D) (p : ℝ × EuclideanSpace ℝ (Fin D)) :
    materialTermsValue d (materialWordsTerms (d.ell*d.r^2) m) a p =
      ((words m).map (fun w => (d.ell*d.r^2)^w.length *
        materialTermsValue d (materialWordTerms (d.ell*d.r^2) w) a p)).sum := by
  unfold materialWordsTerms materialTermsValue
  rw [List.map_flatMap,Conditional.JetCalculus.list_sum_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w _
  simp only [List.map_map,Function.comp_def,MaterialTerm.value]
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u _
  ring

theorem actual_wordSum_coordinate_expansion {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (m : ℕ) (hm : 0<m)
    (a : Fin 2 → Fin D) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b))
    (y : EuclideanSpace ℝ (Fin D)) :
    inner ℝ (coordinateDirection D (a 0))
      (evaluateSum (fun j u => d.jacobianCoefficientJet j u y) (words m) t
        (coordinateDirection D (a 1))) =
      materialTermsValue d (materialWordsTerms (d.ell*d.r^2) m) a (t,(d.state t y).fst) := by
  have hs (ws : List Word) :
      inner ℝ (coordinateDirection D (a 0))
        (evaluateSum (fun j u => d.jacobianCoefficientJet j u y) ws t
          (coordinateDirection D (a 1))) =
        (ws.map (fun w => inner ℝ (coordinateDirection D (a 0))
          (evaluate (fun j u => d.jacobianCoefficientJet j u y) w t
            (coordinateDirection D (a 1))))).sum := by
    induction ws with
    | nil => simp [evaluateSum]
    | cons w ws ih =>
      change inner ℝ (coordinateDirection D (a 0))
        ((evaluate (fun j u => d.jacobianCoefficientJet j u y) w t +
          evaluateSum (fun j u => d.jacobianCoefficientJet j u y) ws t)
          (coordinateDirection D (a 1))) = _
      rw [add_apply,inner_add_right,ih]
      rfl
  rw [hs,materialWordsTerms_value]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w hw
  exact actual_word_coordinate_expansion d w (nonempty_of_mem_words hm hw) a ht y

theorem materialWordsTerms_mass (l : ℝ) (hl : 0 ≤ l) (m : ℕ) :
    materialMass (materialWordsTerms l m) =
      ((words m).map (fun w => l^w.length*materialMass (materialWordTerms l w))).sum := by
  unfold materialWordsTerms materialMass
  rw [List.map_flatMap,Conditional.JetCalculus.list_sum_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w _
  simp only [List.map_map,Function.comp_def,abs_mul,
    abs_of_nonneg (pow_nonneg hl w.length)]
  exact List.sum_map_mul_left _ _ _

theorem materialWordsTerms_source_budgets (l : ℝ) (m : ℕ) (hm : 0<m) :
    ∀ u ∈ materialWordsTerms l m,
      IsMaterialExpression u.expression ∧ u.expression.size ≤ 3*m-1 ∧
      u.expression.weight ≤ 2*((m-1:ℕ):ℝ≥0) ∧ u.degree ≤ m := by
  intro u hu
  obtain ⟨w,hw,hu⟩ := List.mem_flatMap.mp hu
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
  exact ⟨materialWordTerms_isMaterial l w v hv,materialWordTerms_source_budgets l hm hw v hv⟩

theorem actual_materialWordsTerms_mass {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (hsmall : d.r^2*d.ell ≤ 1/2) (m : ℕ) (hm : 0<m) :
    materialMass (materialWordsTerms (d.ell*d.r^2) m) ≤
      (d.ell*d.r^2)*(m.factorial:ℝ)*(materialWordMassBase m)^m := by
  have hl0 := mul_nonneg d.hell (sq_nonneg d.r)
  rw [materialWordsTerms_mass _ hl0]
  exact materialWords_physical_mass _ hl0 (by nlinarith) m hm

/-- The literal finite sum in the Hilbert coefficient tensor space. -/
def materialTermsTensor {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (ts : List (MaterialTerm 2)) (t : ℝ) (y : EuclideanSpace ℝ (Fin D)) : FinCoeff 2 D :=
  (ts.map (fun u => (u.coefficient*t^u.degree) •
    Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) u.expression y)).sum

theorem materialTermsTensor_apply {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (ts : List (MaterialTerm 2)) (t : ℝ) (y : EuclideanSpace ℝ (Fin D)) (a : Fin 2 → Fin D) :
    materialTermsTensor d ts t y a = materialTermsValue d ts a (t,y) := by
  induction ts with
  | nil => rfl
  | cons u ts ih =>
    change (u.coefficient*t^u.degree)*materialExpressionValue d u.expression a (t,y) +
      materialTermsTensor d ts t y a = _
    rw [ih]
    rfl

def operatorTensor {D : ℕ}
    (A : EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D)) : FinCoeff 2 D :=
  toLp 2 (fun a => inner ℝ (coordinateDirection D (a 0)) (A (coordinateDirection D (a 1))))

theorem actual_wordSum_tensor_expansion {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (m : ℕ) (hm : 0<m)
    {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) (y : EuclideanSpace ℝ (Fin D)) :
    operatorTensor (evaluateSum (fun j u => d.jacobianCoefficientJet j u y) (words m) t) =
      materialTermsTensor d (materialWordsTerms (d.ell*d.r^2) m) t (d.state t y).fst := by
  ext a
  rw [materialTermsTensor_apply]
  exact actual_wordSum_coordinate_expansion d m hm a ht y

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
