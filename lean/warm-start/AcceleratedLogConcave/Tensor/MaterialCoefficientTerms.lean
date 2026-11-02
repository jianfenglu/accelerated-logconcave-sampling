import AcceleratedLogConcave.Tensor.MaterialMatrixProduct

noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab Set

/-- The normalized C-jet alternatives; the common factor ell*r² stays outside. -/
def materialCoefficientTerms (l : ℝ) (k : ℕ) : List (MaterialTerm 2) :=
  (materialIterate l (.coefficient (Sum.inl 0)) k).map
    (fun u => ⟨u.coefficient,u.degree+1,u.expression⟩) ++
  (materialIterate l (.coefficient (Sum.inl 0)) (k-1)).map
    (fun u => ⟨(k:ℝ)*u.coefficient,u.degree,u.expression⟩)

theorem materialCoefficientTerms_value {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (k : ℕ)
    (a : Fin 2 → Fin D) (p : ℝ × EuclideanSpace ℝ (Fin D)) :
    materialTermsValue d (materialCoefficientTerms (d.ell*d.r^2) k) a p =
      p.1 * materialTermsValue d (materialIterate (d.ell*d.r^2) (.coefficient (Sum.inl 0)) k) a p +
      (k:ℝ) * materialTermsValue d (materialIterate (d.ell*d.r^2) (.coefficient (Sum.inl 0)) (k-1)) a p := by
  unfold materialCoefficientTerms materialTermsValue
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,MaterialTerm.value,pow_succ]
  congr 1
  · rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro u _
    ring
  · rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro u _
    ring

theorem jacobianCoefficientJet_eq_terms {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (k : ℕ)
    (a : Fin 2 → Fin D) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : EuclideanSpace ℝ (Fin D)) :
    inner ℝ (coordinateDirection D (a 0))
      (d.jacobianCoefficientJet k t y (coordinateDirection D (a 1))) =
      (d.ell*d.r^2) * materialTermsValue d (materialCoefficientTerms (d.ell*d.r^2) k)
        a (t,(d.state t y).fst) := by
  rw [materialCoefficientTerms_value]
  exact jacobianCoefficientJet_coordinate_expansion d k a ht y

theorem materialCoefficientTerms_isMaterial (l : ℝ) (k : ℕ) :
    ∀ u ∈ materialCoefficientTerms l k, IsMaterialExpression u.expression := by
  intro u hu
  simp only [materialCoefficientTerms,List.mem_append,List.mem_map] at hu
  rcases hu with ⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩
  · exact materialIterate_isMaterial l _ (by trivial) k v hv
  · exact materialIterate_isMaterial l _ (by trivial) (k-1) v hv

theorem materialCoefficientTerms_size_degree (l : ℝ) (k : ℕ) :
    ∀ u ∈ materialCoefficientTerms l k, u.expression.size ≤ 2+3*k ∧ u.degree ≤ k+1 := by
  intro u hu
  simp only [materialCoefficientTerms,List.mem_append,List.mem_map] at hu
  rcases hu with ⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩
  · have hh := materialIterate_size_degree l (.coefficient (Sum.inl 0)) k v hv
    change v.expression.size ≤ 2+3*k ∧ v.degree+1 ≤ k+1
    change v.expression.size ≤ 2+3*k ∧ v.degree ≤ k at hh
    omega
  · have hh := materialIterate_size_degree l (.coefficient (Sum.inl 0)) (k-1) v hv
    change v.expression.size ≤ 2+3*k ∧ v.degree ≤ k+1
    change v.expression.size ≤ 2+3*(k-1) ∧ v.degree ≤ k-1 at hh
    omega

theorem materialCoefficientTerms_weight (l : ℝ) (k : ℕ) :
    ∀ u ∈ materialCoefficientTerms l k, u.expression.weight ≤ 2*(k:ℝ≥0) := by
  intro u hu
  simp only [materialCoefficientTerms,List.mem_append,List.mem_map] at hu
  rcases hu with ⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩
  · simpa [Expr.weight,signature] using materialIterate_weight l (.coefficient (Sum.inl 0)) k v hv
  · have hh := materialIterate_weight l (.coefficient (Sum.inl 0)) (k-1) v hv
    have hk : ((k-1:ℕ):ℝ≥0) ≤ (k:ℝ≥0) := by exact_mod_cast Nat.sub_le k 1
    have hbound : v.expression.weight ≤ 2*((k-1:ℕ):ℝ≥0) := by
      simpa [Expr.weight,signature] using hh
    exact hbound.trans (mul_le_mul_of_nonneg_left hk (by positivity))

theorem materialCoefficientTerms_mass (l : ℝ) (k : ℕ) :
    materialMass (materialCoefficientTerms l k) =
      materialMass (materialIterate l (.coefficient (Sum.inl 0)) k) +
      (k:ℝ) * materialMass (materialIterate l (.coefficient (Sum.inl 0)) (k-1)) := by
  unfold materialCoefficientTerms
  rw [materialMass_append]
  simp only [materialMass,List.map_map,Function.comp_def,abs_mul,
    abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  congr 1
  exact List.sum_map_mul_left _ _ _

theorem materialCoefficientTerms_mass_le (l : ℝ) (hl : |l| ≤ 1) (k : ℕ) :
    materialMass (materialCoefficientTerms l k) ≤
      materialMassBudget 2 k + (k:ℝ)*materialMassBudget 2 (k-1) := by
  rw [materialCoefficientTerms_mass]
  exact add_le_add (materialIterate_mass l hl (.coefficient (Sum.inl 0)) k)
    (mul_le_mul_of_nonneg_left (materialIterate_mass l hl (.coefficient (Sum.inl 0)) (k-1))
      (Nat.cast_nonneg k))

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
