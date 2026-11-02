import AcceleratedLogConcave.Tensor.MaterialCoefficientTerms

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab Analysis.OrderedJacobianWords Set

/-- Nonempty ordered C words are expanded without inserting an identity tensor. -/
def materialWordTerms (l : ℝ) : Word → List (MaterialTerm 2)
  | [] => []
  | [j] => materialCoefficientTerms l j
  | j :: k :: w => materialTermsProduct (materialCoefficientTerms l j) (materialWordTerms l (k::w))

theorem materialWordTerms_isMaterial (l : ℝ) (w : Word) :
    ∀ u ∈ materialWordTerms l w, IsMaterialExpression u.expression := by
  induction w with
  | nil => simp [materialWordTerms]
  | cons j w ih =>
    cases w with
    | nil => exact materialCoefficientTerms_isMaterial l j
    | cons k w => exact materialTermsProduct_isMaterial _ _ (materialCoefficientTerms_isMaterial l j) ih

theorem materialWordTerms_size_degree (l : ℝ) (w : Word) :
    ∀ u ∈ materialWordTerms l w,
      u.expression.size ≤ 3*order w-1 ∧ u.degree ≤ order w := by
  induction w with
  | nil => simp [materialWordTerms]
  | cons j w ih =>
    cases w with
    | nil =>
      intro u hu
      have hh := materialCoefficientTerms_size_degree l j u hu
      simp only [order_cons,order_nil]
      omega
    | cons k w =>
      intro u hu
      have hh := materialTermsProduct_size_degree _ _ (2+3*j) (3*order (k::w)-1)
        (j+1) (order (k::w)) (materialCoefficientTerms_size_degree l j) ih u hu
      have hp := length_le_order (k::w)
      simp only [List.length_cons] at hp
      simp only [order_cons]
      simp only [order_cons] at hh
      omega

theorem materialWordTerms_weight (l : ℝ) (w : Word) :
    ∀ u ∈ materialWordTerms l w, u.expression.weight ≤ 2*((order w-w.length:ℕ):ℝ≥0) := by
  induction w with
  | nil => simp [materialWordTerms]
  | cons j w ih =>
    cases w with
    | nil => simpa [materialWordTerms,order_cons,order_nil] using materialCoefficientTerms_weight l j
    | cons k w =>
      intro u hu
      have hh := materialTermsProduct_weight _ _ (2*(j:ℝ≥0))
        (2*((order (k::w)-(k::w).length:ℕ):ℝ≥0)) (materialCoefficientTerms_weight l j) ih u hu
      have hp := length_le_order (k::w)
      have he : order (j::k::w)-(j::k::w).length = j+(order (k::w)-(k::w).length) := by
        simp only [order_cons,List.length_cons] at *
        omega
      rw [he,Nat.cast_add,mul_add]
      exact hh

theorem actual_word_coordinate_expansion {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (w : Word) (hw : w ≠ [])
    (a : Fin 2 → Fin D) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b))
    (y : EuclideanSpace ℝ (Fin D)) :
    inner ℝ (coordinateDirection D (a 0))
      (evaluate (fun j u => d.jacobianCoefficientJet j u y) w t (coordinateDirection D (a 1))) =
      (d.ell*d.r^2)^w.length * materialTermsValue d
        (materialWordTerms (d.ell*d.r^2) w) a (t,(d.state t y).fst) := by
  induction w generalizing a with
  | nil => exact (hw rfl).elim
  | cons j w ih =>
    cases w with
    | nil =>
      simpa [evaluate_cons,evaluate_nil,materialWordTerms] using
        jacobianCoefficientJet_eq_terms d j a ht y
    | cons k w =>
      rw [evaluate_cons,operator_coordinate_mul]
      have he (i : Fin D) :
          inner ℝ (coordinateDirection D i)
            (evaluate (fun j u => d.jacobianCoefficientJet j u y) (k::w) t
              (coordinateDirection D (a 1))) =
          (d.ell*d.r^2)^(k::w).length * materialTermsValue d
            (materialWordTerms (d.ell*d.r^2) (k::w)) ![i,a 1] (t,(d.state t y).fst) :=
        ih (by simp) ![i,a 1]
      have hf (i : Fin D) :
          inner ℝ (coordinateDirection D (a 0))
            (d.jacobianCoefficientJet j t y (coordinateDirection D i)) =
          (d.ell*d.r^2)*materialTermsValue d (materialCoefficientTerms (d.ell*d.r^2) j)
            ![a 0,i] (t,(d.state t y).fst) :=
        jacobianCoefficientJet_eq_terms d j ![a 0,i] ht y
      simp_rw [hf,he]
      rw [materialWordTerms,materialTermsProduct_value]
      simp only [List.length_cons,pow_succ,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem materialWordTerms_mass (l : ℝ) (w : Word) (hw : w ≠ []) :
    materialMass (materialWordTerms l w) =
      (w.map (fun j => materialMass (materialCoefficientTerms l j))).prod := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons j w ih =>
    cases w with
    | nil => simp [materialWordTerms]
    | cons k w =>
      rw [materialWordTerms,materialTermsProduct_mass,ih (by simp)]
      rfl

/-- The precise manuscript size/weight receiver at an actual positive word order. -/
theorem materialWordTerms_source_budgets (l : ℝ) {m : ℕ} {w : Word}
    (hm : 0<m) (hw : w ∈ words m) :
    ∀ u ∈ materialWordTerms l w,
      u.expression.size ≤ 3*m-1 ∧ u.expression.weight ≤ 2*((m-1:ℕ):ℝ≥0) ∧ u.degree ≤ m := by
  intro u hu
  have hs := materialWordTerms_size_degree l w u hu
  have hweight := materialWordTerms_weight l w u hu
  have hord := order_of_mem_words hw
  have hne := nonempty_of_mem_words hm hw
  have hlen : 1 ≤ w.length := List.length_pos_iff.mpr hne
  have hsub : order w-w.length ≤ m-1 := by omega
  have hcast : ((order w-w.length:ℕ):ℝ≥0) ≤ ((m-1:ℕ):ℝ≥0) := by exact_mod_cast hsub
  rw [hord] at hs
  exact ⟨hs.1,hweight.trans (mul_le_mul_of_nonneg_left hcast (by positivity)),hs.2⟩

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
