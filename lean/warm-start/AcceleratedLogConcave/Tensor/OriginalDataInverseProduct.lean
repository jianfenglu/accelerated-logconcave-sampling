import AcceleratedLogConcave.Tensor.OriginalDataInverseBase
import AcceleratedLogConcave.Tensor.LabeledOperatorLeibniz
import AcceleratedLogConcave.Tensor.LabeledOperatorCoefficients

/-!

-/
noncomputable section
set_option autoImplicit false
open Set Function
open scoped ContDiff Classical BigOperators
namespace AcceleratedLogConcave.Tensor.InverseFlow
open Conditional Conditional.Transport.SpatialFlow
open ActualCoefficient EdgeClosure FlowInduction
open LabeledOperatorLeibniz
variable {D : ℕ}

 theorem actual_BJ_constant (d : PositiveVarianceFlowData (ActualCoefficient.Space D)) (t : ℝ) :
    (fun z => (actualB d t z).comp (actualJ d t z)) =
      fun _ => (1 : ActualCoefficient.Space D →L[ℝ] ActualCoefficient.Space D) :=
  funext fun z => (original_data_inverse_pair d t z).2

/-- A literal solved first spatial derivative, with the noncommuting order B DJ B. -/
theorem original_data_inverse_fderiv (d : PositiveVarianceFlowData (ActualCoefficient.Space D))
    (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b)
    (y u : ActualCoefficient.Space D) :
    fderiv ℝ (actualB d t) y u =
      -((actualB d t y * (fderiv ℝ (actualJ d t) y u)) * actualB d t y) := by
  have hB := (original_data_B_smooth d hsmall ht).differentiable (by simp)
  have hJ := (original_data_J_smooth d hsmall ht).differentiable (by simp)
  have hd := congrArg (fun L => L u) (fderiv_clm_comp (hB y) (hJ y))
  simp only [actual_BJ_constant, fderiv_fun_const] at hd
  have hz : actualB d t y * (fderiv ℝ (actualJ d t) y u) +
      (fderiv ℝ (actualB d t) y u) * actualJ d t y = 0 := hd.symm
  have hx := congrArg (fun L => L * actualB d t y) hz
  rw [add_mul, mul_assoc (fderiv ℝ (actualB d t) y u),
    (original_data_inverse_pair d t y).1, mul_one, zero_mul] at hx
  exact eq_neg_of_add_eq_zero_right hx

/-- The full labeled product equation, retaining every derivative direction.
The sole top-B summand is not assumed away; it remains literally in the sum. -/
theorem original_data_inverse_product_sum (d : PositiveVarianceFlowData (ActualCoefficient.Space D))
    (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b)
    (n : ℕ) (hn : 0 < n) (y : ActualCoefficient.Space D)
    (v : Fin n → ActualCoefficient.Space D) :
    (∑ S : Finset (Fin n),
      (iteratedFDeriv ℝ (leftCount ((subsetEquiv n).symm S)) (actualB d t) y
        (v ∘ subsetLeftEmb S)).comp
      (iteratedFDeriv ℝ (rightCount ((subsetEquiv n).symm S)) (actualJ d t) y
        (v ∘ subsetRightEmb S))) = 0 := by
  rw [← iteratedFDeriv_comp_subsets (actualB d t) (actualJ d t)
    (original_data_B_smooth d hsmall ht) (original_data_J_smooth d hsmall ht),
    actual_BJ_constant, iteratedFDeriv_const_of_ne (Nat.ne_of_gt hn)]
  rfl

/-- Exact coefficient form, with all ordinary slots and internal coordinates.
This is not a norm on repeated directions, nor a dimension-positive statement. -/
theorem original_data_inverse_product_coordinates
    (d : PositiveVarianceFlowData (ActualCoefficient.Space D))
    (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b)
    (n : ℕ) (hn : 0 < n) (y : ActualCoefficient.Space D)
    (a : Fin n → Fin D) (i o : Fin D) :
    (∑ S : Finset (Fin n), ∑ w : Fin D,
      inner ℝ (ActualCoefficient.basis D o)
        ((iteratedFDeriv ℝ (leftCount ((subsetEquiv n).symm S)) (actualB d t) y
          (fun j => ActualCoefficient.basis D (a (subsetLeftEmb S j))))
          (ActualCoefficient.basis D w)) *
      inner ℝ (ActualCoefficient.basis D w)
        ((iteratedFDeriv ℝ (rightCount ((subsetEquiv n).symm S)) (actualJ d t) y
          (fun j => ActualCoefficient.basis D (a (subsetRightEmb S j))))
          (ActualCoefficient.basis D i))) = 0 := by
  rw [← iteratedFDeriv_comp_coefficient (actualB d t) (actualJ d t)
    (original_data_B_smooth d hsmall ht) (original_data_J_smooth d hsmall ht),
    actual_BJ_constant,iteratedFDeriv_const_of_ne (Nat.ne_of_gt hn)]
  simp

/-- Positive derivatives vanish at terminal time by equality of actual maps. -/
theorem original_data_inverse_terminal_positive
    (d : PositiveVarianceFlowData (ActualCoefficient.Space D))
    (n : ℕ) (hn : 0 < n) (y : ActualCoefficient.Space D) :
    iteratedFDeriv ℝ n (actualB d d.b) y = 0 := by
  have he : actualB d d.b = fun _ => ContinuousLinearMap.id ℝ (ActualCoefficient.Space D) :=
    funext fun z => transportedJacobian_terminal d.hF d.hell d.hlo d.hhi
      d.x d.hr d.hb0 d.hb1 z
  rw [he,iteratedFDeriv_const_of_ne (Nat.ne_of_gt hn)]
  rfl

/-- Physical dimension zero: coefficient zero by its retained ordinary output.
No false assertion that the identity on a zero space has norm one. -/
theorem inverseJetCoeff_dimension_zero
    (d : PositiveVarianceFlowData (ActualCoefficient.Space 0))
    (n : ℕ) (t : ℝ) (y : ActualCoefficient.Space 0) :
    inverseJetCoeff d n t y = 0 := by
  ext a
  exact Fin.elim0 (a (.inr ()))
end AcceleratedLogConcave.Tensor.InverseFlow
