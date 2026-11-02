import AcceleratedLogConcave.Tensor.InverseSubsetLabels
import AcceleratedLogConcave.Tensor.OriginalDataInverseProduct
import AcceleratedLogConcave.Tensor.ThreeFactorInverseCuts

/-!

-/
noncomputable section
set_option autoImplicit false
open Set Function
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.InverseFlow
open Conditional Conditional.Transport.SpatialFlow
open ActualCoefficient EdgeClosure FlowInduction
open LabeledOperatorLeibniz hiding Space basis
variable {D : ℕ}

private theorem iteratedFDeriv_cast {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → V) (y : E) {m n : ℕ} (h : m = n) (v : Fin n → E) :
    iteratedFDeriv ℝ m f y (v ∘ Fin.cast h) = iteratedFDeriv ℝ n f y v := by
  subst n
  rfl

private theorem iteratedFDeriv_order_zero {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → V) (y : E) {m : ℕ} (h : m = 0) (v : Fin m → E) :
    iteratedFDeriv ℝ m f y v = f y := by
  subst m
  simp

/-- Full-subset evaluation with the dependent count casts paid explicitly. -/
theorem inverse_product_full_subset
    (d : PositiveVarianceFlowData (Space D)) (t : ℝ) (n : ℕ)
    (y : Space D) (v : Fin n → Space D) :
    term (actualB d t) (actualJ d t) ((subsetEquiv n).symm Finset.univ) y v =
      (iteratedFDeriv ℝ n (actualB d t) y v).comp (actualJ d t y) := by
  rw [subsetEquiv_symm_univ]
  unfold term
  rw [fullLeft_leftEmb,
    iteratedFDeriv_cast _ _ (fullLeft_leftCount n) v,
    iteratedFDeriv_order_zero _ _ (fullLeft_rightCount n)]

/-- Isolate the full derivative subset, then multiply by actual B on the RIGHT.
Only JB=I is used in this cancellation; order is not commuted. -/
theorem original_data_inverse_recurrence
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) (n : ℕ) (hn : 0 < n)
    (y : Space D) (v : Fin n → Space D) :
    iteratedFDeriv ℝ n (actualB d t) y v =
      -(∑ S ∈ properSubsets n,
        (term (actualB d t) (actualJ d t) ((subsetEquiv n).symm S) y v).comp
          (actualB d t y)) := by
  let f : Finset (Fin n) → (Space D →L[ℝ] Space D) :=
    fun S => term (actualB d t) (actualJ d t) ((subsetEquiv n).symm S) y v
  have hz : ∑ S, f S = 0 := original_data_inverse_product_sum d hsmall ht n hn y v
  have he := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n))) f
    (Finset.mem_univ (Finset.univ : Finset (Fin n)))
  have hi : (∑ S ∈ properSubsets n, f S) +
      (iteratedFDeriv ℝ n (actualB d t) y v).comp (actualJ d t y) = 0 := by
    rw [← inverse_product_full_subset]
    exact he.trans hz
  have hr := congrArg (fun L : Space D →L[ℝ] Space D => L * actualB d t y) hi
  simp only [zero_mul] at hr
  change ((∑ S ∈ properSubsets n, f S) +
    (iteratedFDeriv ℝ n (actualB d t) y v)*actualJ d t y)*actualB d t y = 0 at hr
  rw [add_mul,mul_assoc,(original_data_inverse_pair d t y).1,mul_one,
    Finset.sum_mul] at hr
  exact eq_neg_of_add_eq_zero_right hr

/-- Every term has all original labels in the SAME operator slot type. -/
def inverseSubsetCoeff (d : PositiveVarianceFlowData (Space D))
    (n : ℕ) (t : ℝ) (y : Space D) (S : Finset (Fin n)) :
    Coeff ((Fin n ⊕ Unit) ⊕ Unit) D :=
  relabel D (inverseSubsetChart S)
    (threeFactorCoeff
      (iteratedFDeriv ℝ (leftCount ((subsetEquiv n).symm S)) (actualB d t) y)
      (iteratedFDeriv ℝ (rightCount ((subsetEquiv n).symm S)) (actualJ d t) y)
      (actualB d t y))

 theorem inverseSubsetCoeff_apply (d : PositiveVarianceFlowData (Space D))
    (n : ℕ) (t : ℝ) (y : Space D) (S : Finset (Fin n))
    (a : ((Fin n ⊕ Unit) ⊕ Unit) → Fin D) :
    inverseSubsetCoeff d n t y S a =
      inner ℝ (basis D (a (.inr ())))
        (((term (actualB d t) (actualJ d t) ((subsetEquiv n).symm S) y
          (fun j => basis D (a (.inl (.inl j))))).comp (actualB d t y))
          (basis D (a (.inl (.inr ()))))) := by
  rfl

/-- Signed coefficient equality, not a directional/operator-norm surrogate. -/
theorem original_data_inverse_coefficient_sum
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) (n : ℕ) (hn : 0 < n) (y : Space D) :
    inverseJetCoeff d n t y = -(∑ S ∈ properSubsets n, inverseSubsetCoeff d n t y S) := by
  ext a
  change inner ℝ (basis D (a (.inr ())))
    ((iteratedFDeriv ℝ n (actualB d t) y
      (fun j => basis D (a (.inl (.inl j)))))
      (basis D (a (.inl (.inr ()))))) =
    -((∑ S ∈ properSubsets n, inverseSubsetCoeff d n t y S) a)
  rw [ActualPartitionTree.coeff_finset_sum_apply]
  rw [original_data_inverse_recurrence d hsmall ht n hn]
  simp only [neg_apply,sum_apply,
    inner_neg_right,inner_sum]
  congr 1

/-- Finite triangle inequality at one fixed arbitrary proper rectangular cut. -/
theorem inverse_coefficient_sum_allProper
    {n : ℕ} (T : Finset (Fin n) → Coeff ((Fin n ⊕ Unit) ⊕ Unit) D)
    (C : Finset (Fin n) → ℝ)
    (hT : ∀ S ∈ properSubsets n, AllProper D (T S) (C S)) :
    AllProper D (-(∑ S ∈ properSubsets n, T S)) (∑ S ∈ properSubsets n, C S) := by
  intro R hR
  change ‖splitOperatorEquiv D R (-(∑ S ∈ properSubsets n, T S))‖ ≤ _
  rw [map_neg,norm_neg,map_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun S hS => hT S hS R hR))

end AcceleratedLogConcave.Tensor.InverseFlow
