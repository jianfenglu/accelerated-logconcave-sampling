import AcceleratedLogConcave.Tensor.OrderedPartitionConsumers

/-!

-/
noncomputable section
open scoped BigOperators Classical ContDiff
namespace AcceleratedLogConcave.Tensor.ActualPartitionTree
open EdgeClosure ActualCoefficient
variable {D n : ℕ}

/-- Pointwise finite-sum evaluation proved directly, avoiding deprecated
multilinear sum_apply aliases in new production code. -/
theorem coeff_finset_sum_apply {X J : Type*} [Fintype X] [DecidableEq J]
    (s : Finset J) (F : J → Coeff X D) (a : X → Fin D) :
    (∑ j ∈ s, F j) a = ∑ j ∈ s, F j a := by
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      change F j a + (∑ k ∈ s, F k) a = F j a + ∑ k ∈ s, F k a
      rw [ih]

/-- Actual derivative coefficient is precisely the finite sum of the actual
partition trees already bounded, including n=0 and repeated coordinate labels. -/
theorem actual_derivative_partition_sum
    (U : Space D → (Space D →L[ℝ] Space D)) (Y : Space D → Space D)
    (y : Space D) (hU : ContDiffAt ℝ ∞ U (Y y)) (hY : ContDiffAt ℝ ∞ Y y) :
    operatorCoeff (iteratedFDeriv ℝ n (U ∘ Y) y) =
      ∑ c : OrderedFinpartition n,
        operatorCoeff (c.compAlongOrderedFinpartition
          (iteratedFDeriv ℝ c.length U (Y y))
          (fun i => iteratedFDeriv ℝ (c.partSize i) Y y)) := by
  ext a
  rw [coeff_finset_sum_apply]
  change inner ℝ (basis D (a (.inr ())))
    ((iteratedFDeriv ℝ n (U ∘ Y) y
      (fun j => basis D (a (.inl (.inl j)))))
      (basis D (a (.inl (.inr ()))))) = _
  rw [operator_composition_derivative_coefficient U Y y hU hY n
    (fun j => a (.inl (.inl j))) (a (.inl (.inr ()))) (a (.inr ()))]
  apply Finset.sum_congr rfl
  intro c _
  exact (partition_coefficient_basis_sum c
    (iteratedFDeriv ℝ c.length U (Y y))
    (fun i => iteratedFDeriv ℝ (c.partSize i) Y y) a).symm

/-- H_n-style budget for the actual U(Y) derivative, conditional ONLY on the
root U-jets and positive Y-branch jets. No unknown composite bound is assumed.
All norms in the conclusion are genuine rectangular Hilbert operator cuts. -/
theorem actual_composition_allProper
    (U : Space D → (Space D →L[ℝ] Space D)) (Y : Space D → Space D)
    (y : Space D) (hU : ContDiffAt ℝ ∞ U (Y y)) (hY : ContDiffAt ℝ ∞ Y y)
    (CU CY : ℕ → ℝ) (hCU : ∀ k, 0 ≤ CU k) (hCY : ∀ k, 0 ≤ CY k)
    (hroot : ∀ c : OrderedFinpartition n,
      AllProper D (operatorCoeff (iteratedFDeriv ℝ c.length U (Y y))) (CU c.length))
    (hbranch : ∀ (c : OrderedFinpartition n) (i : Fin c.length),
      AllProper D (vectorCoeff (iteratedFDeriv ℝ (c.partSize i) Y y)) (CY (c.partSize i))) :
    AllProper D (operatorCoeff (iteratedFDeriv ℝ n (U ∘ Y) y))
      (∑ c : OrderedFinpartition n, CU c.length * ∏ i, CY (c.partSize i)) := by
  rw [actual_derivative_partition_sum U Y y hU hY]
  apply allProper_sum
  intro c
  exact actual_composition_partition_allProper U Y y c
    (CU c.length) (fun i => CY (c.partSize i)) (hCU c.length)
    (fun i => hCY (c.partSize i)) (hroot c) (hbranch c)

end AcceleratedLogConcave.Tensor.ActualPartitionTree
