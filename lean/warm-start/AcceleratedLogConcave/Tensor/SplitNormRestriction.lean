import AcceleratedLogConcave.Tensor.SplitNorm

noncomputable section
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor

private def coordinateExtend {I J : Type*} [Fintype I] [DecidableEq J]
    (e : I → J) (u : I → ℝ) (j : J) : ℝ := ∑ i, if e i = j then u i else 0

private theorem coordinateExtend_apply {I J : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq J] (e : I → J) (he : Function.Injective e) (u : I → ℝ) (i : I) :
    coordinateExtend e u (e i) = u i := by
  simp [coordinateExtend, he.eq_iff]

private theorem sum_coordinateExtend_mul {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (e : I → J) (u : I → ℝ) (h : J → ℝ) :
    ∑ j, coordinateExtend e u j * h j = ∑ i, u i * h (e i) := by
  simp only [coordinateExtend, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

private theorem sum_coordinateExtend_sq {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I → J) (he : Function.Injective e) (u : I → ℝ) :
    ∑ j, (coordinateExtend e u j)^2 = ∑ i, (u i)^2 := by
  simp only [pow_two]
  rw [sum_coordinateExtend_mul]
  simp only [coordinateExtend_apply e he]

/-- Restricting a rectangular Euclidean matrix to injectively selected rows
and columns cannot increase its actual Hilbert-space operator norm. -/
theorem matrixCLM_submatrix_norm_le {I J R C : Type*}
    [Fintype I] [Fintype J] [Fintype R] [Fintype C]
    [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C ℝ) (e : I → R) (he : Function.Injective e)
    (f : J → C) (hf : Function.Injective f) :
    ‖matrixCLMEquiv (A.submatrix e f)‖ ≤ ‖matrixCLMEquiv A‖ := by
  apply matrixCLM_norm_le_of_bilinear_sq _ _ (norm_nonneg _)
  intro u v
  have hh := bilinear_sq_le_of_matrixCLM_norm_le A ‖matrixCLMEquiv A‖
    (norm_nonneg _) le_rfl (coordinateExtend e u) (coordinateExtend f v)
  have hs : (∑ r, ∑ c, coordinateExtend e u r * A r c * coordinateExtend f v c) =
      ∑ i, ∑ j, u i * A (e i) (f j) * v j := by
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [sum_coordinateExtend_mul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp_rw [mul_comm (A (e i) _)]
    rw [sum_coordinateExtend_mul]
  rw [hs, sum_coordinateExtend_sq e he, sum_coordinateExtend_sq f hf] at hh
  exact hh

/-- Slot-dependent injective coordinate restriction preserves every split
operator norm bound. Output slots have exactly the same Hilbert norm as all
other slots. -/
theorem splitNorm_coordinateRestriction_le {Slot : Type*} [Fintype Slot]
    [DecidableEq Slot] {D N : ℕ} (e : Slot → Fin D → Fin N)
    (he : ∀ s, Function.Injective (e s)) (S : Finset Slot) (T : Coeff Slot N) :
    splitNorm D S (WithLp.toLp 2 (fun a => T (fun s => e s (a s)))) ≤
      splitNorm N S T := by
  let er : LeftAssignment D S → LeftAssignment N S := fun a s => e s (a s)
  let ec : RightAssignment D S → RightAssignment N S := fun a s => e s (a s)
  have her : Function.Injective er := by
    intro a b hab
    funext s
    exact he s (congrFun hab s)
  have hec : Function.Injective ec := by
    intro a b hab
    funext s
    exact he s (congrFun hab s)
  have hm : unfoldEquiv D S (WithLp.toLp 2 (fun a => T (fun s => e s (a s)))) =
      (unfoldEquiv N S T).submatrix er ec := by
    ext a b
    change T (fun s => e s (if h : s ∈ S then a ⟨s,h⟩ else b ⟨s,h⟩)) =
      T (fun s => if h : s ∈ S then er a ⟨s,h⟩ else ec b ⟨s,h⟩)
    apply congrArg (fun a => T a)
    funext s
    split <;> rfl
  change ‖matrixCLMEquiv (unfoldEquiv D S _)‖ ≤ ‖matrixCLMEquiv (unfoldEquiv N S T)‖
  rw [hm]
  exact matrixCLM_submatrix_norm_le _ er her ec hec

end AcceleratedLogConcave.Tensor
