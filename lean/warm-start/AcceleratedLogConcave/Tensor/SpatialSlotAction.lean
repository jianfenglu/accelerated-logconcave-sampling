import AcceleratedLogConcave.Tensor.SplitNormRestriction

/-

-/
noncomputable section
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] {D : ℕ}

/-- A matrix acting on one assignment coordinate, identity on all other slots. -/
def spatialSlotMatrix (i : Slot) (A : Matrix (Fin D) (Fin D) ℝ) :
    Matrix (Slot → Fin D) (Slot → Fin D) ℝ :=
  (Matrix.kronecker A (1 : Matrix ({j : Slot // j ≠ i} → Fin D)
    ({j : Slot // j ≠ i} → Fin D) ℝ)).submatrix
      (Equiv.funSplitAt i (Fin D)) (Equiv.funSplitAt i (Fin D))

private theorem matrix_identity_norm_le {I : Type*} [Fintype I] [DecidableEq I] :
    ‖matrixCLMEquiv (1 : Matrix I I ℝ)‖ ≤ 1 := by
  have he : matrixCLMEquiv (1 : Matrix I I ℝ) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ I) := by
    ext v i
    rw [matrixCLMEquiv_apply]
    simp [Matrix.one_apply]
  rw [he]
  exact ContinuousLinearMap.norm_id_le

/-- Lifting an actual matrix to one tensor slot does not increase its operator
norm, including zero physical dimension. -/
theorem spatialSlotMatrix_norm_le (i : Slot) (A : Matrix (Fin D) (Fin D) ℝ) :
    ‖matrixCLMEquiv (spatialSlotMatrix i A)‖ ≤ ‖matrixCLMEquiv A‖ := by
  apply (matrixCLM_submatrix_norm_le _ (Equiv.funSplitAt i (Fin D))
    (Equiv.funSplitAt i (Fin D)).injective (Equiv.funSplitAt i (Fin D))
    (Equiv.funSplitAt i (Fin D)).injective).trans
  exact (matrixCLM_kronecker_norm_le A _).trans
    ((mul_le_mul_of_nonneg_left matrix_identity_norm_le (norm_nonneg _)).trans_eq (mul_one _))

/-- Literal coordinate action, with no assumed matrix interpretation. -/
def spatialSlotAction (i : Slot) (A : Matrix (Fin D) (Fin D) ℝ)
    (T : Coeff Slot D) : Coeff Slot D :=
  WithLp.toLp 2 (fun a => ∑ k : Fin D, A (a i) k * T (Function.update a i k))

theorem spatialSlotMatrix_sum (i : Slot) (A : Matrix (Fin D) (Fin D) ℝ)
    (f : (Slot → Fin D) → ℝ) (a : Slot → Fin D) :
    ∑ b, spatialSlotMatrix i A a b * f b =
      ∑ k : Fin D, A (a i) k * f (Function.update a i k) := by
  let e := Equiv.funSplitAt i (Fin D)
  have hsplit : (∑ b, spatialSlotMatrix i A a b * f b) =
      ∑ p : Fin D × ({j : Slot // j ≠ i} → Fin D),
        A (a i) p.1 * (if (fun j : {j : Slot // j ≠ i} => a j) = p.2 then 1 else 0) * f (e.symm p) := by
    apply Fintype.sum_equiv e
    intro b
    have hb : (fun j => if j = i then b i else b j) = b := by
      funext j
      split_ifs with h
      · subst j; rfl
      · rfl
    simp [spatialSlotMatrix,e,Matrix.one_apply,Equiv.funSplitAt,Equiv.piSplitAt,hb]
  rw [hsplit,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 2

theorem spatialSlotAction_eq_matrix (i : Slot) (A : Matrix (Fin D) (Fin D) ℝ)
    (T : Coeff Slot D) : spatialSlotAction i A T = matrixCLMEquiv (spatialSlotMatrix i A) T := by
  ext a
  exact (spatialSlotMatrix_sum i A T a).symm

/-- Dimension-free Hilbert norm control, before selecting a tensor split. -/
theorem spatialSlotAction_norm_le (i : Slot) (A : Matrix (Fin D) (Fin D) ℝ)
    (T : Coeff Slot D) : ‖spatialSlotAction i A T‖ ≤ ‖matrixCLMEquiv A‖ * ‖T‖ := by
  rw [spatialSlotAction_eq_matrix]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (spatialSlotMatrix_norm_le i A) (norm_nonneg _))

private theorem spatial_matrix_mul {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (A : Matrix I J ℝ) (B : Matrix J K ℝ) :
    matrixCLMEquiv (A * B) = (matrixCLMEquiv A).comp (matrixCLMEquiv B) := by
  ext v i
  simp only [matrixCLMEquiv_apply,Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum,
    ContinuousLinearMap.comp_apply]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

private theorem spatial_matrix_transpose_norm {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J ℝ) :
    ‖matrixCLMEquiv A.transpose‖ ≤ ‖matrixCLMEquiv A‖ := by
  apply matrixCLM_norm_le_of_bilinear_sq _ _ (norm_nonneg _)
  intro u v
  have h := bilinear_sq_le_of_matrixCLM_norm_le A ‖matrixCLMEquiv A‖
    (norm_nonneg _) le_rfl v u
  have he : (∑ i, ∑ j, v i * A i j * u j) =
      ∑ j, ∑ i, u j * A.transpose j i * v i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.transpose_apply]
    ring
  rw [he] at h
  nlinarith [h]

omit [Fintype Slot] in
private theorem assignment_update_left (S : Finset Slot) (i : Slot) (hi : i ∈ S)
    (a : LeftAssignment D S) (b : RightAssignment D S) (k : Fin D) :
    Function.update ((assignmentEquiv D S).symm (a,b)) i k =
      (assignmentEquiv D S).symm (Function.update a ⟨i,hi⟩ k,b) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [assignmentEquiv,Equiv.piEquivPiSubtypeProd,hi]
  · by_cases hj : j ∈ S
    · simp [assignmentEquiv,Equiv.piEquivPiSubtypeProd,hj,hji,Subtype.ext_iff]
    · simp [assignmentEquiv,Equiv.piEquivPiSubtypeProd,hj,hji]

omit [Fintype Slot] in
private theorem assignment_update_right (S : Finset Slot) (i : Slot) (hi : i ∉ S)
    (a : LeftAssignment D S) (b : RightAssignment D S) (k : Fin D) :
    Function.update ((assignmentEquiv D S).symm (a,b)) i k =
      (assignmentEquiv D S).symm (a,Function.update b ⟨i,hi⟩ k) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [assignmentEquiv,Equiv.piEquivPiSubtypeProd,hi]
  · by_cases hj : j ∈ S
    · simp [assignmentEquiv,Equiv.piEquivPiSubtypeProd,hj,hji]
    · simp [assignmentEquiv,Equiv.piEquivPiSubtypeProd,hj,hji,Subtype.ext_iff]

/-- Single-slot action preserves every split bound with exactly one matrix
operator norm, regardless of which side contains that slot. -/
theorem spatialSlotAction_splitNorm_le (S : Finset Slot) (i : Slot)
    (A : Matrix (Fin D) (Fin D) ℝ) (T : Coeff Slot D) :
    splitNorm D S (spatialSlotAction i A T) ≤ ‖matrixCLMEquiv A‖ * splitNorm D S T := by
  by_cases hi : i ∈ S
  · have he : unfoldEquiv D S (spatialSlotAction i A T) =
        spatialSlotMatrix (⟨i,hi⟩ : S) A * unfoldEquiv D S T := by
      ext a b
      rw [Matrix.mul_apply,spatialSlotMatrix_sum]
      change (∑ k, A (((assignmentEquiv D S).symm (a,b)) i) k *
        T (Function.update ((assignmentEquiv D S).symm (a,b)) i k)) = _
      apply Finset.sum_congr rfl
      intro k _
      rw [assignment_update_left S i hi]
      simp only [unfold_apply]
      simp [assignmentEquiv, Equiv.piEquivPiSubtypeProd, hi]
    change ‖matrixCLMEquiv (unfoldEquiv D S _)‖ ≤ _
    rw [he,spatial_matrix_mul]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (spatialSlotMatrix_norm_le _ A) (norm_nonneg _))
  · have he : unfoldEquiv D S (spatialSlotAction i A T) =
        unfoldEquiv D S T * (spatialSlotMatrix (⟨i,hi⟩ : {j : Slot // j ∉ S}) A).transpose := by
      ext a b
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply]
      rw [show (∑ c, unfoldEquiv D S T a c *
          spatialSlotMatrix (⟨i,hi⟩ : {j : Slot // j ∉ S}) A b c) =
          ∑ c, spatialSlotMatrix (⟨i,hi⟩ : {j : Slot // j ∉ S}) A b c *
            unfoldEquiv D S T a c by
        apply Finset.sum_congr rfl
        intro c _
        exact mul_comm _ _, spatialSlotMatrix_sum]
      change (∑ k, A (((assignmentEquiv D S).symm (a,b)) i) k *
        T (Function.update ((assignmentEquiv D S).symm (a,b)) i k)) = _
      apply Finset.sum_congr rfl
      intro k _
      rw [assignment_update_right S i hi]
      simp only [unfold_apply]
      simp [assignmentEquiv, Equiv.piEquivPiSubtypeProd, hi]
    change ‖matrixCLMEquiv (unfoldEquiv D S _)‖ ≤ _
    rw [he,spatial_matrix_mul]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    calc
      _ ≤ splitNorm D S T * ‖matrixCLMEquiv A‖ :=
        mul_le_mul_of_nonneg_left
          ((spatial_matrix_transpose_norm _).trans (spatialSlotMatrix_norm_le _ A)) (norm_nonneg _)
      _ = _ := mul_comm _ _
end AcceleratedLogConcave.Tensor
