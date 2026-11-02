import AcceleratedLogConcave.Tensor.MaterialWordsSum
import AcceleratedLogConcave.Analysis.GaussianLinearIsometry

noncomputable section
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Analysis

variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

theorem operatorTensor_norm_sq (A : E →L[ℝ] E) :
    ‖operatorTensor A‖^2 = ∑ i : Fin D, ‖A (coordinateDirection D i)‖^2 := by
  let b := EuclideanSpace.basisFun (Fin D) ℝ
  have hb (i : Fin D) : b i = coordinateDirection D i := by
    simp [b,EuclideanSpace.basisFun_apply,coordinateDirection,EuclideanSpace.single]
  have hc (v : E) : (∑ i : Fin D, (inner ℝ (coordinateDirection D i) v)^2) = ‖v‖^2 := by
    simpa [hb,Real.norm_eq_abs,sq_abs] using b.sum_sq_norm_inner_right v
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ a : Fin 2 → Fin D,
    (inner ℝ (coordinateDirection D (a 0)) (A (coordinateDirection D (a 1))))^2) = _
  calc
    _ = ∑ ij : Fin D × Fin D,
        (inner ℝ (coordinateDirection D ij.1) (A (coordinateDirection D ij.2)))^2 := by
      apply Fintype.sum_equiv (finTwoArrowEquiv (Fin D))
      intro a
      rfl
    _ = ∑ j : Fin D, ∑ i : Fin D,
        (inner ℝ (coordinateDirection D i) (A (coordinateDirection D j)))^2 := by
      rw [Fintype.sum_prod_type,Finset.sum_comm]
    _ = _ := by simp_rw [hc]

theorem operatorTensor_norm_mul_le (A B : E →L[ℝ] E) :
    ‖operatorTensor (A*B)‖ ≤ ‖A‖*‖operatorTensor B‖ := by
  have hsq : ‖operatorTensor (A*B)‖^2 ≤ ‖A‖^2*‖operatorTensor B‖^2 := by
    rw [operatorTensor_norm_sq,operatorTensor_norm_sq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change ‖A (B (coordinateDirection D i))‖^2 ≤ _
    have hh := A.le_opNorm (B (coordinateDirection D i))
    nlinarith [norm_nonneg (A (B (coordinateDirection D i))),
      mul_nonneg (norm_nonneg A) (norm_nonneg (B (coordinateDirection D i)))]
  nlinarith [norm_nonneg (operatorTensor (A*B)),
    mul_nonneg (norm_nonneg A) (norm_nonneg (operatorTensor B))]

theorem operatorTensor_norm_sq_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    ‖operatorTensor A‖^2 = ∑ i, ‖A (b i)‖^2 := by
  have hb (i : Fin D) : (EuclideanSpace.basisFun (Fin D) ℝ) i = coordinateDirection D i := by
    simp [EuclideanSpace.basisFun_apply,coordinateDirection,EuclideanSpace.single]
  rw [operatorTensor_norm_sq]
  rw [←GaussianLinearIsometry.integral_norm_sq_linear b A]
  simpa only [hb] using
    (GaussianLinearIsometry.integral_norm_sq_linear (EuclideanSpace.basisFun (Fin D) ℝ) A).symm

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
