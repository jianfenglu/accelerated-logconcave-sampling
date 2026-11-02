import AcceleratedLogConcave.Tensor.SplitNorm

/-! Every literal tensor entry is controlled by any rectangular split norm.
This is a qualitative jet-tail adapter, without an extra dimension factor. -/
noncomputable section
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Tensor
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] {D : ℕ}

theorem abs_coefficient_le_splitNorm (T : Coeff Slot D) (S : Finset Slot)
    (a : Slot → Fin D) : |T a| ≤ splitNorm D S T := by
  let r := (assignmentEquiv D S a).1
  let c := (assignmentEquiv D S a).2
  have h := split_pairing_bound D S T
    (EuclideanSpace.basisFun (LeftAssignment D S) ℝ r)
    (EuclideanSpace.basisFun (RightAssignment D S) ℝ c)
  have he : ⟪EuclideanSpace.basisFun (LeftAssignment D S) ℝ r,
      splitOperatorEquiv D S T (EuclideanSpace.basisFun (RightAssignment D S) ℝ c)⟫ = T a := by
    rw [EuclideanSpace.basisFun_inner,splitOperator_apply]
    simp only [EuclideanSpace.basisFun_apply,EuclideanSpace.single,PiLp.single_apply]
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    change T ((assignmentEquiv D S).symm (r,c)) = T a
    simp [r,c]
  rw [he] at h
  simpa using h
end AcceleratedLogConcave.Tensor
