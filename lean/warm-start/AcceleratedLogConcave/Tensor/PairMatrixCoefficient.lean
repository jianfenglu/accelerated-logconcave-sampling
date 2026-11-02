import AcceleratedLogConcave.Tensor.HessianCoefficientBudget
import AcceleratedLogConcave.Tensor.SpatialSlotAction

/-! An actual matrix coefficient tensor on two named slots. Every proper split
has at most its Euclidean operator norm, regardless of slot orientation. -/
noncomputable section
namespace AcceleratedLogConcave.Tensor
open ActualCoefficientIntegrability
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] {D : ℕ}

def pairMatrixCoefficient (p q : Slot) (A : Matrix (Fin D) (Fin D) ℝ) : Coeff Slot D :=
  WithLp.toLp 2 (fun a => A (a p) (a q))

theorem pairMatrixCoefficient_eq_slotAction (p q : Slot) (hpq : p ≠ q)
    (A : Matrix (Fin D) (Fin D) ℝ) :
    pairMatrixCoefficient p q A = spatialSlotAction p A
      (WithLp.toLp 2 (fun a : Slot → Fin D =>
        inner ℝ (coordinateDirection D (a p)) (coordinateDirection D (a q)))) := by
  ext a
  simp [pairMatrixCoefficient, spatialSlotAction, Ne.symm hpq,
    coordinateDirection, EuclideanSpace.inner_single_left, PiLp.single_apply]

theorem pairMatrixCoefficient_splitNorm_le (hcard : Fintype.card Slot = 2)
    (p q : Slot) (hpq : p ≠ q) (A : Matrix (Fin D) (Fin D) ℝ)
    (S : Finset Slot) (hS : NontrivialSplit S) :
    splitNorm D S (pairMatrixCoefficient p q A) ≤ ‖matrixCLMEquiv A‖ := by
  rw [pairMatrixCoefficient_eq_slotAction p q hpq]
  exact (spatialSlotAction_splitNorm_le S p A _).trans
    ((mul_le_mul_of_nonneg_left (pairIdentity_splitNorm_le hcard p q hpq S hS)
      (norm_nonneg _)).trans_eq (mul_one _))

end AcceleratedLogConcave.Tensor
