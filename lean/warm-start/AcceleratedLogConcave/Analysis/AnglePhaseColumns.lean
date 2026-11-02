import AcceleratedLogConcave.Analysis.GaussianPhaseEnvironment
import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoordinates
import AcceleratedLogConcave.Tensor.SkewCoordinateGenerator

/-! Literal weighted columns of the constant skew Gaussian angle generator.
The sign is chosen so that position'=momentum and momentum'=-position. -/
noncomputable section
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.AdjointReduction Tensor.SkewCoordinateGenerator
open Numerics.CenterMeanSecondJetSource Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def rotationEntry (i j : Fin (D+D)) (_z : EP) : ℝ :=
  skewBlockEntry (-ContinuousLinearMap.id ℝ E)
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

theorem rotationEntry_skew (z : EP) (i j : Fin (D+D)) :
    rotationEntry i j z = -rotationEntry j i z :=
  skewBlockEntry_skew _ _ _

theorem dir_rotationEntry (v : EP) (i j : Fin (D+D)) :
    dir v (rotationEntry i j) = fun _ => 0 := by
  funext x
  change fderiv ℝ (fun _ : EP => skewBlockEntry (-ContinuousLinearMap.id ℝ E)
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) x v = 0
  simp only [fderiv_const_apply,zero_apply]

theorem dir_coordinate_gaussian (i : Fin (D+D)) (z : EP) :
    dir (coordinateDirection (D+D) i) gaussianPotential z = z i := by
  have he : coordinateDirection (D+D) i = EuclideanSpace.basisFun (Fin (D+D)) ℝ i := by
    simp [EuclideanSpace.basisFun_apply,coordinateDirection,EuclideanSpace.single]
  rw [he]
  simp [dir,gaussianPotential_fderiv,EuclideanSpace.inner_single_right]

private theorem sum_phase_indices (f : Fin (D+D) → ℝ) :
    (∑ i, f i) = (∑ i, f (finSumFinEquiv (.inl i))) +
      ∑ i, f (finSumFinEquiv (.inr i)) := by
  rw [← finSumFinEquiv.sum_comp f,Fintype.sum_sum_type]

theorem rotation_column_position (z : EP) (j : Fin D) :
    column (coordinateDirection (D+D)) rotationEntry gaussianPotential z
      (finSumFinEquiv (.inl j)) = phaseMomentum z j := by
  unfold column
  simp_rw [dir_rotationEntry,dir_coordinate_gaussian]
  rw [sum_phase_indices]
  simp only [rotationEntry,Equiv.symm_apply_apply,skewBlockEntry]
  simp [EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left,PiLp.single_apply,
    phaseMomentum_apply]

theorem rotation_column_momentum (z : EP) (j : Fin D) :
    column (coordinateDirection (D+D)) rotationEntry gaussianPotential z
      (finSumFinEquiv (.inr j)) = -phasePosition z j := by
  unfold column
  simp_rw [dir_rotationEntry,dir_coordinate_gaussian]
  rw [sum_phase_indices]
  simp only [rotationEntry,Equiv.symm_apply_apply,skewBlockEntry]
  simp [EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left,PiLp.single_apply,
    phasePosition_apply]
end AcceleratedLogConcave.Analysis.AnglePhase
