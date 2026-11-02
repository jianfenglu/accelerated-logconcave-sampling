import AcceleratedLogConcave.Kinetic.ReferenceFlow.PhysicalFlow
import AcceleratedLogConcave.Kinetic.ConditionalContraction.HamiltonianRows

/-! The strong core derivative is the actual Hamiltonian derivative, pulled
back by the same spatial flow used by the moving Poisson corrector. -/
noncomputable section
set_option maxHeartbeats 1600000
open Set Function MeasureTheory InnerProductSpace
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)

/-- The actual full backward-transported test in physical coordinates. -/
def physicalTransportTest (T : Icc a b) (φ : GaussianPhase E → ℝ) (t : ℝ) :=
  fun z => backwardTest F.ordered (physicalDrift_continuous F ell s n hsn)
    (physicalDrift_lipschitz F ell s n hsn) T φ (t,z)

 theorem physicalFrame_eq (t : ℝ) (ht : t ∈ Icc a b) (z : GaussianPhase E) :
    (spaceTimeForward F.ordered (physicalDrift_continuous F 0 s n hsn)
      (physicalDrift_lipschitz F 0 s n hsn) (t,z)).2 =
      ((F.flow ⟨t,ht⟩ z.1.1,z.1.2),z.2) := by
  unfold spaceTimeForward
  dsimp only
  rw [projIcc_of_mem _ ht]
  exact physicalFlow_zero_eq F s n hsn ⟨t,ht⟩ z

 theorem physicalMovingCore_derivative_eq (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (t : ℝ) (ht : t ∈ Ioo a b) (z : GaussianPhase E) :
    fderiv ℝ (physicalMovingCore F ell s n hsn T φ) (t,z) (1,0) =
      -ell * hamiltonianTestDerivative (F.potential t) s n
        (physicalTransportTest F ell s n hsn T φ t)
        ((F.flow ⟨t,ht.1.le,ht.2.le⟩ z.1.1,z.1.2),z.2) := by
  have he := movingFrameCore_derivative_eq F.ordered
    (physicalDrift_continuous F ell s n hsn) (physicalDrift_continuous F 0 s n hsn)
    (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_lipschitz F 0 s n hsn)
    (physicalDriftDerivative_continuous F ell s n hsn) (physicalDriftDerivative_continuous F 0 s n hsn)
    (physicalDrift_hasFDerivAt F ell s n hsn) (physicalDrift_hasFDerivAt F 0 s n hsn)
    T hφ t ht z
  rw [physicalPhaseDrift_difference, map_smul, smul_eq_mul] at he
  rw [hamiltonianTestDerivative_eq_fderiv, ← physicalFrame_eq F s n hsn t ⟨ht.1.le,ht.2.le⟩ z]
  exact he

end AcceleratedLogConcave.Kinetic
