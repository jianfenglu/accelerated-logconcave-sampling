import AcceleratedLogConcave.Analysis.AnglePhaseSourceJet
import AcceleratedLogConcave.Tensor.PhaseVectorSourceJets

/-! One vector source, with exactly zero unused momentum-output coordinates. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Numerics.CenterMeanSecondJetSource Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def displacementVector (T : E → E) (M : E) (q a : ℝ) (z : EP) : EP :=
  a⁻¹ • phaseCoordinateEquiv.symm (WithLp.toLp 2
    (T (M+q • phasePosition z) - (M+q • phasePosition z), (0 : E)))

theorem displacementVector_apply (T : E → E) (M : E) (q a : ℝ)
    (z : EP) (i : Fin (D+D)) :
    displacementVector T M q a z i = displacementCoordinate T M q a i z := by
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i =>
    simp only [displacementCoordinate,Equiv.symm_apply_apply]
    rw [← phasePosition_apply]
    simp [displacementVector,phasePosition,EuclideanSpace.inner_single_left]
  | inr i =>
    simp only [displacementCoordinate,Equiv.symm_apply_apply]
    rw [← phaseMomentum_apply]
    simp [displacementVector,phaseMomentum]

theorem norm_displacementVector (T : E → E) (M : E) (q a : ℝ) (z : EP) :
    ‖displacementVector T M q a z‖ =
      ‖a⁻¹‖ * ‖T (M+q • phasePosition z) - (M+q • phasePosition z)‖ := by
  simp [displacementVector,norm_smul,WithLp.norm_toLp_fst]

theorem iteratedDeriv_displacementVector (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a : ℝ) (z : EP) (k : ℕ) :
    iteratedDeriv (k+1) (fun t => displacementVector T M q a (rotationOrbit q z t)) =
      fun t => (q⁻¹)^(k+1) • vectorSection (angleCoefficients T M q a)
        gaussianPotential (jet F k) (rotationOrbit q z t) := by
  apply iteratedDeriv_sourceVector_eq_jet (angleCoefficients T M q a) gaussianPotential
    (displacementVector T M q a) (smooth_angleCoefficients T hT M q a) gaussianPotential_smooth
  · intro i
    simpa only [displacementVector_apply] using smooth_displacementCoordinate T hT M q a i
  · exact angleCoefficients_skew T M q a
  · intro i j
    simpa only [displacementVector_apply] using angleCoefficients_gradient T M q a i j
  · intro t
    have h := hasDerivAt_rotationOrbit q z t
    rw [rotationVelocity_eq_generator] at h
    exact h
end AcceleratedLogConcave.Analysis.AnglePhase
