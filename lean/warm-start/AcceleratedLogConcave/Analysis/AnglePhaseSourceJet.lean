import AcceleratedLogConcave.Analysis.AnglePhaseCoefficients
import AcceleratedLogConcave.Analysis.AnglePhaseOrbit

/-! Actual angle derivatives equal the connected phase-expression jets.
No derivative estimate or assumed stationary moment appears in this identity. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.AdjointReduction Tensor.CoordinateReduction Tensor.PhaseExpression
open Tensor.PhaseGeneratorIdentification Tensor.SkewCoordinateGenerator
open Numerics.CenterMeanSecondJetSource Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

private theorem generator_velocity_coordinate (z : EP) (i : Fin (D+D)) :
    velocity (coordinateDirection (D+D)) rotationEntry gaussianPotential z i =
      column (coordinateDirection (D+D)) rotationEntry gaussianPotential z i := by
  simp [velocity,coordinateDirection,Pi.single_apply]

theorem rotationVelocity_eq_generator (z : EP) :
    rotationVelocity z = velocity (coordinateDirection (D+D)) rotationEntry gaussianPotential z := by
  ext i
  rw [generator_velocity_coordinate]
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i =>
    rw [rotation_column_position,← phasePosition_apply]
    simp [phasePosition,rotationVelocity]
  | inr i =>
    rw [rotation_column_momentum,← phaseMomentum_apply]
    simp [phaseMomentum,rotationVelocity]

theorem iteratedDeriv_displacement_coordinate (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a : ℝ) (z : EP) (i : Fin (D+D)) (k : ℕ) :
    iteratedDeriv (k+1) (fun t => displacementCoordinate T M q a i (rotationOrbit q z t)) =
      fun t => (q⁻¹)^(k+1) * sectionValue (angleCoefficients T M q a)
        gaussianPotential (jet F k) ![i] (rotationOrbit q z t) := by
  apply Tensor.PhaseSourceJetInduction.iteratedDeriv_eq_jet
    (angleCoefficients T M q a) gaussianPotential (displacementCoordinate T M q a i)
    (smooth_angleCoefficients T hT M q a) gaussianPotential_smooth
    (smooth_displacementCoordinate T hT M q a i)
    (angleCoefficients_skew T M q a) F i
    (angleCoefficients_gradient T M q a i) (rotationOrbit q z) (q⁻¹)
  intro t
  have h := hasDerivAt_rotationOrbit q z t
  rw [rotationVelocity_eq_generator] at h
  exact h
end AcceleratedLogConcave.Analysis.AnglePhase
