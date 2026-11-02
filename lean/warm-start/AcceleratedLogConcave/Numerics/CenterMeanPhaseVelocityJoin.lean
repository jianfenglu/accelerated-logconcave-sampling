import AcceleratedLogConcave.Numerics.CenterMeanPhasePositionColumn
import AcceleratedLogConcave.Numerics.CenterMeanPhaseOrbit

/-! Exact normalized generator matching for the actual centering ODE.
The zero-curvature case must be handled separately before taking a nonzero scale. -/
noncomputable section
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.SkewCoordinateGenerator
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "ep" => EuclideanSpace.basisFun (Fin (D+D)) ℝ

private theorem velocity_coordinate (B : Fin (D+D) → Fin (D+D) → EP → ℝ)
    (H : EP → ℝ) (z : EP) (i : Fin (D+D)) :
    velocity ep B H z i = column ep B H z i := by
  simp [velocity,EuclideanSpace.basisFun_apply,Pi.single_apply]

private theorem phaseVelocity_position (d : Data (Fin D)) (s : ℝ) (z : EP) (i : Fin D) :
    phaseVelocity d s z (finSumFinEquiv (.inl i)) =
      -s⁻¹ * K d (phasePosition z) (phaseMomentum z) i := by
  rw [← phasePosition_apply]
  simp [phasePosition,phaseVelocity]

private theorem phaseVelocity_momentum (d : Data (Fin D)) (s : ℝ) (z : EP) (i : Fin D) :
    phaseVelocity d s z (finSumFinEquiv (.inr i)) =
      s⁻¹ * (M d (phasePosition z) - meanOffset d) i := by
  rw [← phaseMomentum_apply]
  simp [phaseMomentum,phaseVelocity]

theorem phaseVelocity_eq_normalized_generator (d : Data (Fin D)) (ellScale s : ℝ)
    (hscale : ellScale ≠ 0) (hs : s ≠ 0) (z : EP) :
    phaseVelocity d s z = (ellScale/s) •
      velocity ep (phaseTransportEntry d ellScale) (phasePotential d) z := by
  ext i
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i =>
    rw [PiLp.smul_apply,smul_eq_mul,velocity_coordinate,phase_column_position,
      phaseVelocity_position,EuclideanSpace.basisFun_inner]
    field_simp [hscale,hs]
  | inr i =>
    rw [PiLp.smul_apply,smul_eq_mul,velocity_coordinate,phase_column_momentum,
      phaseVelocity_momentum,EuclideanSpace.inner_basisFun_real]
    field_simp [hscale,hs]

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
