import AcceleratedLogConcave.Numerics.AngleGaussianPhase
import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoordinates

/-! Exact rotation orbit in the phase engine's Euclidean coordinates. -/
noncomputable section
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Numerics.CenterMeanSecondJetSource
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def rotationOrbit (q : ℝ) (z : EP) (t : ℝ) : EP :=
  phaseCoordinateEquiv.symm (WithLp.toLp 2
    (AngleGaussianPhase.phase q t (phaseCoordinateEquiv z).ofLp))

def rotationVelocity (z : EP) : EP :=
  phaseCoordinateEquiv.symm (WithLp.toLp 2 (phaseMomentum z,-phasePosition z))

theorem hasDerivAt_rotationOrbit (q : ℝ) (z : EP) (t : ℝ) :
    HasDerivAt (rotationOrbit q z) (q⁻¹ • rotationVelocity (rotationOrbit q z t)) t := by
  have hp := (AngleGaussianPhase.hasDerivAt_phase_fst q t (phaseCoordinateEquiv z).ofLp).prodMk
    (AngleGaussianPhase.hasDerivAt_phase_snd q t (phaseCoordinateEquiv z).ofLp)
  have hl := ((WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.hasFDerivAt).comp_hasDerivAt t hp
  have h := phaseCoordinateEquiv.symm.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t hl
  convert h using 1
  · funext u
    rfl
  · simp only [rotationVelocity,rotationOrbit,phasePosition,phaseMomentum,
      LinearIsometryEquiv.apply_symm_apply,← map_smul]
    apply congrArg (fun p : WithLp 2 (E × E) => (phaseCoordinateEquiv.symm p : EP))
    apply congrArg (WithLp.toLp 2)
    apply Prod.ext <;> simp [neg_smul,smul_neg]

theorem rotationOrbit_zero (q : ℝ) (z : EP) : rotationOrbit q z 0 = z := by
  simp [rotationOrbit,AngleGaussianPhase.phase_zero]
end AcceleratedLogConcave.Analysis.AnglePhase
