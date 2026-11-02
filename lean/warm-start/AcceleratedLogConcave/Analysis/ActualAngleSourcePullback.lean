import AcceleratedLogConcave.Analysis.ActualAngleJointLaw
import AcceleratedLogConcave.Analysis.AngleDisplacementLp
import AcceleratedLogConcave.Analysis.ActualAnglePhysicalBudgets

/-! New literal pullback, before any L² quotient identification. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional Analysis.AnglePhase CenterMeanSecondJetSource AffineGraph AffineGraph.MeanGeometry
variable {D m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def angleEmbed : E →L[ℝ] EP :=
  phaseCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ E E))

theorem angleEmbed_apply (v : E) : angleEmbed v =
    phaseCoordinateEquiv.symm (WithLp.toLp 2 (v,(0:E))) := rfl

theorem norm_angleEmbed (v : E) : ‖angleEmbed v‖ = ‖v‖ := by
  simp [angleEmbed_apply,WithLp.norm_toLp_fst]

theorem angleObservation_rotation (d : Data (Fin D) m) (k : d.G.Kernel)
    (p : (E × E) × E) (t : ℝ) :
    (angleObservationCoordinates d k p).1 + d.G.rotationScale k •
      phasePosition (rotationOrbit (d.G.rotationScale k) (angleObservationCoordinates d k p).2 t) =
        rotationOfObservation d k t p.1.1 p.1.2 p.2 := by
  have hq := (d.G.rotationScale_pos k).ne'
  simp only [angleObservationCoordinates,rotationOrbit,phaseMeasurableEquiv,
    MeasurableEquiv.trans_symm,MeasurableEquiv.coe_trans,Function.comp_apply,
    phasePosition,Analysis.AngleGaussianPhase.phase,Kinetic.gaussianRotate]
  simp only [Homeomorph.toMeasurableEquiv_symm_coe, MeasurableEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply, WithLp.ofLp_toLp]
  change _ + d.G.rotationScale k •
    (Real.cos (t/d.G.rotationScale k) •
      (phaseCoordinateEquiv (phaseCoordinateEquiv.symm (WithLp.toLp 2
        ((d.G.rotationScale k)⁻¹ • (p.1.1 - (d.G.rho k/(1+(d.G.rho k)^2)) •
          (p.1.2+d.G.rho k • p.1.1)),p.2)))).ofLp.1 +
      Real.sin (t/d.G.rotationScale k) •
      (phaseCoordinateEquiv (phaseCoordinateEquiv.symm (WithLp.toLp 2
        ((d.G.rotationScale k)⁻¹ • (p.1.1 - (d.G.rho k/(1+(d.G.rho k)^2)) •
          (p.1.2+d.G.rho k • p.1.1)),p.2)))).ofLp.2) = _
  simp only [LinearIsometryEquiv.apply_symm_apply]
  unfold rotationOfObservation
  simp only [smul_add,smul_smul]
  rw [show d.G.rotationScale k * (Real.cos (t/d.G.rotationScale k) *
    (d.G.rotationScale k)⁻¹) = Real.cos (t/d.G.rotationScale k) by field_simp]
  module

theorem parameterDisplacement_actual_seed (d : Data (Fin D) m) (j : Fin m)
    (k : d.G.Kernel) (a t : ℝ) (w : Seed d) :
    parameterDisplacement (angleEndpoint d k) (d.G.rotationScale k) a
      (parameterRotation (d.G.rotationScale k) t (angleSeedCoordinates d j k w)) =
        a⁻¹ • angleEmbed (action d j k t w) := by
  have hr : (angleSeedCoordinates d j k w).1 + d.G.rotationScale k •
      phasePosition (rotationOrbit (d.G.rotationScale k) (angleSeedCoordinates d j k w).2 t) =
      rotation d j k t w := by
    rw [angleSeedCoordinates,angleObservation_rotation,← rotation_eq_observation]
  dsimp only [parameterDisplacement,parameterRotation,displacementVector]
  rw [hr,angleEmbed_apply]
  rfl
end AcceleratedLogConcave.Numerics.MeanFlowLp
