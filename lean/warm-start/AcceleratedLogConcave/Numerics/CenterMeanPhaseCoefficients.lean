import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoordinates
import AcceleratedLogConcave.Tensor.PhaseSourceJetInduction

/-! Literal normalized primitive environment for the source phase. Definitions
of coefficients are not quantitative budget hypotheses. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.PhaseExpression Tensor.CoordinateReduction
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def phaseEmbedPosition : E →L[ℝ] EP :=
  phaseCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ E E))

@[simp] theorem phaseEmbedPosition_apply (y : E) :
    phaseEmbedPosition y = phaseCoordinateEquiv.symm (WithLp.toLp 2 (y,0)) := rfl

@[simp] theorem norm_phaseEmbedPosition (y : E) : ‖phaseEmbedPosition y‖ = ‖y‖ := by
  rw [phaseEmbedPosition_apply,LinearIsometryEquiv.norm_map,WithLp.norm_toLp_fst]

def phaseObservable (d : Data (Fin D)) (a : ℝ) (z : EP) : EP :=
  a⁻¹ • phaseEmbedPosition (M d (phasePosition z) - meanOffset d)

def phasePaddedPosition (z : EP) : EP := phaseEmbedPosition (phasePosition z)

theorem smooth_phaseObservable (d : Data (Fin D)) (a : ℝ) :
    ContDiff ℝ ∞ (phaseObservable d a) := by
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : EP => a⁻¹)).smul (phaseEmbedPosition.contDiff.comp
    (((smooth_M d).comp smooth_phasePosition).sub contDiff_const))

theorem smooth_phasePaddedPosition : ContDiff ℝ ∞ (phasePaddedPosition (D := D)) :=
  phaseEmbedPosition.contDiff.comp smooth_phasePosition

def phaseCoefficients (d : Data (Fin D)) (ellScale a : ℝ) : CoefficientEnvironment signature (D+D)
  | .transport, z => WithLp.toLp 2 (fun (v : Fin 2 → Fin (D+D)) => phaseTransportEntry d ellScale (v 0) (v 1) z)
  | .scoreHessian, z => WithLp.toLp 2 (fun (v : Fin 2 → Fin (D+D)) => fderiv ℝ (fderiv ℝ (phasePotential d)) z
      (coordinateDirection (D+D) (v 0)) (coordinateDirection (D+D) (v 1)))
  | .observableGradient, z => WithLp.toLp 2 (fun (v : Fin 2 → Fin (D+D)) =>
      fderiv ℝ (fun x => phaseObservable d a x (v 0)) z (coordinateDirection (D+D) (v 1)))
  | .positionProjection, z => WithLp.toLp 2 (fun (v : Fin 2 → Fin (D+D)) =>
      fderiv ℝ (fun x => phasePaddedPosition x (v 0)) z (coordinateDirection (D+D) (v 1)))

theorem phaseCoefficients_transport (d : Data (Fin D)) (ellScale a : ℝ)
    (i j : Fin (D+D)) :
    PhaseGeneratorIdentification.transportEntry (phaseCoefficients d ellScale a) i j =
      phaseTransportEntry d ellScale i j := rfl

theorem phaseCoefficients_observable_gradient (d : Data (Fin D)) (ellScale a : ℝ)
    (i j : Fin (D+D)) :
    sectionValue (phaseCoefficients d ellScale a) (phasePotential d) F ![i,j] =
      AdjointReduction.dir (coordinateDirection (D+D) j) (fun z => phaseObservable d a z i) := rfl

theorem phaseCoefficients_position_gradient (d : Data (Fin D)) (ellScale a : ℝ)
    (i j : Fin (D+D)) :
    sectionValue (phaseCoefficients d ellScale a) (phasePotential d) P ![i,j] =
      AdjointReduction.dir (coordinateDirection (D+D) j) (fun z => phasePaddedPosition z i) := rfl

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
