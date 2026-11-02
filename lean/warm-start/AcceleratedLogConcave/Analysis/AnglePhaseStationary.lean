import AcceleratedLogConcave.Analysis.GaussianPhaseProduct
import AcceleratedLogConcave.Analysis.AnglePhaseOrbit

/-! Full joint Gaussian stationarity in the actual phase coordinates, before
any conditioning on the independent midpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Numerics.CenterMeanSecondJetSource
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def phaseMeasurableEquiv : EP ≃ᵐ E × E :=
  phaseCoordinateEquiv.toHomeomorph.toMeasurableEquiv.trans
    (MeasurableEquiv.toLp 2 (E × E)).symm

theorem phaseMeasurableEquiv_preserving :
    MeasurePreserving (phaseMeasurableEquiv (D := D)) (stdGaussian EP)
      ((stdGaussian E).prod (stdGaussian E)) := by
  have he : MeasurePreserving (phaseCoordinateEquiv (D := D))
      (stdGaussian EP) (stdGaussian (WithLp 2 (E × E))) :=
    ⟨phaseCoordinateEquiv.continuous.measurable,stdGaussian_map phaseCoordinateEquiv⟩
  have ht : MeasurePreserving (MeasurableEquiv.toLp 2 (E × E))
      ((stdGaussian E).prod (stdGaussian E)) (stdGaussian (WithLp 2 (E × E))) :=
    ⟨(MeasurableEquiv.toLp 2 (E × E)).measurable,prod_stdGaussian_toLp⟩
  exact (ht.symm (MeasurableEquiv.toLp 2 (E × E))).comp he

theorem rotationOrbit_preserving (q t : ℝ) :
    MeasurePreserving (fun z : EP => rotationOrbit q z t) (stdGaussian EP) (stdGaussian EP) := by
  have he := phaseMeasurableEquiv_preserving (D := D)
  have hh := (he.symm phaseMeasurableEquiv).comp
    ((AngleGaussianPhase.phase_preserving q t).comp he)
  convert hh using 1
  rfl
end AcceleratedLogConcave.Analysis.AnglePhase
