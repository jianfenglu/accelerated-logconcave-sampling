import AcceleratedLogConcave.Numerics.CenterMeanPhaseMoments
import AcceleratedLogConcave.Numerics.CenterMeanPhaseScorePolynomial

/-! NEW factored reconstruction: reuse the accepted score-polynomial declaration
rather than defining it twice. The environment fields are discharged by the
actual source law and proved marginal moments, not supplied as hypotheses.
Source-only; compilation and declaration audit are pending. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open CenteringFlowLp
variable {D : ℕ}

/-- Genuine Gibbs environment for the original phase seed law. -/
def actualPhaseGibbsEnvironment (d : Data (Fin D)) :
    Tensor.Ordered.Graph.SmoothGibbsEnvironment (D+D) where
  base := phaseHaar
  haar := inferInstance
  potential := phasePotential d
  smooth := smooth_phasePotential d
  partition_integrable := phasePartition_integrable d
  finite := by rw [← phaseSeedLaw_eq_tilted d]; infer_instance
  moments := by rw [← phaseSeedLaw_eq_tilted d]; exact phaseSeedLaw_hasMoments d
  score_jets := phase_score_polynomialJets d

theorem actualPhaseGibbsEnvironment_law (d : Data (Fin D)) :
    (actualPhaseGibbsEnvironment d).law = phaseSeedLaw d :=
  (phaseSeedLaw_eq_tilted d).symm

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
