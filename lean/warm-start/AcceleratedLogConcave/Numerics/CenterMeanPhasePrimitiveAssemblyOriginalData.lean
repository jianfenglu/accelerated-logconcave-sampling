import AcceleratedLogConcave.Numerics.CenterMeanTransportOriginalData
import AcceleratedLogConcave.Numerics.CenterMeanPhaseHessianBudget
import AcceleratedLogConcave.Numerics.CenterMeanPhaseObservableBudget
import AcceleratedLogConcave.Numerics.CenterMeanPhaseProjectionBudget

/-! NEW reconstruction, not recovered historical PrimitiveAssembly.
SOURCE ONLY until isolated compilation and axiom audit succeed.
Original-data primitive closure only: no claim of full Regularity or recovery
of the absent historical centerMeanLp_center_fields_from_primitives receiver. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.Ordered.Graph
variable {D : ℕ}

/-- Every literal coefficient jet and every positive score jet, supplied from
original data and the accepted actual-K half budget. The final constant is 128
only because that is the accepted K supplier's threshold, not an extra premise. -/
theorem centerPhasePrimitiveBudgets_original_data (d : Data (Fin D))
    {c : ℝ} (hc : 128 ≤ c) :
    PhasePrimitiveBudgets (phaseCoefficients d (d.r*d.ell) (d.r*d.ell))
      (phasePotential d) c (Real.sqrt (conditionalVariance d.b)) := by
  have hc4 : 4 ≤ c := by linarith
  constructor
  · intro a n z S hS
    cases a with
    | transport =>
      simpa [PhaseExpression.signature, conditionalVariance] using
        phaseTransportJet_original_data_budget_all d hc n z S hS
    | scoreHessian =>
      simpa [PhaseExpression.signature] using
        phaseHessianJet_budget d (d.r*d.ell) (d.r*d.ell) hc4 n z S hS
    | observableGradient =>
      simpa [PhaseExpression.signature] using
        phaseObservableJet_budget d (d.r*d.ell) (by linarith : 2 ≤ c) n z S hS
    | positionProjection =>
      simpa [PhaseExpression.signature] using
        phaseProjectionJet_budget d (d.r*d.ell) (d.r*d.ell) hc4 n z S hS
  · intro j hj z S hS
    exact phaseScoreJet_budget d hc4 j hj z S hS

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource

namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional Tensor Tensor.Ordered.Graph CenterMeanSecondJetSource
variable {D m : ℕ}

/-- Exact common-seed normalization and exact G.R; this closes primitive data,
not the absent endpoint receiver or the full MeanFlowLp.Regularity record. -/
theorem centerPhasePrimitiveBudgets_commonSeed (d : Data (Fin D) m)
    {c : ℝ} (hc : 128 ≤ c) :
    PhasePrimitiveBudgets
      (phaseCoefficients (kernelData d) ((kernelData d).r*(kernelData d).ell)
        ((kernelData d).r*(kernelData d).ell))
      (phasePotential (kernelData d)) c d.G.R := by
  have hR : Real.sqrt (conditionalVariance (kernelData d).b) = d.G.R := by
    simpa only [kernelData, conditionalVariance] using sqrt_backward_variance d
  rw [← hR]
  exact centerPhasePrimitiveBudgets_original_data (kernelData d) hc

end AcceleratedLogConcave.Numerics.MeanFlowLp
