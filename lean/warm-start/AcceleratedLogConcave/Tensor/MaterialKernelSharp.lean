import AcceleratedLogConcave.Tensor.NetworkExpressionRms
import AcceleratedLogConcave.Tensor.MaterialRmsBudget

noncomputable section
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Analysis.PositiveVarianceSlab
open Tensor.ActualCoefficientIntegrability MeasureTheory Set

/-- Original-data kernel component at the exact Regularity derivative order.
The remaining six Regularity components are not asserted here. -/
theorem smoothKernel_regularity_bound {D m : ℕ} (d : MeanFlowLp.Data (Fin D) m) :
    ∀ j, ∀ t ∈ Icc (0:ℝ) (backwardEnd d.G.R),
      ‖iteratedDeriv (m+2) (smoothKernel d j) t‖ ≤
        materialKernelDerivativeBudget d (m+2) / (1-t^2)^(m+2) := by
  apply smoothKernel_regularity_bound_of_expressionRMS d
  intro t ht e he
  have hi := source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht
  exact Tensor.Ordered.Graph.expression_integral_norm_sq_le
    (KernelFlowLp.smoothData (kernelData d)) (kernelData d).hsmall e he
    ⟨hi.1.le,hi.2.le⟩

end AcceleratedLogConcave.Numerics.MeanResidualBridge
