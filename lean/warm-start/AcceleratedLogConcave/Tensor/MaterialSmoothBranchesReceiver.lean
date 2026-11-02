import AcceleratedLogConcave.Numerics.SmoothAllReceiver
import AcceleratedLogConcave.Tensor.MaterialBackwardKernelReceiver

/-! The already-proved backward and kernel quantitative suppliers apply to
the same all-four-field receiver. No other budget is asserted. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Analysis.PositiveVarianceSlab
variable {D m : ℕ}

theorem smoothBranches_backward_cellRegularity (d : Data (Fin D) m) (j : Fin m) :
    AffineResidual.CellRegularity d.G.backward m
      ((curvesWithSmoothBranches d).backwardMean d.G
        (primitiveLp (primitiveData d) (seedMeasure d)) 0 d.r j)
      (materialBackwardCellBudget d) := by
  rw [smoothBranches_backwardMean_eq]
  exact replacement_backwardMean_cellRegularity d _ (primitiveLp_spec _ _) j

theorem smoothBranches_kernel_bound (d : Data (Fin D) m) :
    ∀ j, ∀ t ∈ Icc (0 : ℝ) (backwardEnd d.G.R),
      ‖iteratedDeriv (m + 2) ((curvesWithSmoothBranches d).kernel j) t‖ ≤
        materialKernelDerivativeBudget d (m + 2) / (1 - t^2)^(m + 2) :=
  smoothKernel_regularity_bound d

theorem smoothBranches_kernel_contDiffOn (d : Data (Fin D) m) (j : Fin m) (n : ℕ) :
    ContDiffOn ℝ n ((curvesWithSmoothBranches d).kernel j)
      (Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :=
  contDiffOn_smoothKernel d j n

theorem smoothBranches_kernel_deriv_zero (d : Data (Fin D) m) (j : Fin m) :
    deriv ((curvesWithSmoothBranches d).kernel j) 0 = 0 :=
  backwardKernel_kernel_deriv_zero d j

theorem smoothBranches_kernel_terminal_zero (d : Data (Fin D) m) (j : Fin m) :
    (curvesWithSmoothBranches d).kernel j (backwardEnd d.G.R) = 0 :=
  backwardKernel_kernel_terminal_zero d j

theorem smoothBranches_kernel_budget_nonneg (d : Data (Fin D) m) :
    0 ≤ materialKernelDerivativeBudget d (m + 2) :=
  materialKernelDerivativeBudget_nonneg d (m + 2)

end AcceleratedLogConcave.Numerics.MeanResidualBridge
