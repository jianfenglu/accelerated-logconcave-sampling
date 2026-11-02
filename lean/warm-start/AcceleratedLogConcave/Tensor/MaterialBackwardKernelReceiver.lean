import AcceleratedLogConcave.Numerics.SmoothBackwardKernelReplacement
import AcceleratedLogConcave.Tensor.MaterialBackwardCell
import AcceleratedLogConcave.Tensor.MaterialKernelSharp

/-! Both original-data supplier bounds apply to the same equation-preserving
receiver. No new regularity assumption or full Regularity assertion is made. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Analysis.PositiveVarianceSlab
variable {D m : ℕ}

theorem backwardKernel_backward_cellRegularity (d : Data (Fin D) m) (j : Fin m) :
    AffineResidual.CellRegularity d.G.backward m
      ((curvesWithBackwardKernel d).backwardMean d.G
        (primitiveLp (primitiveData d) (seedMeasure d)) 0 d.r j)
      (materialBackwardCellBudget d) :=
  replacement_backwardMean_cellRegularity d _ (primitiveLp_spec _ _) j

theorem backwardKernel_kernel_bound (d : Data (Fin D) m) :
    ∀ j, ∀ t ∈ Icc (0 : ℝ) (backwardEnd d.G.R),
      ‖iteratedDeriv (m + 2) ((curvesWithBackwardKernel d).kernel j) t‖ ≤
        materialKernelDerivativeBudget d (m + 2) / (1 - t^2)^(m + 2) :=
  smoothKernel_regularity_bound d

theorem backwardKernel_kernel_contDiffOn (d : Data (Fin D) m) (j : Fin m) (n : ℕ) :
    ContDiffOn ℝ n ((curvesWithBackwardKernel d).kernel j)
      (Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :=
  contDiffOn_smoothKernel d j n

theorem backwardKernel_kernel_deriv_zero (d : Data (Fin D) m) (j : Fin m) :
    deriv ((curvesWithBackwardKernel d).kernel j) 0 = 0 := by
  apply kernel_deriv_zero_of_agreement d (smoothKernel_agreement d) j
  have hzero : (0 : ℝ) ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R)) :=
    source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one
      ⟨le_rfl, d.G.backwardEnd_pos.le⟩
  exact ((contDiffOn_smoothKernel d j 1).contDiffAt
    (isOpen_Ioo.mem_nhds hzero)).differentiableAt (by norm_num)

theorem backwardKernel_kernel_terminal_zero (d : Data (Fin D) m) (j : Fin m) :
    (curvesWithBackwardKernel d).kernel j (backwardEnd d.G.R) = 0 :=
  kernel_terminal_zero_of_agreement d (smoothKernel_agreement d) j

theorem backwardKernel_kernel_budget_nonneg (d : Data (Fin D) m) :
    0 ≤ materialKernelDerivativeBudget d (m + 2) :=
  materialKernelDerivativeBudget_nonneg d (m + 2)

end AcceleratedLogConcave.Numerics.MeanResidualBridge
