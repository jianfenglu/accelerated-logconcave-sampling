import AcceleratedLogConcave.Oracle.MeanOriginalBounds
import AcceleratedLogConcave.Numerics.SmoothInitialDisplacementBound

/-! The actual initializer's intrinsic common-seed displacement budget.
Unlike the coarse one-step residual estimate, this retains the physical
radius outside the original-data row coefficient. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.MeanSharpOriginalBounds
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.MeanCollocationLp
variable {D m : ℕ} (d : MeanFlowLp.Data (Fin D) m)

def initializerBudget : ℝ := d.r*‖SmoothInitialDisplacementBound.rowCoefficient d‖

theorem initializerBudget_nonneg : 0 ≤ initializerBudget d := mul_nonneg d.hr.le (norm_nonneg _)

/-- Same original initializer error, sharper proved bound; no extra
regularity, accuracy or moment assumption. -/
theorem initializer_norm_le (i : d.G.MeanNode) :
    ‖(MeanOriginalBounds.initializer_memLp d i).toLp (MeanOriginalBounds.initializerError d i)‖≤
      initializerBudget d := by
  unfold MeanOriginalBounds.initializerError
  rw [AffineResidual.toLp_eq_of_ae _ (raw_error_ae d 0 i)]
  exact (norm_le_pi_norm (iterate d 0-reference d) i).trans
    (SmoothInitialDisplacementBound.initialError_le_data d)

end AcceleratedLogConcave.Oracle.MeanSharpOriginalBounds
