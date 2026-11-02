import AcceleratedLogConcave.Numerics.SmoothAllReceiver
import AcceleratedLogConcave.Numerics.SmoothConditionalCell

/-! The explicit conditional cell supplier on the actual receiver carrying
all smooth branch fields. This is only a whole-function equality wrapper;
it adds no analytic estimate, mesh hypothesis or full Regularity claim. -/
noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

theorem smoothBranches_conditionalMean_cellRegularity_explicit (d : MeanFlowLp.Data ι m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) :
    AffineResidual.CellRegularity (d.G.conditional ρ) m
      ((curvesWithSmoothBranches d).conditionalMean d.G U 0 d.r j ρ)
      (conditionalCellBudget d ρ) := by
  rw [smoothBranches_conditionalMean_eq d U]
  exact conditionalMean_cellRegularity_explicit d U hu j ρ

end AcceleratedLogConcave.Numerics.MeanResidualBridge
