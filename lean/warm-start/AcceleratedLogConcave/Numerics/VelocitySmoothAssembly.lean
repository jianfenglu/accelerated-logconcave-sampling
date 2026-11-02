import AcceleratedLogConcave.Numerics.VelocityOriginalData
import AcceleratedLogConcave.Numerics.VelocityBudgetAlgebra
import AcceleratedLogConcave.Numerics.SmoothQuantitativeAssembly

/-!

-/
noncomputable section
namespace AcceleratedLogConcave.Numerics.SmoothQuantitativeAssembly
open MeanFlowLp CenterMeanSecondJetSource
variable {D m : ℕ}

theorem velocitySourceBudget_eq_velocityBudget (d : Data (Fin D) m) :
    velocitySourceBudget d ((kernelData d).r*(kernelData d).ell)
      auxiliaryConstant d.G.R m = velocityBudget d := by
  unfold velocitySourceBudget velocityJetEnergyScale velocityBudget
  exact velocity_budget_algebra D m (d.r*d.ell) (d.sigma/2)
    (Tensor.AdjointReduction.PhaseBudget.Q auxiliaryConstant (5*(m+1)+1)) d.G.R
    (mul_nonneg d.hr.le d.hell) (half_pos d.hsigma)
    (Tensor.AdjointReduction.PhaseBudget.Q_nonneg (by norm_num [auxiliaryConstant]) _) d.G.R_pos

theorem velocityBounds_original_data (d : Data (Fin D) m) : VelocityBounds d := by
  constructor
  · intro t _
    exact ((velocityLp_contDiff_original_data d).of_le (by simp)).contDiffAt
  · intro t _
    rw [← velocitySourceBudget_eq_velocityBudget d]
    exact norm_iteratedDeriv_velocityLp_le_original_data d
      (by norm_num [auxiliaryConstant]) m t

end AcceleratedLogConcave.Numerics.SmoothQuantitativeAssembly
