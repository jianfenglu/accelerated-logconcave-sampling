import AcceleratedLogConcave.Analysis.ActualAngleOriginalDataReceiver
import AcceleratedLogConcave.Numerics.SmoothQuantitativeAssembly

/-! Adapter from the recovered actual-angle theorem to the unchanged explicit
receiver budget. Positive order is required, as in the source theorem. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SmoothQuantitativeAssembly
open MeanFlowLp
variable {D m : ℕ}

theorem angleBounds_original_data (d : Data (Fin D) m) (hm : 1 ≤ m) :
    AngleBounds d := by
  constructor
  · intro j k t _
    exact ((actionLp_contDiff_original_data d j k).of_le (by simp)).contDiffAt
  · intro j k t _
    have h := norm_iteratedDeriv_actionLp_le_original_data d j k (m-1) t
    simpa only [Nat.sub_add_cancel hm, angleBudget, auxiliaryConstant,
      show (2:ℝ)*128=256 by norm_num] using h

end AcceleratedLogConcave.Numerics.SmoothQuantitativeAssembly
