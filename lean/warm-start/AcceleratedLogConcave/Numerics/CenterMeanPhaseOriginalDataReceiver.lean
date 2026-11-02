import AcceleratedLogConcave.Numerics.CenterMeanPhaseJetBudget
import AcceleratedLogConcave.Numerics.CenterMeanPhasePrimitiveAssemblyOriginalData
import AcceleratedLogConcave.Numerics.CenterMeanZeroCurvature

/-! NEW reconstruction: actual common-seed center L² bounds from original data.
The positive-scale branch uses the actual ODE and the proved primitive supplier.
The zero-curvature branch uses constancy before any division by r*ell.
This supplies center-only fields, not the full MeanFlowLp.Regularity record. -/
noncomputable section
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open CenterMeanSecondJetSource
open scoped ContDiff
variable {D m : ℕ}

theorem centerMeanLp_contDiff_original_data (d : Data (Fin D) m) :
    ContDiff ℝ ∞ (centerMeanLp d) := by
  by_cases he : (kernelData d).ell = 0
  · exact centerMeanLp_contDiff_of_ell_zero d he
  · have hL : (kernelData d).r * (kernelData d).ell ≠ 0 :=
      mul_ne_zero (ne_of_gt (kernelData d).hr) he
    exact centerMeanLp_contDiff_from_primitives d _ _ hL hL
      (centerPhasePrimitiveBudgets_commonSeed d (c := 128) le_rfl)

/-- Positive-order common-seed L²/RMS bound, including zero curvature.
Both physical scales are r*ell, the radius is the original G.R, and s=sigma/2. -/
theorem norm_iteratedDeriv_centerMeanLp_le_original_data (d : Data (Fin D) m)
    {c : ℝ} (hc : 128 ≤ c) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv (k+1) (centerMeanLp d) t‖ ≤
      centerSourceBudget d ((kernelData d).r*(kernelData d).ell)
        ((kernelData d).r*(kernelData d).ell) c d.G.R k := by
  by_cases he : (kernelData d).ell = 0
  · rw [iteratedDeriv_centerMeanLp_eq_zero_of_ell_zero d he k]
    simpa only [Pi.zero_apply, norm_zero] using
      centerSourceBudget_nonneg d ((kernelData d).r*(kernelData d).ell)
        ((kernelData d).r*(kernelData d).ell) c d.G.R k
  · have hL : (kernelData d).r * (kernelData d).ell ≠ 0 :=
      mul_ne_zero (ne_of_gt (kernelData d).hr) he
    exact norm_iteratedDeriv_centerMeanLp_le_from_primitives d _ _ hL hL
      (by linarith) d.G.R_pos (by linarith [d.G.R_le_half])
      (centerPhasePrimitiveBudgets_commonSeed d hc) k t

/-- Only the three center fields; the order-zero offset is not discarded. -/
theorem centerMeanLp_center_fields_original_data (d : Data (Fin D) m)
    (hm : 1 ≤ m) {c : ℝ} (hc : 128 ≤ c) :
    0 ≤ centerSourceBudget d ((kernelData d).r*(kernelData d).ell)
      ((kernelData d).r*(kernelData d).ell) c d.G.R (m-1) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ m (centerMeanLp d) t) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedDeriv m (centerMeanLp d) t‖ ≤
        centerSourceBudget d ((kernelData d).r*(kernelData d).ell)
          ((kernelData d).r*(kernelData d).ell) c d.G.R (m-1)) := by
  refine ⟨centerSourceBudget_nonneg d _ _ c d.G.R (m-1), ?_, ?_⟩
  · intro t _
    exact ((centerMeanLp_contDiff_original_data d).of_le (by simp)).contDiffAt
  · intro t _
    simpa only [Nat.sub_add_cancel hm] using
      norm_iteratedDeriv_centerMeanLp_le_original_data d hc (m-1) t

end AcceleratedLogConcave.Numerics.MeanFlowLp
