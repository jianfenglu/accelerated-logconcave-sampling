import AcceleratedLogConcave.Numerics.VelocityPhaseJetBudget
import AcceleratedLogConcave.Numerics.CenterMeanPhasePrimitiveAssemblyOriginalData
import AcceleratedLogConcave.Numerics.VelocityZeroCurvature

/-! NEW reconstruction: actual common-seed velocity L² bounds from original data.
The positive-scale branch uses the actual ODE and the proved primitive supplier.
The zero-curvature branch uses the vanishing kernel norm bound before division by r*ell.
This supplies velocity-only fields, not the full MeanFlowLp.Regularity record. -/
noncomputable section
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open CenterMeanSecondJetSource
open scoped ContDiff
variable {D m : ℕ}

theorem velocityLp_contDiff_original_data (d : Data (Fin D) m) :
    ContDiff ℝ ∞ (velocityLp d) := by
  by_cases he : (kernelData d).ell = 0
  · exact velocityLp_contDiff_of_ell_zero d he
  · have hL : (kernelData d).r * (kernelData d).ell ≠ 0 :=
      mul_ne_zero (ne_of_gt (kernelData d).hr) he
    exact velocityLp_contDiff_from_primitives d _ _ hL
      (centerPhasePrimitiveBudgets_commonSeed d (c := 128) le_rfl)

/-- Every-order common-seed L²/RMS bound, including zero curvature.
The physical scale is r*ell, the radius is the original G.R, and s=sigma/2. -/
theorem norm_iteratedDeriv_velocityLp_le_original_data (d : Data (Fin D) m)
    {c : ℝ} (hc : 128 ≤ c) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (velocityLp d) t‖ ≤
      velocitySourceBudget d ((kernelData d).r*(kernelData d).ell)
        c d.G.R k := by
  by_cases he : (kernelData d).ell = 0
  · rw [iteratedDeriv_velocityLp_eq_zero_of_ell_zero d he k]
    simpa only [Pi.zero_apply, norm_zero] using
      velocitySourceBudget_nonneg d ((kernelData d).r*(kernelData d).ell)
        c d.G.R k
  · have hL : (kernelData d).r * (kernelData d).ell ≠ 0 :=
      mul_ne_zero (ne_of_gt (kernelData d).hr) he
    exact norm_iteratedDeriv_velocityLp_le_from_primitives d _ _ hL
      (by linarith) d.G.R_pos (by linarith [d.G.R_le_half])
      (centerPhasePrimitiveBudgets_commonSeed d hc) k t

/-- The three velocity fields, at the correct P-jet index m. -/
theorem velocityLp_velocity_fields_original_data (d : Data (Fin D) m)
    {c : ℝ} (hc : 128 ≤ c) :
    0 ≤ velocitySourceBudget d ((kernelData d).r*(kernelData d).ell)
      c d.G.R m ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ m (velocityLp d) t) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedDeriv m (velocityLp d) t‖ ≤
        velocitySourceBudget d ((kernelData d).r*(kernelData d).ell)
          c d.G.R m) := by
  refine ⟨velocitySourceBudget_nonneg d _ c d.G.R m, ?_, ?_⟩
  · intro t _
    exact ((velocityLp_contDiff_original_data d).of_le (by simp)).contDiffAt
  · intro t _
    exact norm_iteratedDeriv_velocityLp_le_original_data d hc m t

end AcceleratedLogConcave.Numerics.MeanFlowLp
