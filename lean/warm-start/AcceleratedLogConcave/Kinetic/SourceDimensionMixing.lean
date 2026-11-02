import AcceleratedLogConcave.Numerics.SourceNumericalAccuracy
import AcceleratedLogConcave.Kinetic.SourceDimensionPhaseCount

/-! Explicit fixed damping and dimension threshold discharging the source
mixing theorem's scalar smallness conditions. Neither depends on the potential. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Kinetic

def sourceDamping : ℝ := Real.sqrt 2/32/32

def sourceMixingStep : ℝ := (Real.sqrt 2/32)/(8*((1:ℝ)/2+200))

def sourceMixingDimension (e : ℝ) : ℕ :=
  Numerics.SourceNumericalAccuracy.dimensionThreshold e (-Real.log sourceMixingStep)

theorem sourceDamping_pos : 0 < sourceDamping := by unfold sourceDamping; positivity

theorem sourceMixingStep_pos : 0 < sourceMixingStep := by unfold sourceMixingStep; positivity

theorem sourceMixingStep_le_quarter : sourceMixingStep ≤ 1/4 := by
  have hs : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
  unfold sourceMixingStep
  linarith

theorem source_dimension_step {e : ℝ} (he : 0 < e) {D : ℕ}
    (hD : sourceMixingDimension e ≤ D) :
    0 < (D:ℝ)^(-e) ∧ (D:ℝ)^(-e) ≤ sourceMixingStep := by
  have hd1 : (1:ℝ) ≤ D := by
    have hd := (Nat.le_ceil (max 1 (Real.exp (-Real.log sourceMixingStep/e)))).trans
      (show (sourceMixingDimension e : ℝ) ≤ D by exact_mod_cast hD)
    exact (le_max_left _ _).trans hd
  have hd : (0:ℝ) < D := by linarith
  refine ⟨Real.rpow_pos_of_pos hd _, ?_⟩
  have hr := Numerics.SourceNumericalAccuracy.resolution_of_dimension he hD
  rw [Real.rpow_def_of_pos hd]
  calc
    _ ≤ Real.exp (Real.log sourceMixingStep) := by
      apply Real.exp_le_exp.mpr
      change -Real.log sourceMixingStep ≤ e*Real.log (D:ℝ) at hr
      nlinarith
    _ = sourceMixingStep := Real.exp_log sourceMixingStep_pos

/-- Every scalar condition of the original reference mixing theorem is now
paid by a dimension threshold fixed before κ, V, or oracle answers. -/
theorem source_dimension_mixing_parameters {e κ : ℝ} (he : 0 < e) (hκ : 1 ≤ κ)
    {D : ℕ} (hD : sourceMixingDimension e ≤ D) :
    0 < sourceDamping ∧ sourceDamping ≤ Real.sqrt 2/32/32 ∧
    0 < (D:ℝ)^(-e) ∧ (D:ℝ)^(-e) ≤ 1/4 ∧
    (D:ℝ)^(-e) ≤ (Real.sqrt 2/32)/(8*((1:ℝ)/2+200)) ∧
    (κ+2*((D:ℝ)^(-e))^2)⁻¹ ≤ 1 := by
  obtain ⟨hp, hs⟩ := source_dimension_step he hD
  refine ⟨sourceDamping_pos, le_rfl, hp, hs.trans sourceMixingStep_le_quarter, hs, ?_⟩
  apply (inv_le_one₀ (by positivity : 0 < κ+2*((D:ℝ)^(-e))^2)).2
  nlinarith [sq_nonneg ((D:ℝ)^(-e))]

end AcceleratedLogConcave.Kinetic
