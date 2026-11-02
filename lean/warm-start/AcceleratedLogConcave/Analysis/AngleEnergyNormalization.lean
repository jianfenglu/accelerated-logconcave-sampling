import AcceleratedLogConcave.Analysis.AnglePhaseScale

/-! Arithmetic-only normalization of the whole Gaussian jet energy. -/
noncomputable section
namespace AcceleratedLogConcave.Analysis.AnglePhase

theorem scaled_sqrt_energy_eq {q S K : ℝ} (hq : 0 < q) (hS : 0 < S)
    (hK : 0 ≤ K) (n : ℕ) :
    ‖(q⁻¹)^n‖ * Real.sqrt (K*S^(-4*(n:ℝ))) =
      Real.sqrt K * (q⁻¹/S^2)^n := by
  have hp : S^(-2*(n:ℝ)) = ((S^2)⁻¹)^n := by
    rw [Real.rpow_mul hS.le,Real.rpow_natCast,Real.rpow_neg hS.le,Real.rpow_two]
  have he : S^(-4*(n:ℝ)) = (S^(-2*(n:ℝ)))^2 := by
    rw [← Real.rpow_natCast (S^(-2*(n:ℝ))) 2,← Real.rpow_mul hS.le]
    congr 1
    ring
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hq.le) n),
    Real.sqrt_mul hK,he,Real.sqrt_sq (Real.rpow_nonneg hS.le _),hp,
    div_eq_mul_inv,mul_pow]
  ring

theorem scaled_sqrt_energy_le {R q K : ℝ} (hR : 0 < R) (hq : 0 < q)
    (hK : 0 ≤ K) (hspeed : q⁻¹/(radius R q)^2 ≤ 2/R^2) (n : ℕ) :
    ‖(q⁻¹)^n‖ * Real.sqrt (K*(radius R q)^(-4*(n:ℝ))) ≤
      Real.sqrt K * (2/R^2)^n := by
  rw [scaled_sqrt_energy_eq hq (radius_pos hR hq) hK]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hspeed n) (Real.sqrt_nonneg K)
end AcceleratedLogConcave.Analysis.AnglePhase
