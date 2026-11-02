import AcceleratedLogConcave.Analysis.AnglePhaseScale
import Mathlib.Data.Nat.Factorial.Basic

/-! The actual affine pullback scale turns the physical displacement jet
constant into the phase gradient budget, without dimension-dependent factors. -/
noncomputable section
namespace AcceleratedLogConcave.Analysis.AnglePhase

theorem displacement_pullback_budget_le {R q l : ℝ}
    (hR : 0 < R) (hq : 0 < q) (hl : 0 < l) (n : ℕ) :
    (q^n / (2*l*R)) * (2*l * (256:ℝ)^n * (n.factorial : ℝ) * R^((1:ℝ)-(n:ℝ))) ≤
      (256:ℝ)^(n+1) * ((n+1).factorial : ℝ) * (radius R q)^(-(n:ℝ)) := by
  have hr : 0 < radius R q := radius_pos hR hq
  have he : R^((1:ℝ)-(n:ℝ)) = R/R^n := by
    rw [sub_eq_add_neg,Real.rpow_add hR,Real.rpow_one,Real.rpow_neg hR.le,Real.rpow_natCast]
    rfl
  have hc : (256:ℝ)^n * (n.factorial : ℝ) ≤
      (256:ℝ)^(n+1) * ((n+1).factorial : ℝ) := by
    apply mul_le_mul
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 256) (Nat.le_succ n))
    · exact_mod_cast Nat.factorial_le (Nat.le_succ n)
    · positivity
    · positivity
  have hp := pow_le_pow_left₀ (div_nonneg hq.le hR.le)
    (pullback_ratio_le_inv_radius hR hq) n
  calc
    _ = ((256:ℝ)^n * (n.factorial : ℝ)) * (q/R)^n := by
      rw [he,div_pow]
      field_simp [ne_of_gt hR,ne_of_gt hl]
    _ ≤ ((256:ℝ)^(n+1) * ((n+1).factorial : ℝ)) * (radius R q)⁻¹^n :=
      mul_le_mul hc hp (by positivity) (by positivity)
    _ = _ := by rw [Real.rpow_neg hr.le,Real.rpow_natCast,inv_pow]
end AcceleratedLogConcave.Analysis.AnglePhase
