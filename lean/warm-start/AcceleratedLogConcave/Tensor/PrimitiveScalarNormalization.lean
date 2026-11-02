import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!

-/
noncomputable section
namespace AcceleratedLogConcave.Tensor.ActualCoefficient

/-- Exact nonzero-variance cancellation for the literal pinned source expression. -/
theorem primitive_scalar_normalization (r ell t sigma C : ℝ) (hs : 0 < sigma) (k : ℕ) :
    (r*t^(k+1)) * (((sigma^(k+1))⁻¹*(r*ell)) *
      (C*Real.sqrt (2*sigma)^(k+2))) =
    (r^2*ell)*t*(C*Real.sqrt 2^(k+2))*(t/Real.sqrt sigma)^k := by
  have hv : Real.sqrt sigma ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  conv_lhs => arg 2; arg 1; arg 1; arg 1; rw [← Real.sq_sqrt hs.le]
  simp only [pow_add,pow_one,pow_two,mul_pow,div_pow]
  field_simp [hv, pow_ne_zero k hv]

theorem time_variance_ratio_le {t b : ℝ} (ht : 0 ≤ t) (htb : t ≤ b) (hb : b < 1) :
    t / Real.sqrt (1-t^2) ≤ b / Real.sqrt (1-b^2) := by
  have hb0 : 0 ≤ b := ht.trans htb
  have hsb : 0 < 1-b^2 := by nlinarith
  have hst : 0 < 1-t^2 := by nlinarith
  have hden : Real.sqrt (1-b^2) ≤ Real.sqrt (1-t^2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hst) (Real.sqrt_pos.mpr hsb)).2
  calc
    t * Real.sqrt (1-b^2) ≤ b * Real.sqrt (1-b^2) :=
      mul_le_mul_of_nonneg_right htb (Real.sqrt_nonneg _)
    _ ≤ b * Real.sqrt (1-t^2) := mul_le_mul_of_nonneg_left hden hb0

end AcceleratedLogConcave.Tensor.ActualCoefficient
