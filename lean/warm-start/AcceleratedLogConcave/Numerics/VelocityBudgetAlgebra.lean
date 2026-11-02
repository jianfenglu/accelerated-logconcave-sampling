import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section

theorem velocity_budget_algebra (D k : ℕ) (L s Q R : ℝ)
    (hL : 0 ≤ L) (hs : 0 < s) (hQ : 0 ≤ Q) (hR : 0 < R) :
    Real.sqrt D * Real.sqrt (2*((L/s)^(k+1))^2 * Q * R^(-2*(2*(k:ℝ)+1))) =
      (L/s)^(k+1) * Real.sqrt ((D+D : ℕ)*Q) / R^(2*k+1) := by
  have hr : R^(-2*(2*(k:ℝ)+1)) = (R^(2*k+1))⁻¹ ^ 2 := by
    rw [show -2*(2*(k:ℝ)+1) = -(((2*k+1)*2 : ℕ):ℝ) by push_cast; ring]
    rw [Real.rpow_neg hR.le,Real.rpow_natCast,pow_mul,inv_pow]
  have hpow : 0 ≤ (L/s)^(k+1) := pow_nonneg (div_nonneg hL hs.le) _
  have hd : 0 ≤ (D:ℝ) := Nat.cast_nonneg D
  have hleft : 0 ≤ Real.sqrt D * Real.sqrt (2*((L/s)^(k+1))^2 * Q * R^(-2*(2*(k:ℝ)+1))) := by positivity
  have hright : 0 ≤ (L/s)^(k+1) * Real.sqrt ((D+D : ℕ)*Q) / R^(2*k+1) := by positivity
  have hrad : 0 ≤ 2*((L/s)^(k+1))^2 * Q * R^(-2*(2*(k:ℝ)+1)) := by positivity
  have hrad2 : 0 ≤ ((D+D:ℕ):ℝ)*Q := mul_nonneg (Nat.cast_nonneg _) hQ
  apply (sq_eq_sq₀ hleft hright).mp
  conv_lhs => rw [mul_pow,Real.sq_sqrt hd,Real.sq_sqrt hrad,hr]
  conv_rhs => rw [div_pow,mul_pow,Real.sq_sqrt hrad2]
  push_cast
  field_simp
  ring
