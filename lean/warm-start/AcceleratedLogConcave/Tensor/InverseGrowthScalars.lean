import AcceleratedLogConcave.Tensor.InverseOrderConstants
import AcceleratedLogConcave.Tensor.FlowOrderGrowthScalars
import Mathlib.Tactic

/-!

-/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Tensor.InverseFlow
open FlowInduction

theorem inverse_growth_exp_lower : (5/4 : ℝ) ≤ growthConstant := by
  have h := Real.add_one_le_exp (1/4 : ℝ)
  unfold growthConstant
  linarith

theorem inverse_growth_kernel_contraction :
    growthConstant * (2-growthConstant) ≤ (15/16 : ℝ) := by
  have h := inverse_growth_exp_lower
  nlinarith [sq_nonneg (growthConstant - 5/4)]

theorem inverse_growth_kernel_positive : 0 ≤ 2-growthConstant := by
  have h := growthConstant_le_four_thirds
  linarith

/-- The finite coefficient multiplier used to bound the derivative kernel.
No power series or differentiation of a series is invoked. -/
theorem inverse_growth_half_weight (n : ℕ) :
    ((n : ℝ)+1) * (1/2 : ℝ)^n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : 0 ≤ (1/2 : ℝ)^n := pow_nonneg (by norm_num) _
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hnp : 0 ≤ (n : ℝ) * (1/2 : ℝ)^n := mul_nonneg hn hp
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith

theorem inverse_growth_mass_barrier :
    growthConstant + (15/16 : ℝ) * (16*growthConstant) =
      16*growthConstant := by ring

theorem inverse_growth_mass_clean : 16*growthConstant ≤ (64/3 : ℝ) := by
  have h := growthConstant_le_four_thirds
  linarith
end AcceleratedLogConcave.Tensor.InverseFlow
