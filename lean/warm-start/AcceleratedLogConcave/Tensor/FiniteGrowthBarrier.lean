import AcceleratedLogConcave.Tensor.FlowOrderGrowthScalars
import Mathlib.Tactic

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor.FlowInduction

/-- A finite identity, including the empty sum. -/
theorem growth_finite_geom_identity (q : ℝ) (m : ℕ) :
    (1 - q) * (∑ h ∈ Finset.range m, q ^ h) = 1 - q ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/-- The geometric denominator is paid without an infinite sum. -/
theorem growth_finite_geom_bound {q : ℝ} (hq : 0 ≤ q)
    (hsmall : q ≤ 3/32) (m : ℕ) :
    (∑ h ∈ Finset.range m, q ^ h) ≤ (32/29 : ℝ) := by
  have hnonneg : 0 ≤ ∑ h ∈ Finset.range m, q ^ h :=
    Finset.sum_nonneg (fun h _ => pow_nonneg hq h)
  have hp : 0 ≤ q ^ m := pow_nonneg hq m
  have hid := growth_finite_geom_identity q m
  have hm := mul_le_mul_of_nonneg_right hsmall hnonneg
  nlinarith

/-- Coefficient paid using s^2=2, not the looser s<=3/2 cubed. -/
theorem growth_cubic_coefficient :
    0 ≤ growthConstant * Real.sqrt 2 ^ 3 ∧
    growthConstant * Real.sqrt 2 ^ 3 ≤ 4 := by
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs := growth_sqrt_two_le
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hE0 : 0 ≤ growthConstant := le_of_lt (Real.exp_pos _)
  have hE := growthConstant_le_four_thirds
  have hEs : growthConstant * Real.sqrt 2 ≤ 2 := by
    calc
      _ ≤ (4/3 : ℝ) * Real.sqrt 2 := mul_le_mul_of_nonneg_right hE hs0
      _ ≤ (4/3 : ℝ) * (3/2) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = 2 := by norm_num
  constructor
  · exact mul_nonneg hE0 (pow_nonneg hs0 _)
  · calc
      _ = 2 * (growthConstant * Real.sqrt 2) := by
        rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one, hs2]
        ring
      _ ≤ 4 := by linarith

/-- The exact shift k=h+2, including the prefactor s^(k+1). -/
theorem growth_arity_factor (h : ℕ) :
    Real.sqrt 2 ^ (h+3) * (1/16 : ℝ) ^ (h+2) =
      (Real.sqrt 2 ^ 3 / 256) * (Real.sqrt 2 / 16) ^ h := by
  simp only [pow_add, div_pow, one_pow]
  norm_num
  ring

/-- Every finite arity truncation fits strictly below the required mass.
The integer m is the number of arities (k=2,...,m+1), not the maximum order. -/
theorem growth_finite_arity_barrier (m : ℕ) :
    growthConstant / 32 + growthConstant *
      (∑ h ∈ Finset.range m,
        Real.sqrt 2 ^ (h+3) * (1/16 : ℝ) ^ (h+2)) ≤ (1/16 : ℝ) := by
  have hq0 : 0 ≤ Real.sqrt 2 / 16 := div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hq : Real.sqrt 2 / 16 ≤ (3/32 : ℝ) := by
    have hs := growth_sqrt_two_le
    linarith
  have hG := growth_finite_geom_bound hq0 hq m
  have hcoef := growth_cubic_coefficient
  have hE : growthConstant / 32 ≤ (1/24 : ℝ) := by
    have h := growthConstant_le_four_thirds
    linarith
  have hf : growthConstant *
      (∑ h ∈ Finset.range m,
        Real.sqrt 2 ^ (h+3) * (1/16 : ℝ) ^ (h+2)) =
      (growthConstant * Real.sqrt 2 ^ 3 / 256) *
        (∑ h ∈ Finset.range m, (Real.sqrt 2 / 16) ^ h) := by
    simp_rw [growth_arity_factor]
    rw [← Finset.mul_sum]
    ring
  rw [hf]
  have hterm : (growthConstant * Real.sqrt 2 ^ 3 / 256) *
      (∑ h ∈ Finset.range m, (Real.sqrt 2 / 16) ^ h) ≤ (1/58 : ℝ) := by
    calc
      _ ≤ (growthConstant * Real.sqrt 2 ^ 3 / 256) * (32/29) :=
        mul_le_mul_of_nonneg_left hG (div_nonneg hcoef.1 (by norm_num))
      _ ≤ (4/256 : ℝ) * (32/29) := by nlinarith [hcoef.2]
      _ = 1/58 := by norm_num
  linarith

end AcceleratedLogConcave.Tensor.FlowInduction
