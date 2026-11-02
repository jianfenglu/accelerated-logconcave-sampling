import AcceleratedLogConcave.Tensor.FlowOrderConstants
import Mathlib.Tactic

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor.FlowInduction

/-- Direct cardinality proof, avoiding a guessed partition sum API. -/
theorem growth_sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    (∑ i, c.partSize i) = n := by
  have h := Fintype.card_congr c.equivSigma
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

theorem growthConstant_le_four_thirds : growthConstant ≤ (4/3 : ℝ) := by
  have h := Real.add_one_le_exp (-(1/4 : ℝ))
  have hm := mul_le_mul_of_nonneg_left h (le_of_lt (Real.exp_pos (1/4 : ℝ)))
  have he : Real.exp (1/4 : ℝ) * Real.exp (-(1/4 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at hm
  unfold growthConstant
  nlinarith

theorem growth_sqrt_two_le : Real.sqrt 2 ≤ (3/2 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- The numerical barrier after bounding E*s^3 by 4. -/
theorem growth_rational_barrier :
    (1/24 : ℝ) + 4 * (1/256) * (32/29) ≤ 1/16 := by
  norm_num

/-- Positive denominator for the finite geometric-series bound. -/
theorem growth_geometric_denominator :
    (29/32 : ℝ) ≤ 1 - Real.sqrt 2 / 16 := by
  have hs := growth_sqrt_two_le
  linarith

end AcceleratedLogConcave.Tensor.FlowInduction
