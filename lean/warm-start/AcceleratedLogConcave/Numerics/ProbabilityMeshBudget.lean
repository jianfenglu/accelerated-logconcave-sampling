import AcceleratedLogConcave.Numerics.AffineResidual

/-!
# Probability mesh budget cancellation

The conditional step condition is an explicit geometric premise, not a consequence
of original Data or the backward-only MeshConditions. The cell envelope remains
an explicit quantitative supplier boundary. No derivative estimate is asserted.
-/
noncomputable section
open scoped BigOperators
open Set
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.AffineResidual

private theorem probability_den_pos {lo hi : ℝ} (M : IntervalMesh lo hi)
    (hlo : 0 ≤ lo) (hhi : hi < 1) (c : M.Cell) :
    0 < 1 - (M.right c)^2 := by
  have hright : 0 ≤ M.right c := hlo.trans ((M.lo_le_left c).trans (sub_pos.mp (M.length_pos c)).le)
  have hright1 : M.right c < 1 := (M.right_le_hi c).trans_lt hhi
  nlinarith

/-- A named mesh hypothesis is essential: arbitrary conditional meshes do not
satisfy this estimate. The envelope B may be supplied independently of regularity. -/
theorem probability_cellBudget_le {lo hi : ℝ} (M : IntervalMesh lo hi)
    (hlo : 0 ≤ lo) (hhi : hi < 1) (m : ℕ)
    (B : M.Cell → ℝ) (A h₀ : ℝ) (hA : 0 ≤ A) (_hh : 0 ≤ h₀)
    (hstep : ∀ c, M.length c ≤ 2*h₀*(1-(M.right c)^2))
    (hbudget : ∀ c, B c ≤ A/(1-(M.right c)^2)^m) :
    cellBudget M m B ≤
      2^(m+1)*(hi-lo)*A*h₀^m/(m.factorial:ℝ) := by
  have hfac : 0 < (m.factorial:ℝ) := by positivity
  have hcell (c : M.Cell) :
      2 * M.length c ^ (m+1) * B c / (m.factorial:ℝ) ≤
        M.length c * (2^(m+1)*A*h₀^m/(m.factorial:ℝ)) := by
    have hl := (M.length_pos c).le
    have hq := probability_den_pos M hlo hhi c
    have hp : M.length c ^ m ≤ (2*h₀*(1-(M.right c)^2))^m :=
      pow_le_pow_left₀ (M.length_pos c).le (hstep c) m
    calc
      _ ≤ 2 * M.length c ^ (m+1) * (A/(1-(M.right c)^2)^m) /
          (m.factorial:ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbudget c) (by positivity)) hfac.le
      _ = (2 * M.length c * A / ((1-(M.right c)^2)^m * (m.factorial:ℝ))) *
          M.length c ^ m := by rw [pow_succ]; ring
      _ ≤ (2 * M.length c * A / ((1-(M.right c)^2)^m * (m.factorial:ℝ))) *
          (2*h₀*(1-(M.right c)^2))^m := by
        exact mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by
        rw [mul_pow, mul_pow, pow_succ]
        field_simp [ne_of_gt hq]
        ring
  calc
    cellBudget M m B ≤ ∑ c, M.length c *
        (2^(m+1)*A*h₀^m/(m.factorial:ℝ)) := Finset.sum_le_sum fun c _ => hcell c
    _ = _ := by rw [← Finset.sum_mul, M.sum_length]; ring

end AcceleratedLogConcave.Numerics.AffineResidual
