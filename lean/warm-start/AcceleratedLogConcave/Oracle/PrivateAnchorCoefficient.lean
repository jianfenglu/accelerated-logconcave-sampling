import AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorStability
import Mathlib.Algebra.Order.Field.GeomSum

/-! Uniform bounds for the actual finite private-anchor propagation coefficient.
No division by curvature or radius is used; zero endpoints remain included. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorStability
open Numerics.AffineGraph
open scoped BigOperators

variable {m : ℕ} (M : MeanGeometry m) (r : ℝ) (N : ℕ) (κ A : ℝ)

/-- The finite source sum is paid by its actual contraction denominator. -/
theorem coefficient_le_div (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hq : κ*A < 1) :
    coefficient M r N κ A ≤ κ*r*(backwardEnd M.R)^2 / (1-κ*A) := by
  have hs : (∑ j ∈ Finset.range (N+1), (κ*A)^j) ≤ 1/(1-κ*A) := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := N+1) (mul_nonneg hκ hA) hq)
  unfold coefficient
  calc
    _ ≤ (κ*r*(backwardEnd M.R)^2) * (1/(1-κ*A)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- A concrete half-contraction cap, with no hidden dependence on N or dimension. -/
theorem coefficient_le_twice (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hq : κ*A ≤ 1/2) :
    coefficient M r N κ A ≤ 2*κ*r*(backwardEnd M.R)^2 := by
  have hd : 0 < 1-κ*A := by linarith
  have hs := coefficient_le_div M r N κ A hr hκ hA (by linarith)
  apply hs.trans
  apply (div_le_iff₀ hd).2
  have hc : 0 ≤ κ*r*(backwardEnd M.R)^2 := by positivity
  nlinarith [mul_nonneg hc (show 0 ≤ 1/2-κ*A by linarith)]

/-- Radius-only envelope, including κ=0 and r=0. -/
theorem coefficient_le_twice_radius (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hq : κ*A ≤ 1/2) : coefficient M r N κ A ≤ 2*κ*r := by
  have hb : (backwardEnd M.R)^2 ≤ 1 := by
    unfold backwardEnd
    rw [Real.sq_sqrt (by nlinarith [M.R_pos, M.R_le_half])]
    nlinarith [sq_nonneg M.R]
  exact (coefficient_le_twice M r N κ A hr hκ hA hq).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*κ*r by positivity)])

end AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorStability
