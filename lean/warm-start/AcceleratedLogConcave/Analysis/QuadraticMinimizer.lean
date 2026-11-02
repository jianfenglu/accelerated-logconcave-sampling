import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith

/-! An analytic minimizer from a quadratic lower bound.
The point is derived, never supplied as input or exposed as an algorithmic
oracle. The norm constant is deliberately coarse and qualitative. -/
noncomputable section
open Set Filter
namespace AcceleratedLogConcave.Analysis.QuadraticMinimizer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A continuous quadratically coercive function has a derived global minimizer
with a norm bound controlled by the linear term. -/
theorem exists_minimizer_norm_le {F : E → ℝ} (hF : Continuous F)
    (L : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x, F 0 + L x + c * ‖x‖ ^ 2 ≤ F x) :
    ∃ z : E, (∀ y, F z ≤ F y) ∧ ‖z‖ ≤ ‖L‖ / c := by
  have hlinear (x : E) : -(‖L‖ * ‖x‖) ≤ L x :=
    (neg_le_neg (L.le_opNorm x)).trans (by
      simpa only [Real.norm_eq_abs] using neg_abs_le (L x))
  have hfar : ∀ᶠ x in cocompact E, F 0 ≤ F x := by
    filter_upwards [(isCompact_closedBall (0 : E) (‖L‖ / c + 1)).compl_mem_cocompact] with x hx
    have hx' : ‖L‖ / c + 1 < ‖x‖ := by
      simpa only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hmul : ‖L‖ ≤ c * ‖x‖ := by
      apply le_of_lt
      simpa only [mul_comm] using
        (div_lt_iff₀ hc).mp (by linarith : ‖L‖ / c < ‖x‖)
    have hq := mul_le_mul_of_nonneg_right hmul (norm_nonneg x)
    nlinarith [hlower x, hlinear x]
  obtain ⟨z, hz⟩ := hF.exists_forall_le' 0 hfar
  refine ⟨z, hz, ?_⟩
  have hq : c * ‖z‖ ^ 2 ≤ ‖L‖ * ‖z‖ := by
    linarith [hlower z, hlinear z, hz 0]
  by_cases hzero : ‖z‖ = 0
  · rw [hzero]
    exact div_nonneg (norm_nonneg _) hc.le
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    apply (le_div_iff₀ hc).mpr
    apply (mul_le_mul_iff_left₀ hzpos).mp
    nlinarith

/-- The analytic minimizer is a critical point, with the same derived bound. -/
theorem exists_critical_minimizer_norm_le {F : E → ℝ} (hF : Continuous F)
    (L : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x, F 0 + L x + c * ‖x‖ ^ 2 ≤ F x) :
    ∃ z : E, (∀ y, F z ≤ F y) ∧ fderiv ℝ F z = 0 ∧ ‖z‖ ≤ ‖L‖ / c := by
  obtain ⟨z, hz, hb⟩ := exists_minimizer_norm_le hF L hc hlower
  have hm : IsLocalMin F z := Filter.Eventually.of_forall hz
  exact ⟨z, hz, hm.fderiv_eq_zero, hb⟩

end AcceleratedLogConcave.Analysis.QuadraticMinimizer
