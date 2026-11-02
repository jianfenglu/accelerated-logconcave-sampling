import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Continuity of integrated quadratic defects for bounded operator families. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AcceleratedLogConcave.Kinetic
variable {H K Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [MeasurableSpace Ω]

/-- A uniformly bounded family needs only scalar measurability on each input
for continuity of its integrated squared norm. -/
theorem integral_norm_sq_continuous (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : Ω → H →L[ℝ] K) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ t, ‖T t‖ ≤ C)
    (hm : ∀ f, AEStronglyMeasurable (fun t => ‖T t f‖^2) μ) :
    Continuous (fun f => ∫ t, ‖T t f‖^2 ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => (C*(‖f‖+1))^2)
    (Eventually.of_forall hm) ?_ (integrable_const _) ?_
  · have hn : ∀ᶠ g in 𝓝 f, ‖g‖ < ‖f‖+1 :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by linarith : ‖f‖ < ‖f‖+1))
    filter_upwards [hn] with g hg
    exact Eventually.of_forall fun t => by
      have ht := (T t).le_opNorm g
      have hg' := mul_le_mul_of_nonneg_left hg.le hC
      have hb : ‖T t g‖ ≤ C*(‖f‖+1) :=
        (ht.trans (mul_le_mul_of_nonneg_right (hT t) (norm_nonneg g))).trans hg'
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  · exact Eventually.of_forall fun t => ((T t).continuous.norm.pow 2).continuousAt

end AcceleratedLogConcave.Kinetic
