import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Bounded continuous scalar currents can be integrated in either order on
a compact probability-time interval and a finite spatial reference law. -/
noncomputable section
open Set Function MeasureTheory
open scoped Topology

namespace AcceleratedLogConcave.Conditional.Stein
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure E} [IsFiniteMeasure μ]

omit [SecondCountableTopology E] in
theorem continuousOn_integral_bounded_current {b : ℝ} (hb : 0 ≤ b)
    (H : ℝ → E → ℝ)
    (hH : Continuous (fun p : E × Icc 0 b => H p.2 p.1))
    {C : ℝ} (hbound : ∀ t ∈ Icc 0 b, ∀ y, ‖H t y‖ ≤ C) :
    ContinuousOn (fun t => ∫ y, H t y ∂μ) (Icc 0 b) := by
  let G (t : ℝ) (y : E) := H (projIcc 0 b hb t) y
  have hc : Continuous (uncurry G) := hH.comp
    (continuous_snd.prodMk ((continuous_projIcc (h := hb)).comp continuous_fst))
  have hG : Continuous (fun t => ∫ y, G t y ∂μ) :=
    continuous_of_dominated
      (fun t => (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (fun t => Filter.Eventually.of_forall fun y => hbound _ (projIcc 0 b hb t).2 y)
      (integrable_const C)
      (Filter.Eventually.of_forall fun y => hc.comp (continuous_id.prodMk continuous_const))
  apply hG.continuousOn.congr
  intro t ht
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by simp only [G, projIcc_of_mem hb ht]

theorem intervalIntegral_integral_swap_bounded_current {b : ℝ} (hb : 0 ≤ b)
    (H : ℝ → E → ℝ)
    (hH : Continuous (fun p : E × Icc 0 b => H p.2 p.1))
    {C : ℝ} (hbound : ∀ t ∈ Icc 0 b, ∀ y, ‖H t y‖ ≤ C) :
    (∫ t in 0..b, ∫ y, H t y ∂μ) = ∫ y, (∫ t in 0..b, H t y) ∂μ := by
  let G (t : ℝ) (y : E) := H (projIcc 0 b hb t) y
  have hc : Continuous (uncurry G) := hH.comp
    (continuous_snd.prodMk ((continuous_projIcc (h := hb)).comp continuous_fst))
  have hi : Integrable (uncurry G) ((volume.restrict (Ioc 0 b)).prod μ) :=
    (integrable_const C).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hbound _ (projIcc 0 b hb p.1).2 p.2)
  have heq (t : ℝ) (ht : t ∈ Icc 0 b) (y : E) : G t y = H t y := by
    simp only [G, projIcc_of_mem hb ht]
  calc
    (∫ t in 0..b, ∫ y, H t y ∂μ) = ∫ t in 0..b, ∫ y, G t y ∂μ := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc 0 b := by simpa only [uIcc_of_le hb] using ht
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => (heq t ht' y).symm)
    _ = ∫ y, (∫ t in 0..b, G t y) ∂μ := by
      simp only [intervalIntegral.integral_of_le hb]
      exact integral_integral_swap hi
    _ = ∫ y, (∫ t in 0..b, H t y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply intervalIntegral.integral_congr
      intro t ht
      exact heq t (by simpa only [uIcc_of_le hb] using ht) y

end AcceleratedLogConcave.Conditional.Stein
