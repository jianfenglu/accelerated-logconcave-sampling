import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Endpoints do not create integrability obligations for the clock average. -/
noncomputable section
open Set MeasureTheory
namespace AcceleratedLogConcave.Kinetic

/-- An interior-continuous, uniformly bounded scalar energy is integrable over
its clock interval; no artificial endpoint value or endpoint derivative is needed. -/
theorem intervalIntegrable_of_continuousOn_Ioo_bounded {f : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Ioo a b))
    (hb : ∀ t ∈ Ioo a b, ‖f t‖ ≤ C) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  apply Integrable.mono' (integrable_const C)
    (hf.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hb t ht

end AcceleratedLogConcave.Kinetic
