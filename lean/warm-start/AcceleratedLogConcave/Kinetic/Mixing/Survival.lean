import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! The genuine uniform stopping law and exact survival-weight identity. -/
noncomputable section
open MeasureTheory Set
namespace AcceleratedLogConcave.Kinetic

/-- Uniform clock on [0,r]; the endpoint convention is immaterial for volume. -/
def clockLaw (r : ℝ) : Measure ℝ :=
  (ENNReal.ofReal r)⁻¹ • volume.restrict (Ioc 0 r)

theorem clockLaw_probability (r : ℝ) (hr : 0 < r) : IsProbabilityMeasure (clockLaw r) := by
  constructor
  simp only [clockLaw, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top

/-- The clock average is exactly the normalized interval integral. -/
theorem clockLaw_integral {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (r : ℝ) (hr : 0 < r) (f : ℝ → H) :
    (∫ t, f t ∂clockLaw r) = r⁻¹ • ∫ t in 0..r, f t := by
  rw [clockLaw, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hr.le,
    intervalIntegral.integral_of_le hr.le]

/-- Exact survival weight; the common initial value occurs once before drawing
any clock. This is the integration-by-parts form of the triangular Fubini identity. -/
theorem survival_weight_identity (r : ℝ) (F F' : ℝ → ℝ)
    (hF : ∀ t ∈ uIcc 0 r, HasDerivAt F (F' t) t)
    (hI : IntervalIntegrable F' volume 0 r) :
    (∫ t in 0..r, F t) = r * F 0 + ∫ t in 0..r, (r - t) * F' t := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => r - t) (u' := fun _ => (-1 : ℝ))
    (v := F) (v' := F')
    (fun t _ => (hasDerivAt_id t).const_sub r) hF
    (intervalIntegrable_const) hI
  simp only [sub_self, zero_mul, sub_zero, neg_one_mul, intervalIntegral.integral_neg] at h
  linarith

/-- Source current bound integrated against the actual clock survival weight. -/
theorem survival_weight_bound (r A B : ℝ) (hr : 0 ≤ r) (F F' R : ℝ → ℝ)
    (hF : ∀ t ∈ uIcc 0 r, HasDerivAt F (F' t) t)
    (hI : IntervalIntegrable F' volume 0 r)
    (hleft : IntervalIntegrable (fun t => (r - t) * F' t) volume 0 r)
    (hright : IntervalIntegrable (fun t => (r - t) * (-A + B * R t)) volume 0 r)
    (hbound : ∀ t ∈ Icc 0 r, F' t ≤ -A + B * R t) :
    (∫ t in 0..r, F t) ≤ r * F 0 + ∫ t in 0..r, (r - t) * (-A + B * R t) := by
  rw [survival_weight_identity r F F' hF hI]
  apply add_le_add_right
  exact intervalIntegral.integral_mono_on hr hleft hright fun t ht =>
    mul_le_mul_of_nonneg_left (hbound t ht) (sub_nonneg.mpr ht.2)

end AcceleratedLogConcave.Kinetic
