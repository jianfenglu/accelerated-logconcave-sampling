import AcceleratedLogConcave.Gibbs.HeatHessian

/-!
# Original-potential curvature for the localized W05 interval

The source potential is only C², with Hessian between κ⁻¹ I and I.
The existing `heat_hessian_curvature` theorem supplies the analytic estimate.
The new witness is exactly `(κ + A)⁻¹` up to the return variance A, but
decreases beyond A. Thus extending the classical family to R > A does not
weaken W05's common curvature or change its rate.

This file does not construct the joint variance regularity, density continuity
equation, or identification of the Gaussian heat law needed by
`VarianceHeatFamily`. Those are separate obligations, not curvature premises.
-/

noncomputable section
open MeasureTheory Set

namespace AcceleratedLogConcave.Gibbs

/-- A common witness below A, with the natural heat-curvature witness above A. -/
def localizedHeatLower (κ A t : ℝ) : ℝ := (κ + max A t)⁻¹

theorem localizedHeatLower_eq_of_le {κ A t : ℝ} (ht : t ≤ A) :
    localizedHeatLower κ A t = (κ + A)⁻¹ := by
  simp only [localizedHeatLower, max_eq_left ht]

theorem localizedHeatLower_eq_of_ge {κ A t : ℝ} (ht : A ≤ t) :
    localizedHeatLower κ A t = (κ + t)⁻¹ := by
  simp only [localizedHeatLower, max_eq_right ht]

theorem localizedHeatLower_pos {κ A t : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) :
    0 < localizedHeatLower κ A t := by
  apply inv_pos.mpr
  exact add_pos_of_pos_of_nonneg hκ (hA.trans (le_max_left A t))

theorem localizedHeatLower_le_natural {κ A t : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t) :
    localizedHeatLower κ A t ≤ (κ + t)⁻¹ := by
  apply (inv_le_inv₀
    (add_pos_of_pos_of_nonneg hκ (ht.trans (le_max_right A t)))
    (add_pos_of_pos_of_nonneg hκ ht)).mpr
  exact add_le_add le_rfl (le_max_right A t)

/-- Exact scalar identification of the existing heat-curvature coefficient. -/
theorem inv_curvature_heat_coefficient {κ t : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t) :
    κ⁻¹ / (1 + κ⁻¹ * t) = (κ + t)⁻¹ := by
  have hκt : 0 < κ + t := add_pos_of_pos_of_nonneg hκ ht
  have hden : 0 < 1 + κ⁻¹ * t := by positivity
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual heat-potential curvature from original data, on every positive
variance. No hypothesis assumes the desired heat curvature. -/
theorem heat_hessian_localized_curvature {F : E → ℝ} {κ A t : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (ht : 0 < t)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ ‖v‖ ^ 2)
    (y v : E) :
    localizedHeatLower κ A t * ‖v‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (heatPotential F t)) y v v ∧
      fderiv ℝ (fderiv ℝ (heatPotential F t)) y v v ≤ ‖v‖ ^ 2 := by
  have h := heat_hessian_curvature hF (inv_pos.mpr hκ).le ht hlo
    (L := 1) (by simpa only [one_mul] using hup) y v
  rw [inv_curvature_heat_coefficient hκ ht.le] at h
  exact ⟨(mul_le_mul_of_nonneg_right
    (localizedHeatLower_le_natural hκ ht.le) (sq_nonneg ‖v‖)).trans h.1,
    by simpa only [one_mul] using h.2⟩

/-- The precise common curvature on [3A/4,A], with no loss involving R. -/
theorem heat_hessian_common_curvature {F : E → ℝ} {κ A t : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hA : 0 < A)
    (ht : t ∈ Icc (3 * A / 4) A)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ ‖v‖ ^ 2)
    (y v : E) :
    (κ + A)⁻¹ * ‖v‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (heatPotential F t)) y v v ∧
      fderiv ℝ (fderiv ℝ (heatPotential F t)) y v v ≤ ‖v‖ ^ 2 := by
  have ht0 : 0 < t := by linarith [ht.1]
  simpa only [localizedHeatLower_eq_of_le ht.2] using
    heat_hessian_localized_curvature (A := A) hF hκ ht0 hlo hup y v

/-- Strictly positive curvature, C² regularity, and normalizability throughout
the enlarged analytic envelope, including variances beyond A. -/
theorem heat_potential_envelope_data {F : E → ℝ} {κ A R : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hA : 0 < A)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ ‖v‖ ^ 2)
    (t : ℝ) (ht : t ∈ Icc (3 * A / 4) R) :
    ContDiff ℝ 2 (heatPotential F t) ∧
      0 < localizedHeatLower κ A t ∧
      (∀ y v, localizedHeatLower κ A t * ‖v‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (heatPotential F t)) y v v) ∧
      (∀ y v, fderiv ℝ (fderiv ℝ (heatPotential F t)) y v v ≤ ‖v‖ ^ 2) ∧
      Integrable (fun x => Real.exp (-heatPotential F t x)) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hC := contDiff_two_heatPotential hF (inv_pos.mpr hκ).le ht0 hlo
  have hm := localizedHeatLower_pos (t := t) hκ hA.le
  have hH := heat_hessian_localized_curvature (A := A) hF hκ ht0 hlo hup
  exact ⟨hC, hm, fun y v => (hH y v).1, fun y v => (hH y v).2,
    integrable_exp_neg_of_hessian_lower hC hm (fun y v => (hH y v).1)⟩

end AcceleratedLogConcave.Gibbs
