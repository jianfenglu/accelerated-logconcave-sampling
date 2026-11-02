import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrating scalar pairings on a dense set of Hilbert tests

This is the scalar integration / Hilbert duality step of direct W12, not the
physical weak chain rule. The derivative is required only for each dense test,
and its values need not be represented by a jointly measurable vector field.
Endpoint continuity is explicitly required for the scalar pairings. There is
no strong differentiability or strong continuity assumption on the path.
-/

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A dense family of real Hilbert tests detects the norm. -/
theorem norm_le_of_abs_inner_le_dense
    (D : Set H) (hD : Dense D) (x : H) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ ∈ D, |inner ℝ x ψ| ≤ C * ‖ψ‖) :
    ‖x‖ ≤ C := by
  have hall : ∀ ψ : H, |inner ℝ x ψ| ≤ C * ‖ψ‖ :=
    hD.induction hbound
      (isClosed_le (continuous_const.inner continuous_id).abs
        (continuous_const.mul continuous_norm))
  have hx := hall x
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hx
  nlinarith [norm_nonneg x]

/-- Integrate each scalar test, then take the dense Hilbert dual norm.

No derivative continuity, jointly measurable choice of derivatives, or
Bochner-integrable vector velocity is assumed. Both endpoints are covered by
exactly the displayed scalar continuity assumption. -/
theorem norm_sub_le_integral_of_dense_pairings
    (W : ℝ → H) (D : Set H) (hD : Dense D)
    (d : ℝ → H → ℝ) (C : ℝ → ℝ) {u R : ℝ} (huR : u ≤ R)
    (hcont : ∀ ψ ∈ D, ContinuousOn (fun r => inner ℝ (W r) ψ) (Icc u R))
    (hderiv : ∀ ψ ∈ D, ∀ r ∈ Ioo u R,
      HasDerivAt (fun s => inner ℝ (W s) ψ) (d r ψ) r)
    (hbound : ∀ ψ ∈ D, ∀ r ∈ Ioo u R, |d r ψ| ≤ C r * ‖ψ‖)
    (hC : ∀ r ∈ Icc u R, 0 ≤ C r)
    (hCi : IntervalIntegrable C volume u R) :
    ‖W R - W u‖ ≤ ∫ r in u..R, C r := by
  apply norm_le_of_abs_inner_le_dense D hD (W R - W u)
    (intervalIntegral.integral_nonneg huR hC)
  intro ψ hψ
  have hdiff : DifferentiableOn ℝ (fun r => inner ℝ (W r) ψ) (Ioo u R) :=
    fun r hr => (hderiv ψ hψ r hr).differentiableAt.differentiableWithinAt
  have hspeed : ∀ᵐ r, r ∈ Ioo u R →
      ‖deriv (fun s => inner ℝ (W s) ψ) r‖ ≤ C r * ‖ψ‖ := by
    apply Filter.Eventually.of_forall
    intro r hr
    rw [(hderiv ψ hψ r hr).deriv, Real.norm_eq_abs]
    exact hbound ψ hψ r hr
  have hi := norm_sub_le_integral_of_norm_deriv_le_of_le huR
    (hcont ψ hψ) hdiff hspeed (hCi.mul_const ‖ψ‖)
  simpa only [inner_sub_left, Real.norm_eq_abs,
    intervalIntegral.integral_mul_const] using hi

/-- The exact affine-speed primitive needed in direct W12. This theorem is
abstract until the physical coupled path supplies its scalar chain rule and
closed-endpoint continuity. It also includes the zero-length interval. -/
theorem dense_pairing_increment_le_affine
    (W : ℝ → H) (D : Set H) (hD : Dense D) (d : ℝ → H → ℝ)
    {ell a G u R : ℝ} (hell : 0 ≤ ell) (ha : 0 ≤ a) (hG : 0 ≤ G)
    (hu : 0 ≤ u) (huR : u ≤ R)
    (hcont : ∀ ψ ∈ D, ContinuousOn (fun r => inner ℝ (W r) ψ) (Icc u R))
    (hderiv : ∀ ψ ∈ D, ∀ r ∈ Ioo u R,
      HasDerivAt (fun s => inner ℝ (W s) ψ) (d r ψ) r)
    (hbound : ∀ ψ ∈ D, ∀ r ∈ Ioo u R,
      |d r ψ| ≤ (ell + a * r) * G * ‖ψ‖) :
    ‖W R - W u‖ ≤ (ell * (R - u) + a * (R ^ 2 - u ^ 2) / 2) * G := by
  have hi := norm_sub_le_integral_of_dense_pairings W D hD d
    (fun r => (ell + a * r) * G) huR hcont hderiv hbound
    (fun r hr => mul_nonneg (add_nonneg hell (mul_nonneg ha (hu.trans hr.1))) hG)
    ((continuous_const.add (continuous_const.mul continuous_id)).mul
      continuous_const |>.intervalIntegrable u R)
  have hint : (∫ r in u..R, (ell + a * r) * G) =
      (ell * (R - u) + a * (R ^ 2 - u ^ 2) / 2) * G := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_add (f := fun _ : ℝ => ell) (g := fun r : ℝ => a * r)
        (intervalIntegrable_const)
        (continuous_const.mul continuous_id |>.intervalIntegrable u R),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    ring
  exact hi.trans_eq hint

end AcceleratedLogConcave.Analysis.Poisson
