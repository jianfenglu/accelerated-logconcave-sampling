import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Gibbs normalization

The analytic entry point derives a quadratic lower bound from a `C²` Hessian
lower bound, then compares the Gibbs density with an integrable affine Gaussian.
The normalization lemmas make positivity and finiteness explicit; they do not
turn an arbitrary nonintegrable Gibbs density into a probability measure.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace AcceleratedLogConcave.Gibbs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 800000 in
theorem quadratic_lower_bound_of_hessian_lower {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) (x : E) :
    F 0 + fderiv ℝ F 0 x + m / 2 * ‖x‖ ^ 2 ≤ F x := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hFdd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  let g : ℝ → ℝ := fun s ↦ F (s • x) - (m / 2 * ‖x‖ ^ 2) * s ^ 2
  let g' : ℝ → ℝ := fun s ↦ fderiv ℝ F (s • x) x - (m * ‖x‖ ^ 2) * s
  let g'' : ℝ → ℝ := fun s ↦ fderiv ℝ (fderiv ℝ F) (s • x) x x - m * ‖x‖ ^ 2
  have hd (s : ℝ) : HasDerivAt g (g' s) s := by
    have hf := (hFd (s • x)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const x)
    convert hf.sub (((hasDerivAt_id s).pow 2).const_mul (m / 2 * ‖x‖ ^ 2)) using 1
    · rfl
    · dsimp [g']
      simp only [one_smul]
      ring
  have hdd (s : ℝ) : HasDerivAt g' (g'' s) s := by
    have hf := ((hFdd (s • x)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const x)).clm_apply (hasDerivAt_const s x)
    convert! hf.sub ((hasDerivAt_id s).const_mul (m * ‖x‖ ^ 2)) using 1
    simp [g'']
  have hc : ConvexOn ℝ univ g :=
    convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (continuous_iff_continuousAt.mpr (fun s ↦ (hd s).continuousAt)).continuousOn
      (fun s _ ↦ (hd s).hasDerivWithinAt)
      (fun s _ ↦ (hdd s).hasDerivWithinAt)
      (fun s _ ↦ sub_nonneg.mpr (hH (s • x) x))
  have h := hc.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (by norm_num) (hd 0)
  simp [g, g', slope] at h
  linarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_exp_quadratic_affine {c : ℝ} (hc : 0 < c) (b : E) :
    Integrable (fun x : E ↦ Real.exp (-c * ‖x‖ ^ 2 - ⟪b, x⟫)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := (c : ℂ)) (by simpa using hc) (-1) b).norm
  simpa [Complex.norm_exp, sub_eq_add_neg, ← Complex.ofReal_pow] using h

theorem integrable_exp_neg_of_quadratic_lower_bound {F : E → ℝ}
    (hF : Measurable F) {a c : ℝ} (b : E) (hc : 0 < c)
    (hlower : ∀ x, a + ⟪b, x⟫ + c * ‖x‖ ^ 2 ≤ F x) :
    Integrable (fun x ↦ Real.exp (-F x)) := by
  refine ((integrable_exp_quadratic_affine hc b).const_mul (Real.exp (-a))).mono'
    hF.neg.exp.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [hlower x]

theorem lintegral_exp_neg_ne_top {F : E → ℝ}
    (hF : Integrable (fun x ↦ Real.exp (-F x))) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-F x))) ≠ ⊤ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hF]
  · exact ENNReal.ofReal_ne_top
  · exact Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le

theorem lintegral_exp_neg_pos {F : E → ℝ}
    (hF : Integrable (fun x ↦ Real.exp (-F x))) :
    0 < ∫⁻ x, ENNReal.ofReal (Real.exp (-F x)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hF]
  · exact ENNReal.ofReal_pos.mpr (integral_exp_pos hF)
  · exact Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le

theorem normalized_exp_neg_isProbabilityMeasure {F : E → ℝ}
    (hF : Integrable (fun x ↦ Real.exp (-F x))) :
    IsProbabilityMeasure
      ((∫⁻ x, ENNReal.ofReal (Real.exp (-F x)))⁻¹ •
        volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-F x)))) := by
  constructor
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (lintegral_exp_neg_pos hF).ne' (lintegral_exp_neg_ne_top hF)

/-- A strictly positive Hessian lower bound suffices for Gibbs integrability.
No upper Hessian bound or prior normalizability hypothesis is needed. -/
theorem integrable_exp_neg_of_hessian_lower {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    Integrable (fun x ↦ Real.exp (-F x)) := by
  apply integrable_exp_neg_of_quadratic_lower_bound hF.continuous.measurable
    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F 0)) (a := F 0)
    (c := m / 2) (by positivity)
  intro x
  simpa only [InnerProductSpace.toDual_symm_apply] using
    quadratic_lower_bound_of_hessian_lower hF hH x

/-- The normalized Gibbs law is a probability law under the manuscript's
strictly positive curvature assumption. -/
theorem normalized_exp_neg_isProbabilityMeasure_of_hessian_lower
    {F : E → ℝ} {m : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 < m)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    IsProbabilityMeasure
      ((∫⁻ x, ENNReal.ofReal (Real.exp (-F x)))⁻¹ •
        volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-F x)))) :=
  normalized_exp_neg_isProbabilityMeasure (integrable_exp_neg_of_hessian_lower hF hm hH)

theorem integrable_norm_pow_mul_exp_neg_of_quadratic_lower_bound {F : E → ℝ}
    (hF : Measurable F) {a c : ℝ} (b : E) (hc : 0 < c)
    (hlower : ∀ x, a + ⟪b, x⟫ + c * ‖x‖ ^ 2 ≤ F x) (n : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ n * Real.exp (-F x)) := by
  have hdom := (integrable_exp_quadratic_affine (by positivity : 0 < c / 2) b).const_mul
    ((n.factorial : ℝ) * Real.exp (-a + 1 / (2 * c)))
  refine hdom.mono' (by fun_prop) ?_
  filter_upwards [] with x
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hpow : ‖x‖ ^ n ≤ (n.factorial : ℝ) * Real.exp ‖x‖ := by
    have h := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) n)
    simpa [mul_comm] using h
  have hyoung : ‖x‖ ≤ c / 2 * ‖x‖ ^ 2 + 1 / (2 * c) := by
    have heq : c / 2 * ‖x‖ ^ 2 + 1 / (2 * c) - ‖x‖ =
        (c * ‖x‖ - 1) ^ 2 / (2 * c) := by
      field_simp
      ring
    rw [← sub_nonneg, heq]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ‖x‖ ^ n * Real.exp (-F x)
        ≤ ((n.factorial : ℝ) * Real.exp ‖x‖) * Real.exp (-F x) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * Real.exp (‖x‖ - F x) := by
      rw [mul_assoc, ← Real.exp_add]
      rfl
    _ ≤ (n.factorial : ℝ) * Real.exp
        ((-a + 1 / (2 * c)) + (-c / 2 * ‖x‖ ^ 2 - ⟪b, x⟫)) := by
      gcongr
      linarith [hlower x]
    _ = ((n.factorial : ℝ) * Real.exp (-a + 1 / (2 * c))) *
        Real.exp (-(c / 2) * ‖x‖ ^ 2 - ⟪b, x⟫) := by
      rw [Real.exp_add, mul_assoc]
      congr 2
      ring

theorem integrable_one_add_norm_sq_mul_exp_neg_of_quadratic_lower_bound {F : E → ℝ}
    (hF : Measurable F) {a c : ℝ} (b : E) (hc : 0 < c)
    (hlower : ∀ x, a + ⟪b, x⟫ + c * ‖x‖ ^ 2 ≤ F x) :
    Integrable (fun x ↦ (1 + ‖x‖ ^ 2) * Real.exp (-F x)) := by
  convert!
    (integrable_exp_neg_of_quadratic_lower_bound hF b hc hlower).add
      (integrable_norm_pow_mul_exp_neg_of_quadratic_lower_bound hF b hc hlower 2) using 1
  ext x
  simp [add_mul]

theorem integrable_norm_pow_normalized_of_weighted_integrable {F : E → ℝ}
    (hF : Measurable F) (hZ : Integrable (fun x ↦ Real.exp (-F x))) (n : ℕ)
    (hn : Integrable (fun x ↦ ‖x‖ ^ n * Real.exp (-F x))) :
    Integrable (fun x : E ↦ ‖x‖ ^ n)
      ((∫⁻ x, ENNReal.ofReal (Real.exp (-F x)))⁻¹ •
        volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-F x)))) := by
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (lintegral_exp_neg_pos hZ).ne')
  apply (integrable_withDensity_iff_integrable_smul'
    hF.neg.exp.ennreal_ofReal (by simp)).mpr
  simpa [ENNReal.toReal_ofReal, (Real.exp_pos _).le, smul_eq_mul, mul_comm] using hn

/-- Every natural polynomial norm moment is integrable against the unnormalized
Gibbs density under a positive Hessian lower bound. -/
theorem integrable_norm_pow_mul_exp_neg_of_hessian_lower {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) (n : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ n * Real.exp (-F x)) := by
  apply integrable_norm_pow_mul_exp_neg_of_quadratic_lower_bound hF.continuous.measurable
    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F 0)) (a := F 0)
    (c := m / 2) (by positivity) _ n
  intro x
  simpa only [InnerProductSpace.toDual_symm_apply] using
    quadratic_lower_bound_of_hessian_lower hF hH x

/-- A convenient degree-two weighted-density bound for integration by parts. -/
theorem integrable_one_add_norm_sq_mul_exp_neg_of_hessian_lower {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    Integrable (fun x ↦ (1 + ‖x‖ ^ 2) * Real.exp (-F x)) := by
  convert! (integrable_exp_neg_of_hessian_lower hF hm hH).add
    (integrable_norm_pow_mul_exp_neg_of_hessian_lower hF hm hH 2) using 1
  ext x
  simp [add_mul]

/-- All natural norm moments of the actual normalized Gibbs law are finite.
Take `n = 2` for the normalized second moment. -/
theorem integrable_norm_pow_normalized_of_hessian_lower {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 < m)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) (n : ℕ) :
    Integrable (fun x : E ↦ ‖x‖ ^ n)
      ((∫⁻ x, ENNReal.ofReal (Real.exp (-F x)))⁻¹ •
        volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-F x)))) :=
  integrable_norm_pow_normalized_of_weighted_integrable hF.continuous.measurable
    (integrable_exp_neg_of_hessian_lower hF hm hH) n
    (integrable_norm_pow_mul_exp_neg_of_hessian_lower hF hm hH n)

end AcceleratedLogConcave.Gibbs
