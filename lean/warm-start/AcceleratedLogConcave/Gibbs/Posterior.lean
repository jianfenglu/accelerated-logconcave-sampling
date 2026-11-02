import AcceleratedLogConcave.Gibbs.Normalization
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Gaussian-regularized Gibbs normalization

The posterior density is proportional to
`exp (-(F x + ‖x - y‖² / (2 * t)))`. The quadratic regularizer makes its
partition function finite for `t > 0`, even when the base curvature is zero
and the unregularized Gibbs density has infinite integral.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal ContDiff

namespace AcceleratedLogConcave.Gibbs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasFDerivAt_gaussian_regularizer (t : ℝ) (y x : E) :
    HasFDerivAt (fun z : E ↦ ‖z - y‖ ^ 2 / (2 * t))
      (t⁻¹ • innerSL ℝ (x - y)) x := by
  convert! (((hasFDerivAt_id x).sub_const y).norm_sq).mul_const ((2 * t)⁻¹) using 1
  ext v
  simp
  ring

theorem fderiv_gaussian_regularizer (t : ℝ) (y : E) :
    fderiv ℝ (fun z : E ↦ ‖z - y‖ ^ 2 / (2 * t)) =
      fun x ↦ t⁻¹ • innerSL ℝ (x - y) :=
  funext fun x ↦ (hasFDerivAt_gaussian_regularizer t y x).fderiv

theorem hasFDerivAt_gaussian_regularizer_gradient (t : ℝ) (y x : E) :
    HasFDerivAt (fun z : E ↦ t⁻¹ • innerSL ℝ (z - y))
      (t⁻¹ • innerSL ℝ (E := E)) x := by
  convert! (((innerSL ℝ (E := E)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const y)).const_smul t⁻¹) using 1

theorem contDiff_posterior_potential {F : E → ℝ} {n : ℕ∞ω}
    (hF : ContDiff ℝ n F) (t : ℝ) (y : E) :
    ContDiff ℝ n (fun x ↦ F x + ‖x - y‖ ^ 2 / (2 * t)) :=
  hF.add (((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const (2 * t))

theorem posterior_hessian_quadratic {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (t : ℝ) (y x v : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ F z + ‖z - y‖ ^ 2 / (2 * t))) x v v =
      fderiv ℝ (fderiv ℝ F) x v v + t⁻¹ * ‖v‖ ^ 2 := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hFdd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun z ↦ F z + ‖z - y‖ ^ 2 / (2 * t)) =
      fun z ↦ fderiv ℝ F z + t⁻¹ • innerSL ℝ (z - y) := by
    ext z w
    rw [fderiv_fun_add (hFd z) (hasFDerivAt_gaussian_regularizer t y z).differentiableAt,
      fderiv_gaussian_regularizer]
  rw [heq, fderiv_fun_add (hFdd x)
    (hasFDerivAt_gaussian_regularizer_gradient t y x).differentiableAt,
    (hasFDerivAt_gaussian_regularizer_gradient t y x).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change fderiv ℝ (fderiv ℝ F) x v v + t⁻¹ * inner ℝ v v = _
  rw [real_inner_self_eq_norm_sq]

theorem posterior_hessian_lower {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (t : ℝ) (y : E) :
    ∀ x v, (m + t⁻¹) * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (fun z ↦ F z + ‖z - y‖ ^ 2 / (2 * t))) x v v := by
  intro x v
  rw [posterior_hessian_quadratic hF]
  nlinarith [hH x v]

/-- An upper curvature bound shifts by the same Gaussian precision. -/
theorem posterior_hessian_upper {F : E → ℝ} {L : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hH : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ L * ‖v‖ ^ 2)
    (t : ℝ) (y : E) :
    ∀ x v, fderiv ℝ (fderiv ℝ (fun z ↦ F z + ‖z - y‖ ^ 2 / (2 * t))) x v v ≤
      (L + t⁻¹) * ‖v‖ ^ 2 := by
  intro x v
  rw [posterior_hessian_quadratic hF]
  nlinarith [hH x v]

theorem posterior_quadratic_lower_bound {F : E → ℝ} {a m t : ℝ} (b y : E)
    (hlower : ∀ x, a + ⟪b, x⟫ + m / 2 * ‖x‖ ^ 2 ≤ F x) :
    ∀ x, (a + ‖y‖ ^ 2 / (2 * t)) + ⟪b - t⁻¹ • y, x⟫ +
      (m / 2 + 1 / (2 * t)) * ‖x‖ ^ 2 ≤ F x + ‖x - y‖ ^ 2 / (2 * t) := by
  intro x
  rw [inner_sub_left, real_inner_smul_left, norm_sub_sq_real, real_inner_comm x y]
  have h := hlower x
  have heq : (a + ‖y‖ ^ 2 / (2 * t)) + (⟪b, x⟫ - t⁻¹ * ⟪x, y⟫) +
      (m / 2 + 1 / (2 * t)) * ‖x‖ ^ 2 =
      (a + ⟪b, x⟫ + m / 2 * ‖x‖ ^ 2) +
        (‖x‖ ^ 2 - 2 * ⟪x, y⟫ + ‖y‖ ^ 2) / (2 * t) := by
    field_simp
    ring
  rw [heq]
  linarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_posterior_of_quadratic_lower_bound {F : E → ℝ}
    (hF : Measurable F) {a m t : ℝ} (b y : E) (hm : 0 ≤ m) (ht : 0 < t)
    (hlower : ∀ x, a + ⟪b, x⟫ + m / 2 * ‖x‖ ^ 2 ≤ F x) :
    Integrable (fun x ↦ Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) := by
  refine integrable_exp_neg_of_quadratic_lower_bound
    (hF.add (by fun_prop)) (b - t⁻¹ • y) ?_
    (posterior_quadratic_lower_bound b y hlower)
  positivity

theorem integrable_posterior_of_affine_lower_bound {F : E → ℝ}
    (hF : Measurable F) {a t : ℝ} (b y : E) (ht : 0 < t)
    (hlower : ∀ x, a + ⟪b, x⟫ ≤ F x) :
    Integrable (fun x ↦ Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) := by
  apply integrable_posterior_of_quadratic_lower_bound hF b y (m := 0) le_rfl ht
  simpa using hlower

/-- Posterior integrability from nonnegative base curvature. In particular,
`m = 0` does not require a normalizable unregularized Gibbs measure. -/
theorem integrable_posterior_of_hessian_lower {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t) (y : E)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    Integrable (fun x ↦ Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) := by
  apply integrable_posterior_of_quadratic_lower_bound hF.continuous.measurable
    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F 0)) y hm ht (a := F 0)
  intro x
  simpa only [InnerProductSpace.toDual_symm_apply] using
    quadratic_lower_bound_of_hessian_lower hF hH x

/-- The Gaussian posterior is a probability law, including zero base curvature. -/
theorem normalized_posterior_isProbabilityMeasure_of_hessian_lower
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t) (y : E)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    IsProbabilityMeasure
      ((∫⁻ x, ENNReal.ofReal (Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))))⁻¹ •
        volume.withDensity (fun x ↦
          ENNReal.ofReal (Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))))) :=
  normalized_exp_neg_isProbabilityMeasure
    (integrable_posterior_of_hessian_lower hF hm ht y hH)

/-- The Gaussian-regularized density has every natural polynomial norm moment,
even when the base curvature is zero and its unregularized partition is infinite. -/
theorem integrable_norm_pow_mul_posterior_of_hessian_lower {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t) (y : E)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) (n : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ n * Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) := by
  have hlower : ∀ x, F 0 + ⟪(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F 0), x⟫ +
      m / 2 * ‖x‖ ^ 2 ≤ F x := by
    intro x
    simpa only [InnerProductSpace.toDual_symm_apply] using
      quadratic_lower_bound_of_hessian_lower hF hH x
  apply integrable_norm_pow_mul_exp_neg_of_quadratic_lower_bound
    (hF.continuous.measurable.add (by fun_prop))
    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F 0) - t⁻¹ • y)
    (by positivity : 0 < m / 2 + 1 / (2 * t))
    (posterior_quadratic_lower_bound _ y hlower) n

/-- A degree-two posterior density bound, valid at zero base curvature. -/
theorem integrable_one_add_norm_sq_mul_posterior_of_hessian_lower
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t) (y : E)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    Integrable (fun x ↦ (1 + ‖x‖ ^ 2) * Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) := by
  convert! (integrable_posterior_of_hessian_lower hF hm ht y hH).add
    (integrable_norm_pow_mul_posterior_of_hessian_lower hF hm ht y hH 2) using 1
  ext x
  simp [add_mul]

/-- Every natural norm moment of the normalized Gaussian posterior is finite.
This supplies its second moment at `n = 2` without any base-normalizability assumption. -/
theorem integrable_norm_pow_posterior_of_hessian_lower {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t) (y : E)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) (n : ℕ) :
    Integrable (fun x : E ↦ ‖x‖ ^ n)
      ((∫⁻ x, ENNReal.ofReal (Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))))⁻¹ •
        volume.withDensity (fun x ↦
          ENNReal.ofReal (Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))))) :=
  integrable_norm_pow_normalized_of_weighted_integrable
    (hF.continuous.measurable.add (by fun_prop))
    (integrable_posterior_of_hessian_lower hF hm ht y hH) n
    (integrable_norm_pow_mul_posterior_of_hessian_lower hF hm ht y hH n)

end AcceleratedLogConcave.Gibbs
