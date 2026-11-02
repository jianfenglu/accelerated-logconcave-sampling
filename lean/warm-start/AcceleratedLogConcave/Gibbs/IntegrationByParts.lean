import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.InnerProductSpace.PiL2
import AcceleratedLogConcave.External.Samplinglib.TechnicalLemmas.Analysis.HessianSecantOperator

/-!
# Gibbs integration by parts

These are original proofs from Mathlib's whole-space integration-by-parts theorem.
The three integrability conditions below are the boundary hypotheses; compact `C¹`
tests discharge them automatically. Score second-moment identities use only `C²`
regularity of the potential, with their integrability obligations stated explicitly.
-/

noncomputable section

open MeasureTheory

namespace AcceleratedLogConcave.Gibbs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the unnormalized Gibbs density in a fixed direction. -/
theorem fderiv_exp_neg_apply {V : E → ℝ} (hV : Differentiable ℝ V) (x v : E) :
    fderiv ℝ (fun y ↦ Real.exp (-V y)) x v =
      -(Real.exp (-V x) * fderiv ℝ V x v) := by
  simpa using congrArg (fun L : E →L[ℝ] ℝ ↦ L v)
    ((hV x).hasFDerivAt.neg.exp).fderiv

/-- Whole-space Gibbs integration by parts, with explicit integrability conditions.
The hypotheses on the products replace a separate boundary-limit hypothesis. -/
theorem integral_exp_neg_mul_fderiv {V f : E → ℝ} (v : E)
    (hV : Differentiable ℝ V) (hf : Differentiable ℝ f)
    (hscore : Integrable (fun x ↦ Real.exp (-V x) * fderiv ℝ V x v * f x) μ)
    (hderiv : Integrable (fun x ↦ Real.exp (-V x) * fderiv ℝ f x v) μ)
    (hfun : Integrable (fun x ↦ Real.exp (-V x) * f x) μ) :
    ∫ x, Real.exp (-V x) * fderiv ℝ f x v ∂μ =
      ∫ x, Real.exp (-V x) * fderiv ℝ V x v * f x ∂μ := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun x ↦ Real.exp (-V x)) (g := f) (v := v)
    (hscore.neg.congr (Filter.Eventually.of_forall (fun x ↦ by
      simp only [Pi.neg_apply, fderiv_exp_neg_apply hV, neg_mul])))
    hderiv hfun (fun x _ ↦ (hV x).neg.exp) (fun x _ ↦ hf x)
  simpa only [fderiv_exp_neg_apply hV, neg_mul, integral_neg, neg_neg] using h

/-- Compact `C¹` tests satisfy all boundary and integrability conditions. -/
theorem integral_exp_neg_mul_fderiv_of_hasCompactSupport {V f : E → ℝ} (v : E)
    (hV : ContDiff ℝ 1 V) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∫ x, Real.exp (-V x) * fderiv ℝ f x v ∂μ =
      ∫ x, Real.exp (-V x) * fderiv ℝ V x v * f x ∂μ := by
  apply integral_exp_neg_mul_fderiv v (hV.differentiable one_ne_zero)
    (hf.differentiable one_ne_zero)
  · exact (((Real.continuous_exp.comp hV.continuous.neg).mul
      ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const)).mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left
  · exact ((Real.continuous_exp.comp hV.continuous.neg).mul
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ v).mul_left
  · exact ((Real.continuous_exp.comp hV.continuous.neg).mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left

/-- Normalization by a constant preserves the integration-by-parts identity.
Choosing `Z` to be the partition function gives the normalized-density formula. -/
theorem integral_normalized_exp_neg_mul_fderiv {V f : E → ℝ} (v : E) (Z : ℝ)
    (hV : Differentiable ℝ V) (hf : Differentiable ℝ f)
    (hscore : Integrable (fun x ↦ Real.exp (-V x) * fderiv ℝ V x v * f x) μ)
    (hderiv : Integrable (fun x ↦ Real.exp (-V x) * fderiv ℝ f x v) μ)
    (hfun : Integrable (fun x ↦ Real.exp (-V x) * f x) μ) :
    ∫ x, (Z⁻¹ * Real.exp (-V x)) * fderiv ℝ f x v ∂μ =
      ∫ x, (Z⁻¹ * Real.exp (-V x)) * fderiv ℝ V x v * f x ∂μ := by
  simp only [mul_assoc, integral_const_mul]
  exact congrArg (Z⁻¹ * ·) (by
    simpa only [mul_assoc] using integral_exp_neg_mul_fderiv v hV hf hscore hderiv hfun)

/-- The score has mean zero whenever its weighted absolute integrability and
normalizability are known. These hypotheses are explicitly separate from the conclusion. -/
theorem integral_exp_neg_mul_score_eq_zero {V : E → ℝ} (v : E)
    (hV : Differentiable ℝ V) (hZ : Integrable (fun x ↦ Real.exp (-V x)) μ)
    (hscore : Integrable (fun x ↦ Real.exp (-V x) * fderiv ℝ V x v) μ) :
    ∫ x, Real.exp (-V x) * fderiv ℝ V x v ∂μ = 0 := by
  have h := integral_exp_neg_mul_fderiv (f := fun _ ↦ 1) v hV
    (differentiable_const 1) (by simpa using hscore) (by simp) (by simpa using hZ)
  simpa using h.symm

/-- Integration by parts for the actual exponentially tilted measure. -/
theorem integral_tilted_fderiv {V f : E → ℝ} (v : E)
    (hV : Differentiable ℝ V) (hf : Differentiable ℝ f)
    (hZ : Integrable (fun x ↦ Real.exp (-V x)) μ)
    (hscore : Integrable (fun x ↦ fderiv ℝ V x v * f x) (μ.tilted (fun x ↦ -V x)))
    (hderiv : Integrable (fun x ↦ fderiv ℝ f x v) (μ.tilted (fun x ↦ -V x)))
    (hfun : Integrable f (μ.tilted (fun x ↦ -V x))) :
    ∫ x, fderiv ℝ f x v ∂(μ.tilted (fun x ↦ -V x)) =
      ∫ x, fderiv ℝ V x v * f x ∂(μ.tilted (fun x ↦ -V x)) := by
  have hs := (integrable_tilted_iff hZ _).mp hscore
  have hd := (integrable_tilted_iff hZ _).mp hderiv
  have hf' := (integrable_tilted_iff hZ _).mp hfun
  simp only [smul_eq_mul] at hs hd hf'
  simp only [integral_tilted, smul_eq_mul, div_eq_mul_inv, mul_comm _ (∫ x, Real.exp (-V x) ∂μ)⁻¹]
  simpa only [mul_assoc] using
    integral_normalized_exp_neg_mul_fderiv v (∫ x, Real.exp (-V x) ∂μ) hV hf
      (by simpa only [mul_assoc] using hs) hd hf'

/-- Compact `C¹` integration by parts under the exponentially tilted law.
If the partition function is integrable, this law is a probability measure. -/
theorem integral_tilted_fderiv_of_hasCompactSupport {V f : E → ℝ} (v : E)
    (hV : ContDiff ℝ 1 V) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∫ x, fderiv ℝ f x v ∂(μ.tilted (fun x ↦ -V x)) =
      ∫ x, fderiv ℝ V x v * f x ∂(μ.tilted (fun x ↦ -V x)) := by
  simp only [integral_tilted, smul_eq_mul, div_eq_mul_inv,
    mul_comm _ (∫ x, Real.exp (-V x) ∂μ)⁻¹, mul_assoc, integral_const_mul]
  exact congrArg ((∫ x, Real.exp (-V x) ∂μ)⁻¹ * ·) (by
    simpa only [mul_assoc] using
      integral_exp_neg_mul_fderiv_of_hasCompactSupport (μ := μ) v hV hf hfc)

/-- Mean-zero score under the normalized Gibbs law, once the score is integrable. -/
theorem integral_tilted_score_eq_zero {V : E → ℝ} (v : E)
    (hV : Differentiable ℝ V) (hZ : Integrable (fun x ↦ Real.exp (-V x)) μ)
    (hscore : Integrable (fun x ↦ fderiv ℝ V x v) (μ.tilted (fun x ↦ -V x))) :
    ∫ x, fderiv ℝ V x v ∂(μ.tilted (fun x ↦ -V x)) = 0 := by
  have h := integral_tilted_fderiv (f := fun _ ↦ 1) v hV
    (differentiable_const 1) hZ (by simpa using hscore)
    (by simp) (integrable_const 1)
  simpa using h.symm

/-- The mixed score moment equals the expected directional Hessian.
Only `C²` regularity is used. All three analytic integrability obligations are
explicit; deriving them from curvature and Gaussian tails is a separate step. -/
theorem integral_tilted_score_mul_eq_hessian {V : E → ℝ} (v w : E)
    (hV : ContDiff ℝ 2 V) (hZ : Integrable (fun x ↦ Real.exp (-V x)) μ)
    (hscore : Integrable (fun x ↦ fderiv ℝ V x w * fderiv ℝ V x v)
      (μ.tilted (fun x ↦ -V x)))
    (hhessian : Integrable (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ V y v) x w)
      (μ.tilted (fun x ↦ -V x)))
    (hfirst : Integrable (fun x ↦ fderiv ℝ V x v) (μ.tilted (fun x ↦ -V x))) :
    ∫ x, fderiv ℝ V x w * fderiv ℝ V x v ∂(μ.tilted (fun x ↦ -V x)) =
      ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ V y v) x w ∂(μ.tilted (fun x ↦ -V x)) := by
  have hfirstDiff : ContDiff ℝ 1 (fun x ↦ fderiv ℝ V x v) :=
    (hV.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const
  exact (integral_tilted_fderiv w (hV.differentiable (by norm_num))
    (hfirstDiff.differentiable one_ne_zero) hZ hscore hhessian hfirst).symm

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- A finite score second moment implies score integrability under the tilted law.
This discharges the first-moment boundary condition in the second-moment identity. -/
theorem integrable_tilted_score_of_integrable_sq {V : E → ℝ} (v : E)
    (hV : ContDiff ℝ 1 V)
    (hsecond : Integrable (fun x ↦ (fderiv ℝ V x v) ^ 2) (μ.tilted (fun x ↦ -V x))) :
    Integrable (fun x ↦ fderiv ℝ V x v) (μ.tilted (fun x ↦ -V x)) := by
  refine (hsecond.add (integrable_const 1)).mono' ?_ ?_
  · exact ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  · filter_upwards [] with x
    simp only [Real.norm_eq_abs, Pi.add_apply]
    nlinarith [sq_nonneg (|fderiv ℝ V x v| - 1), sq_abs (fderiv ℝ V x v)]

/-- The score second moment equals the expected second directional derivative.
The lower-order score integrability is derived from the second moment. -/
theorem integral_tilted_score_sq_eq_hessian {V : E → ℝ} (v : E)
    (hV : ContDiff ℝ 2 V) (hZ : Integrable (fun x ↦ Real.exp (-V x)) μ)
    (hsecond : Integrable (fun x ↦ (fderiv ℝ V x v) ^ 2) (μ.tilted (fun x ↦ -V x)))
    (hhessian : Integrable (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ V y v) x v)
      (μ.tilted (fun x ↦ -V x))) :
    ∫ x, (fderiv ℝ V x v) ^ 2 ∂(μ.tilted (fun x ↦ -V x)) =
      ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ V y v) x v ∂(μ.tilted (fun x ↦ -V x)) := by
  simpa only [pow_two] using integral_tilted_score_mul_eq_hessian v v hV hZ
    (by simpa only [pow_two] using hsecond) hhessian
    (integrable_tilted_score_of_integrable_sq v (hV.of_le (by norm_num)) hsecond)

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] [NormedSpace ℝ E] in
/-- A second position moment controls the second moment of every continuous
function with an affine growth bound. -/
theorem integrable_tilted_norm_sq_of_affine_bound {F : Type*} [NormedAddCommGroup F]
    {V : E → ℝ} {f : E → F} (hf : Continuous f) (A B : ℝ)
    (hbound : ∀ x, ‖f x‖ ≤ A + B * ‖x‖)
    (hposition : Integrable (fun x : E ↦ ‖x‖ ^ 2) (μ.tilted (fun x ↦ -V x))) :
    Integrable (fun x ↦ ‖f x‖ ^ 2) (μ.tilted (fun x ↦ -V x)) := by
  refine ((integrable_const (2 * A ^ 2)).add (hposition.const_mul (2 * B ^ 2))).mono'
    (hf.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [] with x
  simp only [Real.norm_eq_abs, abs_pow, abs_norm, Pi.add_apply]
  have hb := mul_self_le_mul_self (norm_nonneg (f x)) (hbound x)
  nlinarith [sq_nonneg (A - B * ‖x‖)]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  {ν : Measure H} [ν.IsAddHaarMeasure]

omit [MeasurableSpace H] [BorelSpace H] in
/-- The actual two-sided Hessian bounds imply affine growth of the gradient.
The segment operator comes from the explicitly attributed local Samplinglib port. -/
theorem norm_gradient_le_affine_of_hessian_bounds {V : H → ℝ} {m L : ℝ}
    (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ L * ‖v‖ ^ 2) (x : H) :
    ‖gradient V x‖ ≤ ‖gradient V 0‖ + max |m| |L| * ‖x‖ := by
  obtain ⟨_, heq, _, _, hnorm⟩ :=
    AutoSamplingTheory.TechnicalLemmas.Analysis.HessianSecantOperator.hessian_secant_operator
      hV hlo hup x 0
  have hd : ‖gradient V x - gradient V 0‖ ≤ max |m| |L| * ‖x‖ := by
    rw [heq]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      simpa only [sub_zero] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg x))
  calc
    ‖gradient V x‖ = ‖gradient V 0 + (gradient V x - gradient V 0)‖ := by
      congr 1
      abel
    _ ≤ ‖gradient V 0‖ + ‖gradient V x - gradient V 0‖ := norm_add_le _ _
    _ ≤ _ := add_le_add_right hd _

omit [ν.IsAddHaarMeasure] in
/-- Curvature bounds and the normalized second position moment discharge the
score-square integrability obligation. No score integrability is assumed. -/
theorem integrable_tilted_gradient_norm_sq_of_hessian_bounds {V : H → ℝ} {m L : ℝ}
    (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ L * ‖v‖ ^ 2)
    (hposition : Integrable (fun x : H ↦ ‖x‖ ^ 2) (ν.tilted (fun x ↦ -V x))) :
    Integrable (fun x ↦ ‖gradient V x‖ ^ 2) (ν.tilted (fun x ↦ -V x)) := by
  apply integrable_tilted_norm_sq_of_affine_bound ?_ ‖gradient V 0‖ (max |m| |L|)
    (norm_gradient_le_affine_of_hessian_bounds hV hlo hup) hposition
  exact (InnerProductSpace.toDual ℝ H).symm.continuous.comp
    (hV.continuous_fderiv (by norm_num))

omit [ν.IsAddHaarMeasure] in
/-- The score itself is integrable from the same curvature and position-moment data. -/
theorem integrable_tilted_gradient_of_hessian_bounds {V : H → ℝ} {m L : ℝ}
    (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ L * ‖v‖ ^ 2)
    (hposition : Integrable (fun x : H ↦ ‖x‖ ^ 2) (ν.tilted (fun x ↦ -V x))) :
    Integrable (gradient V) (ν.tilted (fun x ↦ -V x)) := by
  have hs := integrable_tilted_gradient_norm_sq_of_hessian_bounds hV hlo hup hposition
  refine (hs.add (integrable_const 1)).mono' ?_ ?_
  · exact ((InnerProductSpace.toDual ℝ H).symm.continuous.comp
      (hV.continuous_fderiv (by norm_num))).aestronglyMeasurable
  · filter_upwards [] with x
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖gradient V x‖ - 1)]

/-- The vector score has mean zero; its integrability follows from curvature and
an actual second position moment of the normalized law. -/
theorem integral_tilted_gradient_eq_zero_of_hessian_bounds {V : H → ℝ} {m L : ℝ}
    (hV : ContDiff ℝ 2 V) (hZ : Integrable (fun x ↦ Real.exp (-V x)) ν)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ L * ‖v‖ ^ 2)
    (hposition : Integrable (fun x : H ↦ ‖x‖ ^ 2) (ν.tilted (fun x ↦ -V x))) :
    ∫ x, gradient V x ∂(ν.tilted (fun x ↦ -V x)) = 0 := by
  have hg := integrable_tilted_gradient_of_hessian_bounds hV hlo hup hposition
  apply ext_inner_left ℝ
  intro v
  have hs : Integrable (fun x ↦ fderiv ℝ V x v) (ν.tilted (fun x ↦ -V x)) := by
    simpa only [innerSL_apply_apply, inner_gradient_right, conj_trivial] using
      (innerSL ℝ v).integrable_comp hg
  have hi := integral_tilted_score_eq_zero v (hV.differentiable (by norm_num)) hZ hs
  have hc := (innerSL ℝ v).integral_comp_comm hg
  simp only [innerSL_apply_apply, inner_gradient_right, conj_trivial] at hc
  simpa only [inner_zero_right] using hc.symm.trans hi

omit [ν.IsAddHaarMeasure] in
/-- Each directional score has a finite second moment from the position moment. -/
theorem integrable_tilted_directional_score_sq_of_hessian_bounds {V : H → ℝ} {m L : ℝ}
    (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ L * ‖v‖ ^ 2)
    (hposition : Integrable (fun x : H ↦ ‖x‖ ^ 2) (ν.tilted (fun x ↦ -V x))) (v : H) :
    Integrable (fun x ↦ (fderiv ℝ V x v) ^ 2) (ν.tilted (fun x ↦ -V x)) := by
  have hg := integrable_tilted_gradient_norm_sq_of_hessian_bounds hV hlo hup hposition
  refine (hg.mul_const (‖v‖ ^ 2)).mono' ?_ ?_
  · exact (((hV.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).aestronglyMeasurable
  · filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    have hc := real_inner_mul_inner_self_le (gradient V x) v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, inner_gradient_left] at hc
    simpa only [pow_two] using hc

omit [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ H] in
/-- Evaluating the derivative of a directional score gives the genuine Hessian. -/
theorem fderiv_directional_score_apply {V : H → ℝ} (hV : ContDiff ℝ 2 V) (x v w : H) :
    fderiv ℝ (fun y ↦ fderiv ℝ V y v) x w = (fderiv ℝ (fderiv ℝ V) x w) v := by
  have hd : Differentiable ℝ (fderiv ℝ V) :=
    (hV.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable one_ne_zero
  rw [fderiv_clm_apply (hd x) (differentiableAt_const v)]
  simp

omit [ν.IsAddHaarMeasure] [FiniteDimensional ℝ H] in
/-- Two-sided curvature bounds discharge the directional Hessian integrability. -/
theorem integrable_tilted_hessian_diagonal_of_hessian_bounds {V : H → ℝ} {m L : ℝ}
    (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ L * ‖v‖ ^ 2) (v : H) :
    Integrable (fun x ↦ (fderiv ℝ (fderiv ℝ V) x v) v) (ν.tilted (fun x ↦ -V x)) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  refine (integrable_const (max |m| |L| * ‖v‖ ^ 2)).mono' ?_ ?_
  · exact (((hfd.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_le]
    have hl := mul_le_mul_of_nonneg_right
      ((neg_le_abs m).trans (le_max_left |m| |L|)) (sq_nonneg ‖v‖)
    have hu := mul_le_mul_of_nonneg_right
      ((le_abs_self L).trans (le_max_right |m| |L|)) (sq_nonneg ‖v‖)
    constructor <;> nlinarith [hlo x v, hup x v]

/-- Directional score/Hessian identity with every score and Hessian
integrability obligation discharged by curvature and a second position moment. -/
theorem integral_tilted_directional_score_sq_eq_hessian_of_hessian_bounds
    {V : H → ℝ} {m L : ℝ} (hV : ContDiff ℝ 2 V)
    (hZ : Integrable (fun x ↦ Real.exp (-V x)) ν)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ L * ‖v‖ ^ 2)
    (hposition : Integrable (fun x : H ↦ ‖x‖ ^ 2) (ν.tilted (fun x ↦ -V x))) (v : H) :
    ∫ x, (fderiv ℝ V x v) ^ 2 ∂(ν.tilted (fun x ↦ -V x)) =
      ∫ x, (fderiv ℝ (fderiv ℝ V) x v) v ∂(ν.tilted (fun x ↦ -V x)) := by
  simpa only [fderiv_directional_score_apply hV] using
    integral_tilted_score_sq_eq_hessian v hV hZ
      (integrable_tilted_directional_score_sq_of_hessian_bounds hV hlo hup hposition v)
      (by simpa only [fderiv_directional_score_apply hV] using
        integrable_tilted_hessian_diagonal_of_hessian_bounds (ν := ν) hV hlo hup v)

/-- The vector score second moment is the sum of the expected diagonal Hessian
entries in any finite orthonormal basis. -/
theorem integral_tilted_gradient_norm_sq_eq_sum_hessian {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ H) {V : H → ℝ} {m L : ℝ} (hV : ContDiff ℝ 2 V)
    (hZ : Integrable (fun x ↦ Real.exp (-V x)) ν)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ L * ‖v‖ ^ 2)
    (hposition : Integrable (fun x : H ↦ ‖x‖ ^ 2) (ν.tilted (fun x ↦ -V x))) :
    ∫ x, ‖gradient V x‖ ^ 2 ∂(ν.tilted (fun x ↦ -V x)) =
      ∑ i, ∫ x, (fderiv ℝ (fderiv ℝ V) x (b i)) (b i) ∂(ν.tilted (fun x ↦ -V x)) := by
  calc
    _ = ∫ x, ∑ i, (fderiv ℝ V x (b i)) ^ 2 ∂(ν.tilted (fun x ↦ -V x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simpa only [inner_gradient_left] using (b.sum_sq_inner_left (gradient V x)).symm
    _ = ∑ i, ∫ x, (fderiv ℝ V x (b i)) ^ 2 ∂(ν.tilted (fun x ↦ -V x)) := by
      exact integral_finsetSum _ (fun i _ ↦
        integrable_tilted_directional_score_sq_of_hessian_bounds hV hlo hup hposition (b i))
    _ = _ := Finset.sum_congr rfl (fun i _ ↦
      integral_tilted_directional_score_sq_eq_hessian_of_hessian_bounds
        hV hZ hlo hup hposition (b i))

/-- The manuscript's score moment bound: the upper Hessian bound times dimension.
Normalization and a finite second position moment remain the only tail inputs. -/
theorem integral_tilted_gradient_norm_sq_le_finrank_mul {V : H → ℝ} {m L : ℝ}
    (hV : ContDiff ℝ 2 V) (hZ : Integrable (fun x ↦ Real.exp (-V x)) ν)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ L * ‖v‖ ^ 2)
    (hposition : Integrable (fun x : H ↦ ‖x‖ ^ 2) (ν.tilted (fun x ↦ -V x))) :
    ∫ x, ‖gradient V x‖ ^ 2 ∂(ν.tilted (fun x ↦ -V x)) ≤ Module.finrank ℝ H * L := by
  let _ := isProbabilityMeasure_tilted hZ
  rw [integral_tilted_gradient_norm_sq_eq_sum_hessian (stdOrthonormalBasis ℝ H)
    hV hZ hlo hup hposition]
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ H), L := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∫ _x : H, L ∂(ν.tilted (fun x ↦ -V x)) := by
          apply integral_mono
            (integrable_tilted_hessian_diagonal_of_hessian_bounds hV hlo hup _)
            (integrable_const L)
          intro x
          simpa only [OrthonormalBasis.norm_eq_one, one_pow, mul_one] using
            hup x (stdOrthonormalBasis ℝ H i)
        _ = L := by simp
    _ = _ := by simp

/-- Score calculus for a supplied law identified with the normalized Gibbs law.
This accepts the equality proved by the ENNReal normalization bridge. The only
remaining tail inputs are density integrability and the law's position second moment. -/
theorem score_calculus_of_eq_tilted {V : H → ℝ} {m L : ℝ} (π : Measure H)
    (hπ : π = ν.tilted (fun x ↦ -V x)) (hV : ContDiff ℝ 2 V)
    (hZ : Integrable (fun x ↦ Real.exp (-V x)) ν)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ L * ‖v‖ ^ 2)
    (hposition : Integrable (fun x : H ↦ ‖x‖ ^ 2) π) :
    Integrable (gradient V) π ∧
      Integrable (fun x ↦ ‖gradient V x‖ ^ 2) π ∧
      (∫ x, gradient V x ∂π) = 0 ∧
      (∫ x, ‖gradient V x‖ ^ 2 ∂π) =
        ∑ i : Fin (Module.finrank ℝ H),
          ∫ x, (fderiv ℝ (fderiv ℝ V) x (stdOrthonormalBasis ℝ H i))
            (stdOrthonormalBasis ℝ H i) ∂π ∧
      (∫ x, ‖gradient V x‖ ^ 2 ∂π) ≤ Module.finrank ℝ H * L := by
  subst π
  exact ⟨integrable_tilted_gradient_of_hessian_bounds hV hlo hup hposition,
    integrable_tilted_gradient_norm_sq_of_hessian_bounds hV hlo hup hposition,
    integral_tilted_gradient_eq_zero_of_hessian_bounds hV hZ hlo hup hposition,
    integral_tilted_gradient_norm_sq_eq_sum_hessian (stdOrthonormalBasis ℝ H)
      hV hZ hlo hup hposition,
    integral_tilted_gradient_norm_sq_le_finrank_mul hV hZ hlo hup hposition⟩

end Hilbert

end AcceleratedLogConcave.Gibbs
