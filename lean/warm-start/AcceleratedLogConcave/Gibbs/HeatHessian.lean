import AcceleratedLogConcave.Gibbs.HeatScore
import Mathlib.MeasureTheory.Function.L2Space
import AcceleratedLogConcave.Analysis.Poisson.HessianMultiplier
import Mathlib.Probability.Moments.Covariance
import AcceleratedLogConcave.Gibbs.Poincare

/-!
# Gaussian heat Hessian, curvature, and score covariance

This file proves the Hessian dictionary, curvature preservation, and score
covariance bound in `sources/warm-start.tex`, lines 280–313. It imports the
frozen HeatScore proof. All public conclusions follow from C² base regularity,
nonnegative lower curvature, a finite upper Hessian bound, and positive time.
The base density need not be normalizable, including at lower curvature zero.

Weighted posterior expectations are differentiated with an explicit integrable
bound on a common center neighborhood; continuity of those derivatives proves
actual C² regularity of the heat potential. Mixed integration by parts gives
both bilinear identities. The curvature and covariance conclusions use the
proved Gibbs Poincare theorem on C¹ tests with L² conditions derived here.
-/

noncomputable section

namespace AcceleratedLogConcave.Gibbs

section Common
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace ENNReal ContDiff Topology


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The normalized Gaussian posterior without measurability proof arguments. -/
def heatPosterior (F : E → ℝ) (t : ℝ) (y : E) : Measure E :=
  (∫⁻ x : E, ENNReal.ofReal (Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))))⁻¹ •
    volume.withDensity (fun x : E ↦
      ENNReal.ofReal (Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))))

theorem heatPosterior_eq_normalizedPosteriorKernel {F : E → ℝ}
    (hF : Measurable F) (t : ℝ) (y : E) :
    heatPosterior F t y = normalizedPosteriorKernel F (fun _ : E ↦ t) id
      hF measurable_const measurable_id y := rfl

theorem heatPosterior_eq_tilted {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E) :
    heatPosterior F t y = volume.tilted (fun x ↦ -(F x + ‖x - y‖ ^ 2 / (2 * t))) :=
  normalizedPosteriorKernel_eq_tilted hF hm ht hlo y

theorem heatPosterior_isProbabilityMeasure {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E) :
    IsProbabilityMeasure (heatPosterior F t y) :=
  normalized_posterior_isProbabilityMeasure_of_hessian_lower hF hm ht y hlo

theorem integrable_norm_pow_heatPosterior {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E) (n : ℕ) :
    Integrable (fun x : E ↦ ‖x‖ ^ n) (heatPosterior F t y) :=
  integrable_norm_pow_posterior_of_hessian_lower hF hm ht y hlo n

/-- Every measurable observable of polynomial growth is integrable under the posterior. -/
theorem integrable_heatPosterior_of_norm_le_polynomial
    {G : Type*} [NormedAddCommGroup G] {g : E → G}
    {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E)
    (hg : AEStronglyMeasurable g (heatPosterior F t y))
    (A B : ℝ) (n : ℕ) (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖ ^ n) :
    Integrable g (heatPosterior F t y) := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  exact ((integrable_const A).add
    ((integrable_norm_pow_heatPosterior hF hm ht hlo y n).const_mul B)).mono'
    hg (Eventually.of_forall hbound)

/-- The same polynomial growth criterion before normalization, useful for differentiation. -/
theorem integrable_polynomial_mul_posterior
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : E → G}
    {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E)
    (hg : AEStronglyMeasurable g volume)
    (A B : ℝ) (n : ℕ) (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖ ^ n) :
    Integrable (fun x ↦ Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))) • g x) := by
  have h0 := integrable_posterior_of_hessian_lower hF hm ht y hlo
  have hn := integrable_norm_pow_mul_posterior_of_hessian_lower hF hm ht y hlo n
  refine ((h0.const_mul A).add (hn.const_mul B)).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun x ↦
      Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))))).aestronglyMeasurable.smul hg
  · filter_upwards [] with x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [Pi.add_apply] using
      (mul_le_mul_of_nonneg_left (hbound x) (Real.exp_pos
        (-(F x + ‖x - y‖ ^ 2 / (2 * t)))).le).trans_eq (by ring)

/-- Affine growth and the genuine second posterior moment imply square integrability. -/
theorem memLp_two_heatPosterior_of_affine_bound
    {G : Type*} [NormedAddCommGroup G] {g : E → G}
    {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E)
    (hg : Continuous g) (A B : ℝ) (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) :
    MemLp g 2 (heatPosterior F t y) := by
  rw [heatPosterior_eq_tilted hF hm ht hlo y]
  apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
  apply integrable_tilted_norm_sq_of_affine_bound hg A B hbound
  rw [← heatPosterior_eq_tilted hF hm ht hlo y]
  exact integrable_norm_pow_heatPosterior hF hm ht hlo y 2

theorem memLp_two_id_heatPosterior {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E) :
    MemLp (fun x : E ↦ x) 2 (heatPosterior F t y) := by
  apply memLp_two_heatPosterior_of_affine_bound hF hm ht hlo y continuous_id 0 1
  intro x
  simp

theorem memLp_two_position_heatPosterior {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y v : E) :
    MemLp (fun x : E ↦ inner ℝ x v) 2 (heatPosterior F t y) := by
  apply memLp_two_heatPosterior_of_affine_bound hF hm ht hlo y
    (by fun_prop) 0 ‖v‖
  intro x
  simpa only [zero_add, mul_comm] using norm_inner_le_norm x v

omit [MeasurableSpace E] [BorelSpace E] in
theorem norm_directionalScore_le_affine {F : E → ℝ} {m L : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (v x : E) :
    ‖fderiv ℝ F x v‖ ≤ ‖gradient F 0‖ * ‖v‖ +
      (max |m| |L| * ‖v‖) * ‖x‖ := by
  calc
    _ = ‖inner ℝ (gradient F x) v‖ := by rw [inner_gradient_left]
    _ ≤ ‖gradient F x‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ (‖gradient F 0‖ + max |m| |L| * ‖x‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (norm_gradient_le_affine_of_hessian_bounds hF hlo hup x) (norm_nonneg _)
    _ = _ := by ring

theorem memLp_two_directionalScore_heatPosterior {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y v : E) :
    MemLp (fun x ↦ fderiv ℝ F x v) 2 (heatPosterior F t y) := by
  apply memLp_two_heatPosterior_of_affine_bound hF hm ht hlo y
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (‖gradient F 0‖ * ‖v‖) (max |m| |L| * ‖v‖)
  exact norm_directionalScore_le_affine hF hlo hup v

theorem memLp_two_gradient_heatPosterior {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y : E) :
    MemLp (gradient F) 2 (heatPosterior F t y) := by
  apply memLp_two_heatPosterior_of_affine_bound hF hm ht hlo y
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hF.continuous_fderiv (by norm_num))) ‖gradient F 0‖ (max |m| |L|)
  exact norm_gradient_le_affine_of_hessian_bounds hF hlo hup

theorem integrable_gradient_heatPosterior {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y : E) :
    Integrable (gradient F) (heatPosterior F t y) := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  exact (memLp_two_gradient_heatPosterior hF hm ht hlo hup y).integrable (by norm_num)

theorem integral_heatPosterior {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E) (g : E → G) :
    (∫ x, g x ∂heatPosterior F t y) =
      (∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))))⁻¹ •
        ∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))) • g x := by
  exact integral_normalized_exp_neg (hF.continuous.measurable.add (by fun_prop))
    (integrable_posterior_of_hessian_lower hF hm ht y hlo) g

theorem integrable_id_heatPosterior {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y : E) :
    Integrable (fun x : E ↦ x) (heatPosterior F t y) := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  exact (memLp_two_id_heatPosterior hF hm ht hlo y).integrable (by norm_num)

theorem integrable_position_heatPosterior {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v) (y v : E) :
    Integrable (fun x : E ↦ inner ℝ x v) (heatPosterior F t y) := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  exact (memLp_two_position_heatPosterior hF hm ht hlo y v).integrable (by norm_num)

theorem integrable_directionalScore_heatPosterior {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y v : E) :
    Integrable (fun x ↦ fderiv ℝ F x v) (heatPosterior F t y) := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  exact (memLp_two_directionalScore_heatPosterior hF hm ht hlo hup y v).integrable
    (by norm_num)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem hessian_mixed_eq_polarization {F : E → ℝ} (hF : ContDiff ℝ 2 F) (x v w : E) :
    (fderiv ℝ (fderiv ℝ F) x v) w =
      ((fderiv ℝ (fderiv ℝ F) x (v + w)) (v + w) -
        (fderiv ℝ (fderiv ℝ F) x v) v - (fderiv ℝ (fderiv ℝ F) x w) w) / 2 := by
  have hsym : (fderiv ℝ (fderiv ℝ F) x v) w =
      (fderiv ℝ (fderiv ℝ F) x w) v :=
    hF.contDiffAt.isSymmSndFDerivAt (by norm_num) v w
  simp only [map_add, add_apply]
  rw [← hsym]
  ring

theorem integrable_hessian_diagonal_heatPosterior {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y v : E) :
    Integrable (fun x ↦ (fderiv ℝ (fderiv ℝ F) x v) v) (heatPosterior F t y) := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  have hfd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  refine (integrable_const (max |m| |L| * ‖v‖ ^ 2)).mono' ?_ ?_
  · exact (((hfd.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply
      continuous_const).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_le]
    have hl := mul_le_mul_of_nonneg_right
      ((neg_le_abs m).trans (le_max_left |m| |L|)) (sq_nonneg ‖v‖)
    have hu := mul_le_mul_of_nonneg_right
      ((le_abs_self L).trans (le_max_right |m| |L|)) (sq_nonneg ‖v‖)
    constructor <;> nlinarith [hlo x v, hup x v]

theorem integrable_hessian_heatPosterior {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y v w : E) :
    Integrable (fun x ↦ (fderiv ℝ (fderiv ℝ F) x v) w) (heatPosterior F t y) := by
  have hd := integrable_hessian_diagonal_heatPosterior hF hm ht hlo hup y
  simpa only [Pi.sub_apply, ← hessian_mixed_eq_polarization hF] using
    (((hd (v + w)).sub (hd v)).sub (hd w)).div_const 2

theorem integrable_directionalScore_mul_heatPosterior {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y v w : E) :
    Integrable (fun x ↦ fderiv ℝ F x v * fderiv ℝ F x w) (heatPosterior F t y) :=
  (memLp_two_directionalScore_heatPosterior hF hm ht hlo hup y v).integrable_mul
    (memLp_two_directionalScore_heatPosterior hF hm ht hlo hup y w)

theorem integrable_position_mul_directionalScore_heatPosterior {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y v w : E) :
    Integrable (fun x ↦ inner ℝ x v * fderiv ℝ F x w) (heatPosterior F t y) :=
  (memLp_two_position_heatPosterior hF hm ht hlo y v).integrable_mul
    (memLp_two_directionalScore_heatPosterior hF hm ht hlo hup y w)

end Common

section Differentiation
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal ContDiff Topology


variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- An affine-growth observable is integrable against the unnormalized posterior. -/
theorem integrable_weighted_posterior_of_affine_growth
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {g : E → G} (hg : Continuous g) (A B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) (y : E) :
    Integrable (fun x ↦ Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))) • g x) := by
  have h0 := integrable_posterior_of_hessian_lower hF hm ht y hH
  have h1 := integrable_norm_pow_mul_posterior_of_hessian_lower hF hm ht y hH 1
  refine ((h0.const_mul A).add (h1.const_mul B)).mono'
    (by fun_prop : Continuous (fun x ↦
      Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))) • g x)).aestronglyMeasurable ?_
  filter_upwards [] with x
  simp only [Pi.add_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), pow_one]
  have h := mul_le_mul_of_nonneg_left (hbound x)
    (Real.exp_pos (-(F x + ‖x - y‖ ^ 2 / (2 * t)))).le
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The fixed-center derivative envelope for a weighted posterior numerator. -/
theorem norm_weighted_posterior_center_deriv_le
    (F : E → ℝ) {t : ℝ} (ht : 0 < t) {g : E → G} (A B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖)
    (x y z : E) (hz : ‖z - y‖ ≤ 1) :
    ‖((-Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t)))) •
      (t⁻¹ • innerSL ℝ (z - x))).smulRight (g x)‖ ≤
      (t⁻¹ * Real.exp (1 / (2 * t))) *
        (((‖x‖ + (‖y‖ + 1)) * (|A| + |B| * ‖x‖)) *
          Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (2 * t))))) := by
  have hg : ‖g x‖ ≤ |A| + |B| * ‖x‖ := by
    calc
      _ ≤ A + B * ‖x‖ := hbound x
      _ ≤ _ := add_le_add (le_abs_self A)
        (mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg x))
  rw [ContinuousLinearMap.norm_smulRight_apply]
  calc
    _ ≤ ((t⁻¹ * Real.exp (1 / (2 * t))) *
        ((‖x‖ + (‖y‖ + 1)) *
          Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (2 * t)))))) *
        (|A| + |B| * ‖x‖) := by
      gcongr
      exact norm_posterior_density_center_deriv_le F ht x y z hz
    _ = _ := by ring

/-- The local derivative envelope has degree two and is integrable even at
zero base curvature. -/
theorem integrable_weighted_posterior_center_deriv_bound
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (A B : ℝ) (y : E) :
    Integrable (fun x ↦ (t⁻¹ * Real.exp (1 / (2 * t))) *
      (((‖x‖ + (‖y‖ + 1)) * (|A| + |B| * ‖x‖)) *
        Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (2 * t)))))) := by
  have h0 := integrable_posterior_of_hessian_lower hF hm (by positivity : 0 < 2*t) y hH
  have h1 := integrable_norm_pow_mul_posterior_of_hessian_lower hF hm
    (by positivity : 0 < 2*t) y hH 1
  have h2 := integrable_norm_pow_mul_posterior_of_hessian_lower hF hm
    (by positivity : 0 < 2*t) y hH 2
  convert (((h2.const_mul |B|).add
    (h1.const_mul (|A| + (‖y‖ + 1) * |B|))).add
      (h0.const_mul ((‖y‖ + 1) * |A|))).const_mul
        (t⁻¹ * Real.exp (1 / (2*t))) using 1
  ext x
  simp only [Pi.add_apply, pow_one]
  ring

/-- Absolute integrability of the CLM-valued derivative, for commuting
direction evaluation with its integral. -/
theorem integrable_weighted_posterior_center_deriv
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {g : E → G} (hg : Continuous g) (A B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) (y : E) :
    Integrable (fun x ↦
      ((-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (y - x))).smulRight (g x)) := by
  refine (integrable_weighted_posterior_center_deriv_bound hF hm ht hH A B y).mono'
    (by fun_prop : Continuous (fun x ↦
      ((-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (y - x))).smulRight (g x))).aestronglyMeasurable ?_
  filter_upwards [] with x
  exact norm_weighted_posterior_center_deriv_le F ht A B hbound x y y (by simp)

/-- Derivative of a raw weighted posterior numerator in its center. -/
theorem hasFDerivAt_weighted_posterior_partition
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {g : E → G} (hg : Continuous g) (A B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) (y : E) :
    HasFDerivAt
      (fun z ↦ ∫ x, Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t))) • g x)
      (∫ x, ((-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (y - x))).smulRight (g x)) y := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball y 1)
    (bound := fun x ↦ (t⁻¹ * Real.exp (1 / (2 * t))) *
      (((‖x‖ + (‖y‖ + 1)) * (|A| + |B| * ‖x‖)) *
        Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (2 * t))))))
    (Metric.ball_mem_nhds y zero_lt_one)
  · exact Eventually.of_forall fun z ↦ (by fun_prop : Continuous
      (fun x ↦ Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t))) • g x)).aestronglyMeasurable
  · exact integrable_weighted_posterior_of_affine_growth hF hm ht hH hg A B hbound y
  · exact (by fun_prop : Continuous (fun x ↦
      ((-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (y - x))).smulRight (g x))).aestronglyMeasurable
  · filter_upwards [] with x z hz
    apply norm_weighted_posterior_center_deriv_le F ht A B hbound x y z
    exact (by simpa only [Metric.mem_ball, dist_eq_norm] using hz : ‖z - y‖ < 1).le
  · exact integrable_weighted_posterior_center_deriv_bound hF hm ht hH A B y
  · filter_upwards [] with x z _
    exact (hasFDerivAt_posterior_density_center F t x z).smul_const (g x)

/-- The derivative of the raw numerator is continuous by the same common local
envelope; this is stronger than pointwise differentiability. -/
theorem continuous_weighted_posterior_partition_deriv
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {g : E → G} (hg : Continuous g) (A B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) :
    Continuous (fun y ↦ ∫ x,
      ((-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (y - x))).smulRight (g x)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  apply continuousAt_of_dominated
    (bound := fun x ↦ (t⁻¹ * Real.exp (1 / (2 * t))) *
      (((‖x‖ + (‖y‖ + 1)) * (|A| + |B| * ‖x‖)) *
        Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (2 * t))))))
  · exact Eventually.of_forall fun z ↦ (by fun_prop : Continuous (fun x ↦
      ((-Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (z - x))).smulRight (g x))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds y zero_lt_one] with z hz
    filter_upwards [] with x
    apply norm_weighted_posterior_center_deriv_le F ht A B hbound x y z
    exact (by simpa only [Metric.mem_ball, dist_eq_norm] using hz : ‖z - y‖ < 1).le
  · exact integrable_weighted_posterior_center_deriv_bound hF hm ht hH A B y
  · filter_upwards [] with x
    exact (by fun_prop : Continuous (fun z ↦
      ((-Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (z - x))).smulRight (g x))).continuousAt

/-- Every continuous affine-growth observable has a C¹ raw posterior numerator. -/
theorem contDiff_one_weighted_posterior_partition
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {g : E → G} (hg : Continuous g) (A B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) :
    ContDiff ℝ 1 (fun y ↦ ∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))) • g x) := by
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨_,
    continuous_weighted_posterior_partition_deriv hF hm ht hH hg A B hbound,
    hasFDerivAt_weighted_posterior_partition hF hm ht hH hg A B hbound⟩

end Differentiation

section Spectral
/-! Pointwise Hessian spectral estimates for the heat Hessian proof. -/

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace


open AcceleratedLogConcave.Analysis.Poisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The gradient of a directional first derivative is the genuine Riesz Hessian action. -/
theorem gradient_fderiv_eq_hessian {F : E → ℝ} (hF : ContDiff ℝ 2 F) (x v : E) :
    gradient (fun z => fderiv ℝ F z v) x = hessianOperator F x v := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hd : Differentiable ℝ (fderiv ℝ F) := hfd.differentiable_one
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left, inner_hessianOperator]
  rw [((hd x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact hF.contDiffAt.isSymmSndFDerivAt (by norm_num) w v

/-- Signed curvature bounds give a uniform bound on the directional score gradient. -/
theorem norm_gradient_fderiv_le {F : E → ℝ} (hF : ContDiff ℝ 2 F) {m L : ℝ}
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (x v : E) :
    ‖gradient (fun z => fderiv ℝ F z v) x‖ ≤ max |m| |L| * ‖v‖ := by
  rw [gradient_fderiv_eq_hessian hF]
  exact ((hessianOperator F x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hessianOperator_norm_le hF hlo hup x) (norm_nonneg v))

omit [FiniteDimensional ℝ E] in
/-- A positive symmetric operator satisfies `T² ≤ L T` from its quadratic upper bound.
The conclusion permits signed `L`; if `L < 0`, the assumptions force the space to be trivial. -/
theorem norm_symmetric_positive_apply_sq_le (T : E →L[ℝ] E) (hs : T.IsSymmetric)
    {L : ℝ} (hlo : ∀ v, 0 ≤ inner ℝ (T v) v)
    (hup : ∀ v, inner ℝ (T v) v ≤ L * ‖v‖ ^ 2) (v : E) :
    ‖T v‖ ^ 2 ≤ L * inner ℝ (T v) v := by
  by_cases hL : 0 ≤ L
  · let B : E →L[ℝ] E := (2 : ℝ) • T - L • ContinuousLinearMap.id ℝ E
    have hBs : B.IsSymmetric := by
      intro a b
      change inner ℝ ((2 : ℝ) • T a - L • a) b =
        inner ℝ a ((2 : ℝ) • T b - L • b)
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right]
      rw [show inner ℝ (T a) b = inner ℝ a (T b) from hs a b]
    have hBn : ‖B‖ ≤ L := by
      rw [B.norm_eq_iSup_rayleighQuotient hBs]
      apply ciSup_le
      intro w
      change |inner ℝ (B w) w / ‖w‖ ^ 2| ≤ L
      by_cases hw : w = 0
      · simpa [hw] using hL
      · simp only [abs_div, abs_pow, abs_norm]
        apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hw))).mpr
        change |inner ℝ ((2 : ℝ) • T w - L • w) w| ≤ L * ‖w‖ ^ 2
        rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq]
        exact abs_le.mpr ⟨by nlinarith [hlo w], by nlinarith [hup w]⟩
    have hb : ‖(2 : ℝ) • T v - L • v‖ ≤ L * ‖v‖ :=
      (B.le_opNorm v).trans (mul_le_mul_of_nonneg_right hBn (norm_nonneg v))
    have hsq := (sq_le_sq₀ (norm_nonneg ((2 : ℝ) • T v - L • v))
      (mul_nonneg hL (norm_nonneg v))).mpr hb
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right] at hsq
    simp only [Real.norm_eq_abs, abs_of_nonneg hL] at hsq
    norm_num at hsq
    nlinarith
  · have hv : v = 0 := by
      by_contra hv
      have hpos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
      have hneg : L * ‖v‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hL) hpos
      linarith [hlo v, hup v]
    simp [hv]

/-- The pointwise Hessian energy bound used in the posterior score covariance estimate. -/
theorem norm_gradient_fderiv_sq_le {F : E → ℝ} (hF : ContDiff ℝ 2 F) {m L : ℝ}
    (hm : 0 ≤ m)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (x v : E) :
    ‖gradient (fun z => fderiv ℝ F z v) x‖ ^ 2 ≤
      L * fderiv ℝ (fderiv ℝ F) x v v := by
  rw [gradient_fderiv_eq_hessian hF, ← inner_hessianOperator]
  exact norm_symmetric_positive_apply_sq_le _ (hessianOperator_symmetric hF x)
    (fun w => by rw [inner_hessianOperator]; exact (mul_nonneg hm (sq_nonneg ‖w‖)).trans (hlo x w))
    (fun w => by simpa only [inner_hessianOperator] using hup x w) v

end Spectral

section Mean
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace ENNReal ContDiff Topology


variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The normalized posterior expectation is continuously differentiable for
all continuous affine-growth observables. Its raw numerator and denominator
are differentiated using a common integrable local envelope. -/
theorem contDiff_one_integral_heatPosterior
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    {g : E → G} (hg : Continuous g) (A B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) :
    ContDiff ℝ 1 (fun y ↦ ∫ x, g x ∂heatPosterior F t y) := by
  have hZ : ContDiff ℝ 1
      (fun y ↦ ∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) := by
    simpa only [smul_eq_mul, mul_one] using
      (contDiff_one_weighted_posterior_partition hF hm ht hlo
        (continuous_const : Continuous (fun _ : E ↦ (1 : ℝ))) 1 0 (by intro x; simp))
  have hn := contDiff_one_weighted_posterior_partition hF hm ht hlo hg A B hbound
  have hz (y : E) : (∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) ≠ 0 :=
    (integral_exp_pos (integrable_posterior_of_hessian_lower hF hm ht y hlo)).ne'
  have heq (y : E) : (∫ x, g x ∂heatPosterior F t y) =
      (∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))))⁻¹ •
        ∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))) • g x :=
    integral_heatPosterior hF hm ht hlo y g
  simp_rw [heq]
  exact (hZ.inv hz).smul hn

/-- The Fréchet derivative of the normalized posterior mean, including the
normalizing partition derivative. -/
theorem hasFDerivAt_integral_heatPosterior
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    {g : E → G} (hg : Continuous g) (A B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) (y : E) :
    HasFDerivAt (fun z ↦ ∫ x, g x ∂heatPosterior F t z)
      ((∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))))⁻¹ •
        (∫ x, ((-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
          (t⁻¹ • innerSL ℝ (y - x))).smulRight (g x)) +
      (-( (∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) ^ 2)⁻¹ •
        (∫ x, (-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
          (t⁻¹ • innerSL ℝ (y - x)))).smulRight
        (∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))) • g x)) y := by
  have hz : (∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) ≠ 0 :=
    (integral_exp_pos (integrable_posterior_of_hessian_lower hF hm ht y hlo)).ne'
  have hZ := hasFDerivAt_posterior_partition hF hm ht y hlo
  have hN := hasFDerivAt_weighted_posterior_partition hF hm ht hlo hg A B hbound y
  have hi := (hasDerivAt_inv hz).comp_hasFDerivAt y hZ
  have h := hi.fun_smul hN
  have heq (z : E) : (∫ x, g x ∂heatPosterior F t z) =
      (∫ x, Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t))))⁻¹ •
        ∫ x, Real.exp (-(F x + ‖x - z‖ ^ 2 / (2 * t))) • g x :=
    integral_heatPosterior hF hm ht hlo z g
  simpa only [heq, Function.comp_apply, neg_inv] using h

/-- Evaluation of the dominated derivative integral commutes with expectation
and gives the centered Gaussian likelihood score. -/
private theorem inv_partition_mul_derivative_integral_apply
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    {g : E → ℝ} (hg : Continuous g) (A B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) (y v : E) :
    (∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))))⁻¹ *
      (∫ x, ((-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
        (t⁻¹ • innerSL ℝ (y - x))).smulRight (g x)) v =
      ∫ x, (t⁻¹ * (inner ℝ x v - inner ℝ y v)) * g x ∂heatPosterior F t y := by
  rw [ContinuousLinearMap.integral_apply
    (integrable_weighted_posterior_center_deriv hF hm ht hlo hg A B hbound y) v,
    integral_heatPosterior hF hm ht hlo y]
  simp only [smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul, inner_sub_left]
  ring

/-- The derivative of a scalar posterior expectation is its actual posterior
covariance with position. All square-integrability and derivative exchanges
are consequences of the stated curvature and affine-growth hypotheses. -/
theorem fderiv_integral_heatPosterior_eq_covariance
    {F : E → ℝ} {m t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    {g : E → ℝ} (hg : Continuous g) (A B : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ A + B * ‖x‖) (y v : E) :
    fderiv ℝ (fun z ↦ ∫ x, g x ∂heatPosterior F t z) y v =
      t⁻¹ * cov[g, fun x ↦ inner ℝ x v; heatPosterior F t y] := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  let Z : ℝ := ∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))
  let N : ℝ := ∫ x, Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t))) • g x
  let D : E → E →L[ℝ] ℝ := fun x ↦
    (-Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * t)))) •
      (t⁻¹ • innerSL ℝ (y - x))
  let S : E → ℝ := fun x ↦ t⁻¹ * (inner ℝ x v - inner ℝ y v)
  have hN : (∫ x, g x ∂heatPosterior F t y) = Z⁻¹ * N :=
    integral_heatPosterior hF hm ht hlo y g
  have hg' : Z⁻¹ * (∫ x, (D x).smulRight (g x)) v =
      ∫ x, S x * g x ∂heatPosterior F t y :=
    inv_partition_mul_derivative_integral_apply hF hm ht hlo hg A B hbound y v
  have h1' : Z⁻¹ * (∫ x, D x) v = ∫ x, S x ∂heatPosterior F t y := by
    have heq : (fun x ↦ (D x).smulRight (1 : ℝ)) = D := by
      ext x w
      simp
    have hh := inv_partition_mul_derivative_integral_apply hF hm ht hlo
      (continuous_const : Continuous (fun _ : E ↦ (1 : ℝ))) 1 0
      (by intro x; simp) y v
    change Z⁻¹ * (∫ x, (D x).smulRight (1 : ℝ)) v = _ at hh
    simpa only [heq, mul_one] using hh
  have hder : fderiv ℝ (fun z ↦ ∫ x, g x ∂heatPosterior F t z) y v =
      Z⁻¹ * (∫ x, (D x).smulRight (g x)) v -
        (Z⁻¹ * N) * (Z⁻¹ * (∫ x, D x) v) := by
    rw [(hasFDerivAt_integral_heatPosterior hF hm ht hlo hg A B hbound y).fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    change Z⁻¹ * (∫ x, (D x).smulRight (g x)) v +
      -((Z ^ 2)⁻¹) * (∫ x, D x) v * N = _
    rw [← inv_pow]
    ring
  rw [hder, hg', h1', ← hN]
  have hg2 := memLp_two_heatPosterior_of_affine_bound hF hm ht hlo y hg A B hbound
  have hx2 := memLp_two_position_heatPosterior hF hm ht hlo y v
  have hs2 : MemLp S 2 (heatPosterior F t y) :=
    (hx2.sub (memLp_const (inner ℝ y v))).const_mul t⁻¹
  have hcov : (∫ x, S x * g x ∂heatPosterior F t y) -
      (∫ x, g x ∂heatPosterior F t y) * (∫ x, S x ∂heatPosterior F t y) =
      cov[g, S; heatPosterior F t y] := by
    rw [covariance_eq_sub hg2 hs2]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Pi.mul_apply, mul_comm]
  rw [hcov]
  change cov[g, fun x ↦ t⁻¹ * (inner ℝ x v - inner ℝ y v); heatPosterior F t y] = _
  rw [covariance_const_mul_right,
    covariance_sub_const_right (hx2.integrable (by norm_num))]

end Mean

section IBP
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Whole-space Gibbs integration by parts expressed as a covariance.
The score mean is proved by integration by parts, not assumed. -/
theorem integral_tilted_fderiv_eq_covariance {V f : E → ℝ} (v : E)
    (hV : Differentiable ℝ V) (hf : Differentiable ℝ f)
    (hZ : Integrable (fun x ↦ Real.exp (-V x)))
    (hscore : MemLp (fun x ↦ fderiv ℝ V x v) 2 (volume.tilted (fun x ↦ -V x)))
    (hfun : MemLp f 2 (volume.tilted (fun x ↦ -V x)))
    (hderiv : Integrable (fun x ↦ fderiv ℝ f x v) (volume.tilted (fun x ↦ -V x))) :
    (∫ x, fderiv ℝ f x v ∂(volume.tilted (fun x ↦ -V x))) =
      cov[fun x ↦ fderiv ℝ V x v, f; volume.tilted (fun x ↦ -V x)] := by
  let := isProbabilityMeasure_tilted hZ
  have hzero := integral_tilted_score_eq_zero v hV hZ (hscore.integrable (by norm_num))
  rw [covariance_eq_sub hscore hfun, hzero, zero_mul, sub_zero]
  exact integral_tilted_fderiv v hV hf hZ (hscore.integrable_mul hfun)
    hderiv (hfun.integrable (by norm_num))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The directional posterior score is the original score plus a centered linear term. -/
theorem fderiv_posterior_potential_apply {F : E → ℝ} (hF : Differentiable ℝ F)
    (t : ℝ) (y x v : E) :
    fderiv ℝ (fun z ↦ F z + ‖z - y‖ ^ 2 / (2 * t)) x v =
      fderiv ℝ F x v + t⁻¹ * (⟪x, v⟫ - ⟪y, v⟫) := by
  rw [fderiv_fun_add (hF x)
    (hasFDerivAt_gaussian_regularizer t y x).differentiableAt,
    (hasFDerivAt_gaussian_regularizer t y x).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, inner_sub_left]

/-- Bilinear posterior integration by parts identifies the expected base Hessian
minus the base-score covariance with the position/score covariance. All moment
and integrability conditions are derived from the source curvature hypotheses. -/
theorem integral_hessian_sub_score_covariance_heatPosterior
    {F : E → ℝ} {m L t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y v w : E) :
    (∫ x, (fderiv ℝ (fderiv ℝ F) x v) w ∂(heatPosterior F t y)) -
        cov[fun x ↦ fderiv ℝ F x v, fun x ↦ fderiv ℝ F x w; heatPosterior F t y] =
      t⁻¹ * cov[fun x ↦ ⟪x, v⟫, fun x ↦ fderiv ℝ F x w; heatPosterior F t y] := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  have hR := heatPosterior_eq_tilted hF hm ht hlo y
  have hv := memLp_two_directionalScore_heatPosterior hF hm ht hlo hup y v
  have hw := memLp_two_directionalScore_heatPosterior hF hm ht hlo hup y w
  have hp := memLp_two_position_heatPosterior hF hm ht hlo y v
  have hlinear : MemLp (fun x ↦ t⁻¹ * (⟪x, v⟫ - ⟪y, v⟫)) 2
      (heatPosterior F t y) := by
    simpa only [Pi.sub_apply] using! (hp.sub (memLp_const ⟪y, v⟫)).const_mul t⁻¹
  have hpost : MemLp
      (fun x ↦ fderiv ℝ (fun z ↦ F z + ‖z - y‖ ^ 2 / (2 * t)) x v)
      2 (heatPosterior F t y) := by
    simpa only [Pi.add_apply, Pi.sub_apply,
      fderiv_posterior_potential_apply (hF.differentiable (by norm_num))] using!
      hv.add hlinear
  have hf : ContDiff ℝ 1 (fun x ↦ fderiv ℝ F x w) :=
    (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const
  have hh : Integrable (fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ F z w) x v)
      (heatPosterior F t y) := by
    simpa only [fderiv_directional_score_apply hF] using
      integrable_hessian_heatPosterior hF hm ht hlo hup y v w
  have hibp := integral_tilted_fderiv_eq_covariance v
    ((contDiff_posterior_potential hF t y).differentiable (by norm_num))
    (hf.differentiable one_ne_zero)
    (integrable_posterior_of_hessian_lower hF hm ht y hlo)
    (by rwa [← hR]) (by rwa [← hR]) (by rwa [← hR])
  rw [← hR] at hibp
  simp only [fderiv_directional_score_apply hF,
    fderiv_posterior_potential_apply (hF.differentiable (by norm_num))] at hibp
  have hcov : cov[fun x ↦ fderiv ℝ F x v + t⁻¹ * (⟪x, v⟫ - ⟪y, v⟫),
        fun x ↦ fderiv ℝ F x w; heatPosterior F t y] =
      cov[fun x ↦ fderiv ℝ F x v, fun x ↦ fderiv ℝ F x w; heatPosterior F t y] +
        t⁻¹ * cov[fun x ↦ ⟪x, v⟫, fun x ↦ fderiv ℝ F x w; heatPosterior F t y] := by
    change cov[(fun x ↦ fderiv ℝ F x v) +
      (fun x ↦ t⁻¹ * (⟪x, v⟫ - ⟪y, v⟫)),
      fun x ↦ fderiv ℝ F x w; heatPosterior F t y] = _
    rw [covariance_add_left hv hlinear hw, covariance_const_mul_left,
      covariance_sub_const_left (hp.integrable (by norm_num))]
  linarith [hibp.trans hcov]

/-- The mixed position/base-score covariance follows by testing posterior
integration by parts against a linear position coordinate. -/
theorem position_score_covariance_heatPosterior
    {F : E → ℝ} {m L t : ℝ} (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x v) v)
    (hup : ∀ x v, (fderiv ℝ (fderiv ℝ F) x v) v ≤ L * ‖v‖ ^ 2) (y v w : E) :
    cov[fun x ↦ ⟪x, v⟫, fun x ↦ fderiv ℝ F x w; heatPosterior F t y] =
      ⟪v, w⟫ - t⁻¹ * cov[fun x ↦ ⟪x, v⟫, fun x ↦ ⟪x, w⟫; heatPosterior F t y] := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  have hR := heatPosterior_eq_tilted hF hm ht hlo y
  have hw := memLp_two_directionalScore_heatPosterior hF hm ht hlo hup y w
  have hpv := memLp_two_position_heatPosterior hF hm ht hlo y v
  have hpw := memLp_two_position_heatPosterior hF hm ht hlo y w
  have hlinear : MemLp (fun x ↦ t⁻¹ * (⟪x, w⟫ - ⟪y, w⟫)) 2
      (heatPosterior F t y) := by
    simpa only [Pi.sub_apply] using! (hpw.sub (memLp_const ⟪y, w⟫)).const_mul t⁻¹
  have hpost : MemLp
      (fun x ↦ fderiv ℝ (fun z ↦ F z + ‖z - y‖ ^ 2 / (2 * t)) x w)
      2 (heatPosterior F t y) := by
    simpa only [Pi.add_apply, Pi.sub_apply,
      fderiv_posterior_potential_apply (hF.differentiable (by norm_num))] using!
      hw.add hlinear
  have hd (x : E) : fderiv ℝ (fun z ↦ ⟪z, v⟫) x w = ⟪w, v⟫ := by
    change fderiv ℝ (fun z ↦ ⟪id z, v⟫) x w = _
    rw [fderiv_inner_apply ℝ differentiableAt_id (differentiableAt_const v)]
    simp
  have hderiv : Integrable (fun x ↦ fderiv ℝ (fun z ↦ ⟪z, v⟫) x w)
      (heatPosterior F t y) := by
    simpa only [hd] using (integrable_const ⟪w, v⟫ :
      Integrable (fun _ : E ↦ ⟪w, v⟫) (heatPosterior F t y))
  have hibp := integral_tilted_fderiv_eq_covariance (f := fun x ↦ ⟪x, v⟫) w
    ((contDiff_posterior_potential hF t y).differentiable (by norm_num))
    (by simpa only [id_eq] using (differentiable_id.inner ℝ (differentiable_const v)))
    (integrable_posterior_of_hessian_lower hF hm ht y hlo)
    (by rwa [← hR]) (by rwa [← hR]) (by rwa [← hR])
  rw [← hR] at hibp
  simp only [hd, integral_const, probReal_univ, smul_eq_mul, one_mul,
    fderiv_posterior_potential_apply (hF.differentiable (by norm_num))] at hibp
  have hcov : cov[fun x ↦ fderiv ℝ F x w + t⁻¹ * (⟪x, w⟫ - ⟪y, w⟫),
        fun x ↦ ⟪x, v⟫; heatPosterior F t y] =
      cov[fun x ↦ ⟪x, v⟫, fun x ↦ fderiv ℝ F x w; heatPosterior F t y] +
        t⁻¹ * cov[fun x ↦ ⟪x, v⟫, fun x ↦ ⟪x, w⟫; heatPosterior F t y] := by
    change cov[(fun x ↦ fderiv ℝ F x w) + (fun x ↦ t⁻¹ * (⟪x, w⟫ - ⟪y, w⟫)),
      fun x ↦ ⟪x, v⟫; heatPosterior F t y] = _
    rw [covariance_add_left hw hlinear hpv, covariance_const_mul_left,
      covariance_sub_const_left (hpw.integrable (by norm_num)),
      covariance_comm (fun x ↦ fderiv ℝ F x w), covariance_comm (fun x ↦ ⟪x, w⟫)]
  rw [real_inner_comm] at hibp
  linarith [hibp.trans hcov]

end IBP

section Poincare
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal ContDiff


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_fderiv_apply {F : E → ℝ} (hF : ContDiff ℝ 2 F) (v : E) :
    ContDiff ℝ 1 (fun x ↦ fderiv ℝ F x v) := by
  exact (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_gradient_fderiv_apply {F : E → ℝ} (hF : ContDiff ℝ 2 F) (v : E) :
    Continuous (gradient (fun x ↦ fderiv ℝ F x v)) := by
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    ((contDiff_fderiv_apply hF v).continuous_fderiv one_ne_zero)

omit [MeasurableSpace E] [BorelSpace E] in
theorem gradient_position_inner (v x : E) :
    gradient (fun z : E ↦ ⟪z, v⟫) x = v := by
  have heq : (fun z : E ↦ ⟪z, v⟫) = (innerSL ℝ v) := by
    funext z
    exact (real_inner_comm z v).symm
  rw [heq]
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left]
  exact congrArg (fun f : E →L[ℝ] ℝ ↦ f w) (innerSL ℝ v).hasFDerivAt.fderiv

/-- The directional base score has square-integrable gradient, proved from the
uniform Hessian bound and posterior probability normalization. -/
theorem memLp_two_gradient_directionalScore_heatPosterior {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (y v : E) :
    MemLp (gradient (fun x ↦ fderiv ℝ F x v)) 2 (heatPosterior F t y) := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  exact MemLp.of_bound (continuous_gradient_fderiv_apply hF v).aestronglyMeasurable
    (max |m| |L| * ‖v‖) (Filter.Eventually.of_forall fun x ↦
      norm_gradient_fderiv_le hF hlo hup x v)

/-- Posterior Poincare applied to a linear position observable. All domain
membership comes from actual posterior moments, including when `m = 0`. -/
theorem covariance_position_heatPosterior_le {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (y v : E) :
    (m + t⁻¹) * cov[fun x ↦ ⟪x, v⟫, fun x ↦ ⟪x, v⟫; heatPosterior F t y] ≤
      ‖v‖ ^ 2 := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  have hq : MemLp (gradient (fun x : E ↦ ⟪x, v⟫)) 2 (heatPosterior F t y) := by
    have hg : gradient (fun x : E ↦ ⟪x, v⟫) = fun _ ↦ v :=
      funext (gradient_position_inner v)
    rw [hg]
    exact memLp_const v
  have h := c1_variance_poincare (heatPosterior F t y)
    (fun x ↦ F x + ‖x - y‖ ^ 2 / (2 * t))
    (contDiff_posterior_potential hF t y)
    (integrable_posterior_of_hessian_lower hF hm ht y hlo)
    (heatPosterior_eq_tilted hF hm ht hlo y)
    (m + t⁻¹) (L + t⁻¹) (by positivity)
    (posterior_hessian_lower hF hlo t y) (posterior_hessian_upper hF hup t y)
    (fun x ↦ ⟪x, v⟫) (contDiff_id.inner ℝ contDiff_const)
    (memLp_two_position_heatPosterior hF hm ht hlo y v) hq
  simpa only [covariance, pow_two, gradient_position_inner, integral_const,
    probReal_univ, one_smul] using h

/-- Poincare for the base-score observable, with its gradient energy explicit. -/
theorem covariance_directionalScore_heatPosterior_le_energy {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (y v : E) :
    (m + t⁻¹) * cov[fun x ↦ fderiv ℝ F x v, fun x ↦ fderiv ℝ F x v;
      heatPosterior F t y] ≤
      ∫ x, ‖gradient (fun z ↦ fderiv ℝ F z v) x‖ ^ 2 ∂heatPosterior F t y := by
  have h := c1_variance_poincare (heatPosterior F t y)
    (fun x ↦ F x + ‖x - y‖ ^ 2 / (2 * t))
    (contDiff_posterior_potential hF t y)
    (integrable_posterior_of_hessian_lower hF hm ht y hlo)
    (heatPosterior_eq_tilted hF hm ht hlo y)
    (m + t⁻¹) (L + t⁻¹) (by positivity)
    (posterior_hessian_lower hF hlo t y) (posterior_hessian_upper hF hup t y)
    (fun x ↦ fderiv ℝ F x v) (contDiff_fderiv_apply hF v)
    (memLp_two_directionalScore_heatPosterior hF hm ht hlo hup y v)
    (memLp_two_gradient_directionalScore_heatPosterior hF hm ht hlo hup y v)
  simpa only [covariance, pow_two] using h

/-- Positive Hessian curvature bounds its squared action under the actual posterior. -/
theorem integral_directionalScore_gradient_sq_le {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (y v : E) :
    (∫ x, ‖gradient (fun z ↦ fderiv ℝ F z v) x‖ ^ 2 ∂heatPosterior F t y) ≤
      L * ∫ x, fderiv ℝ (fderiv ℝ F) x v v ∂heatPosterior F t y := by
  have hq := memLp_two_gradient_directionalScore_heatPosterior hF hm ht hlo hup y v
  have hi := (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq
  rw [← integral_const_mul]
  exact integral_mono hi
    ((integrable_hessian_diagonal_heatPosterior hF hm ht hlo hup y v).const_mul L)
    (fun x ↦ norm_gradient_fderiv_sq_le hF hm hlo hup x v)

/-- Posterior score covariance bounded by the mean base Hessian, with the full
posterior curvature `m + 1/t` retained. -/
theorem covariance_directionalScore_heatPosterior_le_hessian {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (y v : E) :
    (m + t⁻¹) * cov[fun x ↦ fderiv ℝ F x v, fun x ↦ fderiv ℝ F x v;
      heatPosterior F t y] ≤
      L * ∫ x, fderiv ℝ (fderiv ℝ F) x v v ∂heatPosterior F t y :=
  (covariance_directionalScore_heatPosterior_le_energy hF hm ht hlo hup y v).trans
    (integral_directionalScore_gradient_sq_le hF hm ht hlo hup y v)

end Poincare

section Assembly
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace


/-- Scalar algebra converting the posterior position Poincare estimate into
heat curvature. Analytic inputs are supplied by the public theorem below. -/
theorem heat_curvature_lower_algebra {m t q s : ℝ} (hm : 0 ≤ m) (ht : 0 < t)
    (hvar : (m + t⁻¹) * s ≤ q) :
    m / (1 + m * t) * q ≤ t⁻¹ * q - (t⁻¹) ^ 2 * s := by
  have hD : 0 < 1 + m * t := by positivity
  have h1 : (m * t + 1) * s ≤ t * q := by
    have h := mul_le_mul_of_nonneg_left hvar ht.le
    convert! h using 1
    field_simp
  have heq : t⁻¹ * q - (t⁻¹) ^ 2 * s = (t * q - s) / t ^ 2 := by
    field_simp
  rw [heq, div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hD (sq_pos_of_pos ht)).mpr
  nlinarith

/-- Scalar rearrangement of posterior score Poincare and the Hessian identity. -/
theorem heat_score_covariance_algebra {m L t sigma hess : ℝ}
    (hm : 0 ≤ m) (ht : 0 < t) (hsigma : 0 ≤ sigma) (htL : t * L < 1)
    (hp : (m + t⁻¹) * sigma ≤ L * (hess + sigma)) :
    sigma ≤ t * L / (1 - t * L) * hess := by
  have hD : 0 < 1 - t * L := by linarith
  have h1 := mul_le_mul_of_nonneg_left hp ht.le
  have h2 : (m * t + 1) * sigma ≤ t * L * (hess + sigma) := by
    convert! h1 using 1
    · field_simp
    · ring
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hD).mpr
  nlinarith [mul_nonneg (mul_nonneg hm ht.le) hsigma]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Positive Gaussian time gives a genuine C² heat potential. The derivative
is C¹ because the posterior mean is C¹ by local dominated differentiation. -/
theorem contDiff_two_heatPotential {F : E → ℝ} {m t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) :
    ContDiff ℝ 2 (heatPotential F t) := by
  have hmean : ContDiff ℝ 1 (fun y ↦ ∫ x, x ∂heatPosterior F t y) :=
    contDiff_one_integral_heatPosterior hF hm ht hlo continuous_id 0 1 (by intro x; simp)
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨fun y ↦ t⁻¹ • innerSL ℝ (y - ∫ x, x ∂heatPosterior F t y), ?_, ?_⟩
  · exact ((innerSL ℝ (E := E)).contDiff.comp (contDiff_id.sub hmean)).const_smul t⁻¹
  · intro y
    convert! (hasGradientAt_heatPotential hF hm ht hlo y).hasFDerivAt using 1
    ext v
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
      InnerProductSpace.toDual_apply_apply, real_inner_smul_left]
    rfl

/-- The directional heat score is the expectation of the directional base score. -/
theorem fderiv_heatPotential_eq_integral_score {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (y w : E) :
    fderiv ℝ (heatPotential F t) y w =
      ∫ x, fderiv ℝ F x w ∂heatPosterior F t y := by
  have hs : gradient (heatPotential F t) y =
      ∫ x, gradient F x ∂heatPosterior F t y :=
    (heat_score_dictionary hF hm ht hlo hup y).1
  have hi := (innerSL ℝ w).integral_comp_comm
    (integrable_gradient_heatPosterior hF hm ht hlo hup y)
  simp only [innerSL_apply_apply, inner_gradient_right, conj_trivial] at hi
  rw [← inner_gradient_left, hs, real_inner_comm]
  exact hi.symm

/-- Differentiating the actual directional heat score gives its posterior
position/score covariance. -/
theorem heat_hessian_cross_covariance {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (y v w : E) :
    fderiv ℝ (fderiv ℝ (heatPotential F t)) y v w =
      t⁻¹ * cov[fun x ↦ inner ℝ x v, fun x ↦ fderiv ℝ F x w; heatPosterior F t y] := by
  rw [← fderiv_directional_score_apply (contDiff_two_heatPotential hF hm ht hlo) y w v]
  have heq : (fun z ↦ fderiv ℝ (heatPotential F t) z w) =
      fun z ↦ ∫ x, fderiv ℝ F x w ∂heatPosterior F t z :=
    funext fun z ↦ fderiv_heatPotential_eq_integral_score hF hm ht hlo hup z w
  rw [heq, fderiv_integral_heatPosterior_eq_covariance hF hm ht hlo
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (‖gradient F 0‖ * ‖w‖) (max |m| |L| * ‖w‖)
    (norm_directionalScore_le_affine hF hlo hup w) y v,
    covariance_comm]

/-- Both bilinear Hessian identities from the manuscript. Covariances use
Mathlib's actual centered-integral definition under the normalized posterior. -/
theorem heat_hessian_dictionary {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (y v w : E) :
    fderiv ℝ (fderiv ℝ (heatPotential F t)) y v w =
      (∫ x, fderiv ℝ (fderiv ℝ F) x v w ∂heatPosterior F t y) -
        cov[fun x ↦ fderiv ℝ F x v, fun x ↦ fderiv ℝ F x w; heatPosterior F t y] ∧
    fderiv ℝ (fderiv ℝ (heatPotential F t)) y v w =
      t⁻¹ * inner ℝ v w - (t⁻¹) ^ 2 *
        cov[fun x ↦ inner ℝ x v, fun x ↦ inner ℝ x w; heatPosterior F t y] := by
  constructor
  · exact (heat_hessian_cross_covariance hF hm ht hlo hup y v w).trans
      (integral_hessian_sub_score_covariance_heatPosterior hF hm ht hlo hup y v w).symm
  · rw [heat_hessian_cross_covariance hF hm ht hlo hup y v w,
      position_score_covariance_heatPosterior hF hm ht hlo hup y v w]
    ring

/-- A covariance quadratic form is nonnegative, directly from its centered square. -/
theorem covariance_self_nonneg_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : 0 ≤ cov[f, f; μ] := by
  unfold covariance
  apply integral_nonneg
  intro x
  exact mul_self_nonneg _

/-- Gaussian smoothing preserves the manuscript's two-sided curvature bounds.
The lower estimate uses the actual posterior Poincare theorem. -/
theorem heat_hessian_curvature {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2) (y v : E) :
    m / (1 + m * t) * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (heatPotential F t)) y v v ∧
    fderiv ℝ (fderiv ℝ (heatPotential F t)) y v v ≤ L * ‖v‖ ^ 2 := by
  let := heatPosterior_isProbabilityMeasure hF hm ht hlo y
  have hd := heat_hessian_dictionary hF hm ht hlo hup y v v
  constructor
  · rw [hd.2, real_inner_self_eq_norm_sq]
    exact heat_curvature_lower_algebra hm ht
      (covariance_position_heatPosterior_le hF hm ht hlo hup y v)
  · rw [hd.1]
    have hi : (∫ x, fderiv ℝ (fderiv ℝ F) x v v ∂heatPosterior F t y) ≤
        L * ‖v‖ ^ 2 := by
      simpa only [integral_const, probReal_univ, one_smul] using
        integral_mono (integrable_hessian_diagonal_heatPosterior hF hm ht hlo hup y v)
          (integrable_const (L * ‖v‖ ^ 2)) (fun x ↦ hup x v)
    exact (sub_le_self _ (covariance_self_nonneg_integral _ _)).trans hi

/-- The posterior base-score covariance is bounded by the smoothed Hessian
when `t * L < 1`, with the exact coefficient from the source. -/
theorem heat_score_covariance_bound {F : E → ℝ} {m L t : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ L * ‖v‖ ^ 2)
    (htL : t * L < 1) (y v : E) :
    cov[fun x ↦ fderiv ℝ F x v, fun x ↦ fderiv ℝ F x v; heatPosterior F t y] ≤
      t * L / (1 - t * L) * fderiv ℝ (fderiv ℝ (heatPotential F t)) y v v := by
  apply heat_score_covariance_algebra hm ht (covariance_self_nonneg_integral _ _) htL
  have hp := covariance_directionalScore_heatPosterior_le_hessian hF hm ht hlo hup y v
  rw [(heat_hessian_dictionary hF hm ht hlo hup y v v).1]
  simpa only [sub_add_cancel] using hp

end Assembly

end AcceleratedLogConcave.Gibbs
