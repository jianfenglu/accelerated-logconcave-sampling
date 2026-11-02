import AcceleratedLogConcave.Gibbs.Posterior
import Mathlib.Probability.Kernel.Basic

/-!
# Measurable Gaussian-posterior kernels

The exact normalized Gaussian-posterior law is jointly measurable in arbitrary
measurable center and variance parameters. Nonnegative base curvature and
pointwise positive variance make it a Markov kernel, with every natural norm
moment finite. No uniform positive lower bound on the variance is required.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Gibbs

variable {A E : Type*} [MeasurableSpace A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma posterior_density_joint_measurable {F : E → ℝ} {t : A → ℝ} {center : A → E}
    (hF : Measurable F) (ht : Measurable t) (hc : Measurable center) :
    Measurable (fun p : A × E ↦
      ENNReal.ofReal (Real.exp (-(F p.2 + ‖p.2 - center p.1‖ ^ 2 / (2 * t p.1))))) := by
  fun_prop

lemma posterior_partition_measurable {F : E → ℝ} {t : A → ℝ} {center : A → E}
    (hF : Measurable F) (ht : Measurable t) (hc : Measurable center) :
    Measurable (fun a ↦ ∫⁻ x : E,
      ENNReal.ofReal (Real.exp (-(F x + ‖x - center a‖ ^ 2 / (2 * t a))))) :=
  (posterior_density_joint_measurable hF ht hc).lintegral_prod_right'

/-- Measurability of exactly the scalar-normalized law used by the existing core.
This statement by itself does not assert that the laws have mass one. -/
lemma normalized_posterior_measurable {F : E → ℝ} {t : A → ℝ} {center : A → E}
    (hF : Measurable F) (ht : Measurable t) (hc : Measurable center) :
    Measurable (fun a ↦
      (∫⁻ x : E, ENNReal.ofReal (Real.exp (-(F x + ‖x - center a‖ ^ 2 / (2 * t a)))))⁻¹ •
        volume.withDensity (fun x : E ↦
          ENNReal.ofReal (Real.exp (-(F x + ‖x - center a‖ ^ 2 / (2 * t a)))))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
  exact (posterior_partition_measurable hF ht hc).inv.mul
    ((posterior_density_joint_measurable hF ht hc).lintegral_prod_right'
      (ν := volume.restrict s))

/-- The exact normalized posterior family, packaged as a kernel once measurability is proved. -/
noncomputable def normalizedPosteriorKernel (F : E → ℝ) (t : A → ℝ) (center : A → E)
    (hF : Measurable F) (ht : Measurable t) (hc : Measurable center) : Kernel A E where
  toFun a :=
    (∫⁻ x : E, ENNReal.ofReal (Real.exp (-(F x + ‖x - center a‖ ^ 2 / (2 * t a)))))⁻¹ •
      volume.withDensity (fun x : E ↦
        ENNReal.ofReal (Real.exp (-(F x + ‖x - center a‖ ^ 2 / (2 * t a)))))
  measurable' := normalized_posterior_measurable hF ht hc

lemma normalizedPosteriorKernel_apply (F : E → ℝ) (t : A → ℝ) (center : A → E)
    (hF : Measurable F) (ht : Measurable t) (hc : Measurable center) (a : A) :
    normalizedPosteriorKernel F t center hF ht hc a =
      (∫⁻ x : E, ENNReal.ofReal (Real.exp (-(F x + ‖x - center a‖ ^ 2 / (2 * t a)))))⁻¹ •
        volume.withDensity (fun x : E ↦
          ENNReal.ofReal (Real.exp (-(F x + ‖x - center a‖ ^ 2 / (2 * t a))))) := rfl

/-- Nonnegative base curvature and positive variance at every parameter suffice.
In particular the base potential need not itself define a normalizable law. -/
lemma normalizedPosteriorKernel_isMarkov {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {t : A → ℝ} {center : A → E} (ht : Measurable t) (hc : Measurable center)
    (htpos : ∀ a, 0 < t a) :
    IsMarkovKernel (normalizedPosteriorKernel F t center hF.continuous.measurable ht hc) := by
  constructor
  intro a
  exact normalized_posterior_isProbabilityMeasure_of_hessian_lower hF hm (htpos a) (center a) hH

omit [MeasurableSpace A] in
/-- The posterior partition is strictly positive and finite at every parameter.
The partition here omits the Gaussian prefactor, which cancels in the normalized law. -/
lemma posterior_partition_pos_ne_top {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {t : A → ℝ} {center : A → E} (htpos : ∀ a, 0 < t a) (a : A) :
    0 < (∫⁻ x : E, ENNReal.ofReal
        (Real.exp (-(F x + ‖x - center a‖ ^ 2 / (2 * t a))))) ∧
      (∫⁻ x : E, ENNReal.ofReal
        (Real.exp (-(F x + ‖x - center a‖ ^ 2 / (2 * t a))))) ≠ ⊤ := by
  have hI := integrable_posterior_of_hessian_lower hF hm (htpos a) (center a) hH
  exact ⟨lintegral_exp_neg_pos hI, lintegral_exp_neg_ne_top hI⟩

/-- The packaged kernel preserves the core's all-natural-moment interface. -/
lemma normalizedPosteriorKernel_integrable_norm_pow {F : E → ℝ} {m : ℝ}
    (hF : ContDiff ℝ 2 F) (hm : 0 ≤ m)
    (hH : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {t : A → ℝ} {center : A → E} (ht : Measurable t) (hc : Measurable center)
    (htpos : ∀ a, 0 < t a) (a : A) (n : ℕ) :
    Integrable (fun x : E ↦ ‖x‖ ^ n)
      (normalizedPosteriorKernel F t center hF.continuous.measurable ht hc a) :=
  integrable_norm_pow_posterior_of_hessian_lower hF hm (htpos a) (center a) hH n


end AcceleratedLogConcave.Gibbs
