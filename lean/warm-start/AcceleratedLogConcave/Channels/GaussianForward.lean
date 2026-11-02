import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Concrete Gaussian forward channels

This module proves convolution/semigroup identities for every nonnegative
variance, including zero. For positive variance it identifies the multivariate
Gaussian with its normalized quadratic density by characteristic functions and
the Gaussian Fourier integral. The Markov kernel is an explicit fresh-noise
product pushforward. No Gaussian-density or semigroup axiom is assumed.

Source: warm-start.tex, lines 319–332 (forward-channel measure identities).
-/

open MeasureTheory ProbabilityTheory Matrix Complex
open scoped RealInnerProductSpace NNReal ENNReal

namespace AcceleratedLogConcave.Channels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma multivariateGaussian_conv
    (m₁ m₂ : EuclideanSpace ℝ ι) (S₁ S₂ : Matrix ι ι ℝ)
    (h₁ : S₁.PosSemidef) (h₂ : S₂.PosSemidef) :
    multivariateGaussian m₁ S₁ ∗ multivariateGaussian m₂ S₂ =
      multivariateGaussian (m₁ + m₂) (S₁ + S₂) := by
  apply Measure.ext_of_charFun
  ext x
  simp_rw [charFun_conv, charFun_multivariateGaussian h₁,
    charFun_multivariateGaussian h₂, charFun_multivariateGaussian (h₁.add h₂)]
  rw [← Complex.exp_add]
  simp only [inner_add_right, Matrix.add_mulVec, dotProduct_add,
    Complex.ofReal_add]
  congr 1
  ring

noncomputable def noise (t : ℝ≥0) : Measure (EuclideanSpace ℝ ι) :=
  multivariateGaussian 0 ((t : ℝ) • (1 : Matrix ι ι ℝ))

lemma noise_conv (s t : ℝ≥0) :
    noise (ι := ι) s ∗ noise t = noise (s + t) := by
  unfold noise
  rw [multivariateGaussian_conv _ _ _ _
    (Matrix.PosSemidef.one.smul s.coe_nonneg)
    (Matrix.PosSemidef.one.smul t.coe_nonneg)]
  simp [add_smul]

@[simp] lemma noise_zero : noise (ι := ι) 0 = Measure.dirac 0 := by
  simp [noise, multivariateGaussian]

lemma noise_sum_map (s t : ℝ≥0) :
    ((noise (ι := ι) s).prod (noise t)).map (fun p ↦ p.1 + p.2) =
      noise (s + t) := noise_conv s t

noncomputable def forward (μ : Measure (EuclideanSpace ℝ ι)) (t : ℝ≥0) := μ ∗ noise t

lemma forward_add (μ : Measure (EuclideanSpace ℝ ι)) (s t : ℝ≥0) :
    forward (forward μ s) t = forward μ (s + t) := by
  unfold forward
  have : IsProbabilityMeasure (noise (ι := ι) s) := by unfold noise; infer_instance
  have : IsProbabilityMeasure (noise (ι := ι) t) := by unfold noise; infer_instance
  rw [Measure.conv_assoc, noise_conv]

@[simp] lemma forward_zero (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] :
    forward μ 0 = μ := by simp [forward]

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
instance (t : ℝ≥0) : IsProbabilityMeasure (noise (ι := ι) t) := by
  unfold noise
  infer_instance

lemma charFun_noise (t : ℝ≥0) (x : EuclideanSpace ℝ ι) :
    charFun (noise t) x = Complex.exp (-((t : ℝ) * ‖x‖ ^ 2 : ℝ) / 2) := by
  rw [noise, charFun_multivariateGaussian (Matrix.PosSemidef.one.smul t.coe_nonneg)]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, zero_sub]
  have hx : (x : ι → ℝ) ⬝ᵥ (x : ι → ℝ) = ‖x‖ ^ 2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using (real_inner_self_eq_norm_sq x)
  rw [hx]
  congr 1
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

lemma noise_eq_scaled_stdGaussian (t : ℝ≥0) :
    noise (ι := ι) t = (stdGaussian (EuclideanSpace ℝ ι)).map
      (fun x ↦ Real.sqrt (t : ℝ) • x) := by
  apply Measure.ext_of_charFun
  ext x
  rw [charFun_noise, charFun_map_smul, charFun_stdGaussian]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    ← Complex.ofReal_pow, mul_pow, Real.sq_sqrt t.coe_nonneg]

end AcceleratedLogConcave.Channels


namespace AcceleratedLogConcave.Channels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def forwardKernel (t : ℝ≥0) :
    Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) :=
  (Kernel.id ×ₖ Kernel.const _ (noise t)).map (fun p ↦ p.1 + p.2)

instance (t : ℝ≥0) : IsMarkovKernel (forwardKernel (ι := ι) t) := by
  unfold forwardKernel
  apply Kernel.IsMarkovKernel.map
  fun_prop

lemma forwardKernel_apply (t : ℝ≥0) (x : EuclideanSpace ℝ ι) :
    forwardKernel t x = (noise t).map (fun z ↦ x + z) := by
  rw [forwardKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply]
  exact Measure.dirac_conv x (noise t)

lemma forwardKernel_comp (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] (t : ℝ≥0) :
    forwardKernel t ∘ₘ μ = forward μ t := by
  rw [forwardKernel, ← Measure.map_comp _ _ (by fun_prop),
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  rfl

lemma forwardKernel_semigroup (s t : ℝ≥0) :
    forwardKernel (ι := ι) t ∘ₖ forwardKernel s = forwardKernel (s + t) := by
  ext x : 1
  change forwardKernel t ∘ₘ (forwardKernel s x) = _
  rw [forwardKernel_comp, forwardKernel_apply, forwardKernel_apply]
  unfold forward
  rw [← Measure.dirac_conv, Measure.conv_assoc, noise_conv, Measure.dirac_conv]

@[simp] lemma forwardKernel_zero : forwardKernel (ι := ι) 0 = Kernel.id := by
  ext x : 1
  simp [forwardKernel_apply, Kernel.id_apply]
end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma integrable_gaussian_weight (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : EuclideanSpace ℝ ι ↦ Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < (b : ℂ).re from hb) 0 (0 : EuclideanSpace ℝ ι)).norm
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h

omit [DecidableEq ι] in
lemma charFun_gaussian_tilt (b : ℝ) (hb : 0 < b) (w : EuclideanSpace ℝ ι) :
    charFun (volume.tilted (fun x : EuclideanSpace ℝ ι ↦ -b * ‖x‖ ^ 2)) w =
      Complex.exp (-((‖w‖ ^ 2 : ℝ) : ℂ) / (4 * (b : ℂ))) := by
  let Z : ℝ := ∫ x : EuclideanSpace ℝ ι, Real.exp (-b * ‖x‖ ^ 2)
  have hZ : Z ≠ 0 := (integral_exp_pos (integrable_gaussian_weight (ι := ι) b hb)).ne'
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ
  have hc : (Z : ℂ) = (Real.pi / (b : ℂ)) ^
      (Module.finrank ℝ (EuclideanSpace ℝ ι) / 2 : ℂ) := by
    dsimp only [Z]
    rw [← integral_complex_ofReal]
    convert GaussianFourier.integral_cexp_neg_mul_sq_norm
      (show 0 < (b : ℂ).re from hb) (V := EuclideanSpace ℝ ι) using 1
    congr 1
    ext x
    simp
  rw [charFun_apply, integral_tilted]
  change (∫ x : EuclideanSpace ℝ ι,
    (Real.exp (-b * ‖x‖ ^ 2) / Z) • Complex.exp ((inner ℝ x w : ℝ) * Complex.I)) = _
  calc
    _ = (Z : ℂ)⁻¹ * ∫ x : EuclideanSpace ℝ ι,
        Complex.exp (-(b : ℂ) * ‖x‖ ^ 2 + Complex.I * (inner ℝ w x : ℝ)) := by
      rw [← integral_const_mul]
      congr 1
      ext x
      rw [Complex.exp_add, real_inner_comm w x]
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_exp,
        Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]
      ring_nf
    _ = _ := by
      rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add
        (show 0 < (b : ℂ).re from hb), ← hc, ← mul_assoc, inv_mul_cancel₀ hZc, one_mul]
      simp [Complex.I_sq]

lemma noise_eq_tilted (t : ℝ≥0) (ht : 0 < t) :
    noise (ι := ι) t = volume.tilted
      (fun x : EuclideanSpace ℝ ι ↦ -‖x‖ ^ 2 / (2 * (t : ℝ))) := by
  have htR : 0 < (t : ℝ) := ht
  have hb : 0 < (1 / (2 * (t : ℝ))) := by positivity
  have heq : (fun x : EuclideanSpace ℝ ι ↦ -‖x‖ ^ 2 / (2 * (t : ℝ))) =
      (fun x ↦ -(1 / (2 * (t : ℝ))) * ‖x‖ ^ 2) := by
    ext x
    ring
  rw [heq]
  apply Measure.ext_of_charFun
  ext w
  rw [charFun_noise, charFun_gaussian_tilt _ hb]
  congr 1
  push_cast
  field_simp
  ring

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma map_tilted_add (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    (volume.tilted f).map (fun z ↦ x + z) =
      volume.tilted (fun y ↦ f (y - x)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (by fun_prop), lintegral_tilted, lintegral_tilted]
  rw [integral_sub_right_eq_self (fun y ↦ Real.exp (f y)) x]
  conv_rhs => rw [← lintegral_add_left_eq_self _ x]
  simp

lemma forwardKernel_eq_tilted (t : ℝ≥0) (ht : 0 < t) (x : EuclideanSpace ℝ ι) :
    forwardKernel t x = volume.tilted
      (fun y ↦ -‖y - x‖ ^ 2 / (2 * (t : ℝ))) := by
  rw [forwardKernel_apply, noise_eq_tilted t ht, map_tilted_add]

lemma forwardKernel_eq_withDensity (t : ℝ≥0) (ht : 0 < t) (x : EuclideanSpace ℝ ι) :
    forwardKernel t x = volume.withDensity
      (fun y ↦ ENNReal.ofReal (Real.exp (-‖y - x‖ ^ 2 / (2 * (t : ℝ))) /
        ∫ z : EuclideanSpace ℝ ι, Real.exp (-‖z‖ ^ 2 / (2 * (t : ℝ))))) := by
  rw [forwardKernel_eq_tilted t ht x, Measure.tilted]
  rw [integral_sub_right_eq_self (fun z : EuclideanSpace ℝ ι ↦
    Real.exp (-‖z‖ ^ 2 / (2 * (t : ℝ)))) x]

end AcceleratedLogConcave.Channels



namespace AcceleratedLogConcave.Channels
variable {ι : Type*} [Fintype ι]
lemma gaussian_weight_integrable (t : ℝ≥0) (ht : 0 < t) :
    Integrable (fun x : EuclideanSpace ℝ ι ↦ Real.exp (-‖x‖ ^ 2 / (2 * (t : ℝ)))) := by
  have h := integrable_gaussian_weight (ι := ι) (1 / (2 * (t : ℝ))) (by positivity)
  convert h using 1
  ext x
  congr 1
  ring

lemma gaussian_normalizer_pos (t : ℝ≥0) (ht : 0 < t) :
    0 < ∫ x : EuclideanSpace ℝ ι, Real.exp (-‖x‖ ^ 2 / (2 * (t : ℝ))) :=
  integral_exp_pos (gaussian_weight_integrable t ht)

lemma gaussian_normalizer (t : ℝ≥0) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (-‖x‖ ^ 2 / (2 * (t : ℝ)))) =
      (2 * Real.pi * (t : ℝ)) ^ (Fintype.card ι / 2 : ℝ) := by
  have heq : (fun x : EuclideanSpace ℝ ι ↦ Real.exp (-‖x‖ ^ 2 / (2 * (t : ℝ)))) =
      (fun x ↦ Real.exp (-(1 / (2 * (t : ℝ))) * ‖x‖ ^ 2)) := by
    ext x
    congr 1
    ring
  rw [heq, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  congr 1
  · field_simp
  · simp
end AcceleratedLogConcave.Channels
