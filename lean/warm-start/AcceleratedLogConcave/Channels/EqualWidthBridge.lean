import Mathlib.Probability.Kernel.Composition.WithDensity
import AcceleratedLogConcave.Channels.GaussianForward
import AcceleratedLogConcave.Gibbs.PosteriorKernel
import AcceleratedLogConcave.Analysis.WeightedGradient.MeasureBridge

/-!
# The concrete equal-width Gaussian reverse bridge

The Gaussian likelihood identifies W02a's jointly measurable normalized
posterior kernel by the full swapped-joint identity. Thus the bridge theorem
below has no assumed Bayes/disintegration identity. A measurable potential with
integrable exp(-F) suffices; curvature is not needed for this measure identity.
Positive width is required by the likelihood interpretation.

The bridge pairs the posterior draw with an independent Gaussian reserve and
maps (y,a,z) to (y+a+z)/2. The resulting law is the original Gibbs law convolved
with the Gaussian of half the variance. This is the measure-level portion of
warm-start.tex, lines 319–342; score differentiation is outside this module.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AcceleratedLogConcave.Channels
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
  {κ : Kernel A B} [IsSFiniteKernel κ]
  {f : A → B → ℝ≥0∞}

omit [IsSFiniteKernel κ] in
/-- A measurable likelihood gives the forward marginal density, in ENNReal. -/
lemma marginal_density (hf : Measurable (Function.uncurry f))
    (hκ : ∀ a, κ a = ν.withDensity (f a)) :
    κ ∘ₘ μ = ν.withDensity (fun b ↦ ∫⁻ a, f a b ∂μ) := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  erw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable hg.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (hf.lintegral_prod_left' (μ := μ)) hg]
  simp_rw [hκ, lintegral_withDensity_eq_lintegral_mul _ hf.of_uncurry_left hg]
  rw [lintegral_lintegral_swap (hf.mul (hg.comp measurable_snd)).aemeasurable]
  congr with b
  exact lintegral_mul_const _ hf.of_uncurry_right

/-- Pointwise finite positive evidence yields the complete swapped Bayes joint law. -/
lemma bayes_joint (hf : Measurable (Function.uncurry f))
    (hκ : ∀ a, κ a = ν.withDensity (f a))
    {η : Kernel B A} [IsSFiniteKernel η]
    (hη : ∀ b, η b = μ.withDensity (fun a ↦ (∫⁻ a, f a b ∂μ)⁻¹ * f a b))
    (hz0 : ∀ b, (∫⁻ a, f a b ∂μ) ≠ 0)
    (hzt : ∀ b, (∫⁻ a, f a b ∂μ) ≠ ⊤) :
    (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap := by
  rw [marginal_density hf hκ]
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  erw [Measure.lintegral_compProd hg,
    lintegral_withDensity_eq_lintegral_mul _ (hf.lintegral_prod_left' (μ := μ))
      hg.lintegral_kernel_prod_right',
    lintegral_map hg (by fun_prop),
    Measure.lintegral_compProd (by fun_prop)]
  have hηint (b : B) : (∫⁻ a, g (b, a) ∂η b) =
      ∫⁻ a, (∫⁻ a, f a b ∂μ)⁻¹ * f a b * g (b, a) ∂μ := by
    rw [hη]
    exact lintegral_withDensity_eq_lintegral_mul _
      (measurable_const.mul hf.of_uncurry_right) (hg.comp measurable_prodMk_left)
  have hκint (a : A) : (∫⁻ b, g (b, a) ∂κ a) =
      ∫⁻ b, f a b * g (b, a) ∂ν := by
    rw [hκ]
    exact lintegral_withDensity_eq_lintegral_mul _
      hf.of_uncurry_left (hg.comp measurable_prodMk_right)
  simp only [Pi.mul_apply, Prod.swap] 
  simp_rw [hηint, hκint]
  rw [lintegral_lintegral_swap (hf.mul (hg.comp measurable_swap)).aemeasurable]
  congr with b
  erw [← lintegral_const_mul _
    ((measurable_const.mul hf.of_uncurry_right).mul (hg.comp measurable_prodMk_left))]
  congr with a
  dsimp only [Pi.mul_apply, Function.uncurry, Function.comp_apply]
  rw [← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel (hz0 b) (hzt b), one_mul]

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
open AcceleratedLogConcave.Gibbs
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Gaussian regularization is dominated by the original integrable Gibbs density. -/
lemma posterior_integrable_of_base {F : E → ℝ}
    (hF : Measurable F) (hI : Integrable (fun x ↦ Real.exp (-F x)))
    (t : ℝ≥0) (y : E) :
    Integrable (fun x ↦ Real.exp (-(F x + ‖x - y‖ ^ 2 / (2 * (t : ℝ))))) := by
  refine hI.mono' (by fun_prop) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have : 0 ≤ ‖x - y‖ ^ 2 / (2 * (t : ℝ)) := by positivity
  linarith

lemma posterior_kernel_isMarkov {F : E → ℝ}
    (hF : Measurable F) (hI : Integrable (fun x ↦ Real.exp (-F x))) (t : ℝ≥0) :
    IsMarkovKernel (normalizedPosteriorKernel F (fun _ : E ↦ (t : ℝ)) id
      hF measurable_const measurable_id) := by
  constructor
  intro y
  exact normalized_exp_neg_isProbabilityMeasure (posterior_integrable_of_base hF hI t y)

lemma posterior_kernel_eq_tilted_prior {F : E → ℝ}
    (hF : Measurable F) (hI : Integrable (fun x ↦ Real.exp (-F x)))
    (t : ℝ≥0) (y : E) :
    normalizedPosteriorKernel F (fun _ : E ↦ (t : ℝ)) id
      hF measurable_const measurable_id y =
      (volume.tilted (fun x ↦ -F x)).tilted
        (fun x ↦ -‖x - y‖ ^ 2 / (2 * (t : ℝ))) := by
  erw [normalizedPosteriorKernel_apply,
    ennreal_smul_withDensity_eq_tilted volume _ (posterior_integrable_of_base hF hI t y) _ rfl,
    tilted_tilted hI]
  congr 1
  ext x
  simp only [Pi.add_apply]
  ring

lemma posterior_weight_integrable {F : E → ℝ}
    (hF : Measurable F) (hI : Integrable (fun x ↦ Real.exp (-F x)))
    (t : ℝ≥0) (y : E) :
    Integrable (fun x ↦ Real.exp (-‖x - y‖ ^ 2 / (2 * (t : ℝ))))
      (volume.tilted (fun x ↦ -F x)) := by
  rw [integrable_tilted_iff hI]
  convert posterior_integrable_of_base hF hI t y using 1
  ext x
  rw [smul_eq_mul, ← Real.exp_add]
  congr 1
  ring

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
variable {A : Type*} [MeasurableSpace A] (μ : Measure A)

lemma likelihood_lintegral (h : A → ℝ)
    (hi : Integrable (fun a ↦ Real.exp (h a)) μ) (C : ℝ) (hC : 0 < C) :
    (∫⁻ a, ENNReal.ofReal (Real.exp (h a) / C) ∂μ) =
      ENNReal.ofReal ((∫ a, Real.exp (h a) ∂μ) / C) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const C)
    (Filter.Eventually.of_forall (fun a ↦ by positivity)), integral_div]

lemma likelihood_lintegral_pos [NeZero μ] (h : A → ℝ)
    (hi : Integrable (fun a ↦ Real.exp (h a)) μ) (C : ℝ) (hC : 0 < C) :
    0 < ∫⁻ a, ENNReal.ofReal (Real.exp (h a) / C) ∂μ := by
  rw [likelihood_lintegral μ h hi C hC]
  exact ENNReal.ofReal_pos.mpr (div_pos (integral_exp_pos hi) hC)

lemma likelihood_lintegral_ne_top (h : A → ℝ)
    (hi : Integrable (fun a ↦ Real.exp (h a)) μ) (C : ℝ) (hC : 0 < C) :
    (∫⁻ a, ENNReal.ofReal (Real.exp (h a) / C) ∂μ) ≠ ⊤ := by
  rw [likelihood_lintegral μ h hi C hC]
  exact ENNReal.ofReal_ne_top

lemma normalized_likelihood_eq_tilted [NeZero μ] (h : A → ℝ)
    (hi : Integrable (fun a ↦ Real.exp (h a)) μ) (C : ℝ) (hC : 0 < C) :
    μ.withDensity (fun a ↦
      (∫⁻ a, ENNReal.ofReal (Real.exp (h a) / C) ∂μ)⁻¹ *
        ENNReal.ofReal (Real.exp (h a) / C)) = μ.tilted h := by
  rw [likelihood_lintegral μ h hi C hC, Measure.tilted]
  congr 1
  funext a
  have hZ : 0 < ∫ a, Real.exp (h a) ∂μ := integral_exp_pos hi
  rw [← ENNReal.ofReal_inv_of_pos (div_pos hZ hC),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
open AcceleratedLogConcave.Gibbs AcceleratedLogConcave.Channels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The supplied normalized posterior is the actual Gaussian-channel reverse kernel. -/
lemma normalizedPosterior_bayes_joint {F : E → ℝ}
    (hF : Measurable F) (hI : Integrable (fun x ↦ Real.exp (-F x)))
    (t : ℝ≥0) (ht : 0 < t) :
    (forward (volume.tilted (fun x ↦ -F x)) t) ⊗ₘ
        normalizedPosteriorKernel F (fun _ : E ↦ (t : ℝ)) id
          hF measurable_const measurable_id =
      ((volume.tilted (fun x ↦ -F x)) ⊗ₘ forwardKernel t).map Prod.swap := by
  have : IsProbabilityMeasure (volume.tilted (fun x ↦ -F x)) :=
    isProbabilityMeasure_tilted hI
  have := posterior_kernel_isMarkov hF hI t
  rw [← forwardKernel_comp]
  let C : ℝ := ∫ z : E, Real.exp (-‖z‖ ^ 2 / (2 * (t : ℝ)))
  have hC : 0 < C := gaussian_normalizer_pos t ht
  let q : E → E → ℝ≥0∞ := fun x y ↦
    ENNReal.ofReal (Real.exp (-‖x - y‖ ^ 2 / (2 * (t : ℝ))) / C)
  have hq : Measurable (Function.uncurry q) := by dsimp [q]; fun_prop
  apply bayes_joint (ν := volume) hq
  · intro x
    rw [forwardKernel_eq_withDensity t ht x]
    congr 1
    ext y
    dsimp [q, C]
    rw [norm_sub_rev]
  · intro y
    rw [posterior_kernel_eq_tilted_prior hF hI t y]
    exact (normalized_likelihood_eq_tilted _ _
      (posterior_weight_integrable hF hI t y) C hC).symm
  · intro y
    exact (likelihood_lintegral_pos _ _
      (posterior_weight_integrable hF hI t y) C hC).ne'
  · intro y
    exact likelihood_lintegral_ne_top _ _
      (posterior_weight_integrable hF hI t y) C hC

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

lemma noise_half_sum_map (w : ℝ≥0) :
    (noise (ι := ι) (w + w)).map (fun z ↦ (1 / 2 : ℝ) • z) = noise (w / 2) := by
  apply Measure.ext_of_charFun
  ext x
  rw [charFun_map_smul, charFun_noise, charFun_noise]
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2)]
  push_cast
  ring

lemma noise_average_map (w : ℝ≥0) :
    ((noise (ι := ι) w).prod (noise w)).map
      (fun p ↦ (1 / 2 : ℝ) • (p.1 + p.2)) = noise (w / 2) := by
  change ((noise w).prod (noise w)).map
    ((fun z : E ↦ (1 / 2 : ℝ) • z) ∘ (fun p : E × E ↦ p.1 + p.2)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), noise_sum_map, noise_half_sum_map]

noncomputable def bridgeKernel (η : Kernel E E) (w : ℝ≥0) : Kernel E E :=
  (Kernel.id ×ₖ (η ×ₖ Kernel.const _ (noise w))).map
    (fun p ↦ (1 / 2 : ℝ) • (p.1 + p.2.1 + p.2.2))

instance (η : Kernel E E) [IsMarkovKernel η] (w : ℝ≥0) :
    IsMarkovKernel (bridgeKernel η w) := by
  unfold bridgeKernel
  apply Kernel.IsMarkovKernel.map
  fun_prop

lemma lintegral_bridgeKernel (η : Kernel E E) [IsMarkovKernel η] (w : ℝ≥0)
    (y : E) (f : E → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂(bridgeKernel η w y) =
      ∫⁻ a, ∫⁻ z, f ((1 / 2 : ℝ) • (y + a + z)) ∂noise w ∂η y := by
  rw [bridgeKernel, Kernel.lintegral_map _ (by fun_prop) _ hf,
    Kernel.lintegral_id_prod (by fun_prop), Kernel.lintegral_prod _ _ _ (by fun_prop)]
  rfl

lemma swap_joint_lintegral (μ : Measure E) [IsProbabilityMeasure μ]
    (η : Kernel E E) [IsMarkovKernel η] (w : ℝ≥0)
    (hBayes : (forward μ w) ⊗ₘ η = (μ ⊗ₘ forwardKernel w).map Prod.swap)
    (g : E × E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, ∫⁻ a, g (y,a) ∂η y ∂forward μ w) =
      ∫⁻ a, ∫⁻ y, g (y,a) ∂forwardKernel w a ∂μ := by
  have : IsProbabilityMeasure (forward μ w) := by unfold forward; infer_instance
  rw [← Measure.lintegral_compProd hg, hBayes, lintegral_map hg measurable_swap,
    Measure.lintegral_compProd (by fun_prop)]
  rfl

lemma bridge_equal_width (μ : Measure E) [IsProbabilityMeasure μ]
    (η : Kernel E E) [IsMarkovKernel η] (w : ℝ≥0)
    (hBayes : (forward μ w) ⊗ₘ η = (μ ⊗ₘ forwardKernel w).map Prod.swap) :
    bridgeKernel η w ∘ₘ forward μ w = forward μ (w / 2) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
  simp_rw [lintegral_bridgeKernel η w _ f hf]
  rw [swap_joint_lintegral μ η w hBayes
    (fun p ↦ ∫⁻ z, f ((1 / 2 : ℝ) • (p.1 + p.2 + z)) ∂noise w)
    (by fun_prop)]
  rw [forward, Measure.lintegral_conv hf]
  apply lintegral_congr
  intro a
  rw [forwardKernel_apply, lintegral_map (by fun_prop) (by fun_prop)]
  have halg (z v : E) : (1 / 2 : ℝ) • (a + z + a + v) =
      a + (1 / 2 : ℝ) • (z + v) := by module
  simp_rw [halg]
  rw [← lintegral_prod (f := fun p : E × E ↦ f (a + (1 / 2 : ℝ) • (p.1 + p.2))) (by fun_prop)]
  rw [← lintegral_map (by fun_prop : Measurable (fun z : E ↦ f (a + z))) (by fun_prop),
    noise_average_map]

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
lemma bridgeKernel_apply (η : Kernel E E) [IsMarkovKernel η] (w : ℝ≥0) (y : E) :
    bridgeKernel η w y = ((η y).prod (noise w)).map
      (fun p ↦ (1 / 2 : ℝ) • (y + p.1 + p.2)) := by
  rw [bridgeKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop), Kernel.prod_apply, Kernel.const_apply]
  rfl
end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
open AcceleratedLogConcave.Gibbs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Posterior draw plus a fresh independent Gaussian reserve, then midpoint decoding. -/
noncomputable def equalWidthBridge (F : E → ℝ) (hF : Measurable F) (w : ℝ≥0) :
    Kernel E E :=
  bridgeKernel (normalizedPosteriorKernel F (fun _ : E ↦ (w : ℝ)) id
    hF measurable_const measurable_id) w

lemma equalWidthBridge_isMarkov {F : E → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x ↦ Real.exp (-F x))) (w : ℝ≥0) :
    IsMarkovKernel (equalWidthBridge F hF w) := by
  have := posterior_kernel_isMarkov hF hI w
  unfold equalWidthBridge
  infer_instance

/-- Concrete fresh-reserve representation at every retained input y. -/
lemma equalWidthBridge_apply {F : E → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x ↦ Real.exp (-F x))) (w : ℝ≥0) (y : E) :
    equalWidthBridge F hF w y =
      ((normalizedPosteriorKernel F (fun _ : E ↦ (w : ℝ)) id
        hF measurable_const measurable_id y).prod (noise w)).map
          (fun p ↦ (1 / 2 : ℝ) • (y + p.1 + p.2)) := by
  have := posterior_kernel_isMarkov hF hI w
  exact bridgeKernel_apply _ w y

/-- The exact equal-width reverse bridge sends pi_w to pi_(w/2). -/
theorem equalWidthBridge_comp_forward {F : E → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x ↦ Real.exp (-F x))) (w : ℝ≥0) (hw : 0 < w) :
    equalWidthBridge F hF w ∘ₘ forward (volume.tilted (fun x ↦ -F x)) w =
      forward (volume.tilted (fun x ↦ -F x)) (w / 2) := by
  have : IsProbabilityMeasure (volume.tilted (fun x ↦ -F x)) :=
    isProbabilityMeasure_tilted hI
  have := posterior_kernel_isMarkov hF hI w
  exact bridge_equal_width _ _ w (normalizedPosterior_bayes_joint hF hI w hw)

/-- The same identity for a supplied Gibbs law identified through MeasureBridge. -/
theorem equalWidthBridge_comp_forward_of_gibbs (μ : Measure E) {F : E → ℝ}
    (hF : Measurable F) (hI : Integrable (fun x ↦ Real.exp (-F x)))
    (hμ : μ = volume.tilted (fun x ↦ -F x)) (w : ℝ≥0) (hw : 0 < w) :
    equalWidthBridge F hF w ∘ₘ forward μ w = forward μ (w / 2) := by
  rw [hμ]
  exact equalWidthBridge_comp_forward hF hI w hw

end AcceleratedLogConcave.Channels
