import AcceleratedLogConcave.Channels.EqualWidthBridge
import AcceleratedLogConcave.Channels.GaussianReverseKL
import AcceleratedLogConcave.Gibbs.PrimitiveMoments

/-!
# Cooling KL from a supplied measurable pre-reserve coupling

The decoder adds independent noise of variance `1/4` in the standardized
primitive coordinate and then applies `z ↦ x + sqrt(w) • z / 2`.
Its physical reserve covariance is therefore `w I / 16`.
The exact reference before that reserve is the primitive posterior convolved
with variance `3/4`. All identities are derived from the pinned measure laws.

The final bound is exact-to-implemented, with factor `2`, averaged under the
exact input Gibbs law at width `w`. The measurable Markov coupling kernel `J`
is supplied explicitly. No measurable selection or compiler run law is claimed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace AcceleratedLogConcave.Channels
open Gibbs
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Independent standardized variance-`1/4` reserve followed by affine decoding. -/
def reservedDecoder (pre : Kernel E E) (w : ℝ≥0) : Kernel E E :=
  (Kernel.id ×ₖ (pre ×ₖ Kernel.const _ (noise (1 / 4)))).map
    (fun p ↦ p.1 + (Real.sqrt (w : ℝ) / 2) • (p.2.1 + p.2.2))

instance reservedDecoder_isMarkov (pre : Kernel E E) [IsMarkovKernel pre] (w : ℝ≥0) :
    IsMarkovKernel (reservedDecoder pre w) := by
  unfold reservedDecoder
  apply Kernel.IsMarkovKernel.map
  fun_prop

/-- The reserve is a product with the complete pre-reserve output law. -/
theorem reservedDecoder_apply (pre : Kernel E E) [IsMarkovKernel pre]
    (w : ℝ≥0) (x : E) :
    reservedDecoder pre w x = ((pre x).prod (noise (1 / 4))).map
      (fun p ↦ x + (Real.sqrt (w : ℝ) / 2) • (p.1 + p.2)) := by
  rw [reservedDecoder, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop), Kernel.prod_apply, Kernel.const_apply]
  rfl

theorem reservedDecoder_eq_map_forward (pre : Kernel E E) [IsMarkovKernel pre]
    (w : ℝ≥0) (x : E) :
    reservedDecoder pre w x = (forward (pre x) (1 / 4)).map
      (fun z ↦ x + (Real.sqrt (w : ℝ) / 2) • z) := by
  rw [reservedDecoder_apply]
  change _ = (((pre x).prod (noise (1 / 4))).map (fun p ↦ p.1 + p.2)).map _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The standardized primitive coordinate maps to the physical posterior at width `w`. -/
theorem primitiveLaw_map_sqrt {V : E → ℝ} (hV : Measurable V)
    (w : ℝ≥0) (hw : 0 < w) (x : E) :
    (primitiveLaw V x (Real.sqrt (w : ℝ))).map
      (fun z ↦ x + Real.sqrt (w : ℝ) • z) =
      normalizedPosteriorKernel V (fun _ : E ↦ (w : ℝ)) id
        hV measurable_const measurable_id x := by
  have h : (primitiveLaw V x (Real.sqrt (w : ℝ))).map
      (fun z ↦ x + Real.sqrt (w : ℝ) • z) =
      heatPosterior V ((Real.sqrt (w : ℝ)) ^ 2) x :=
    primitiveLaw_map_affine hV (Real.sqrt_pos.mpr hw).ne' x
  simpa only [Real.sq_sqrt w.coe_nonneg,
    heatPosterior_eq_normalizedPosteriorKernel hV] using h

theorem primitiveLaw_sqrt_isProbability {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x)))
    (w : ℝ≥0) (hw : 0 < w) (x : E) :
    IsProbabilityMeasure (primitiveLaw V x (Real.sqrt (w : ℝ))) := by
  have := posterior_kernel_isMarkov hV hI w
  have hm := primitiveLaw_map_sqrt hV w hw x
  have hp : IsProbabilityMeasure ((primitiveLaw V x (Real.sqrt (w : ℝ))).map
      (fun z ↦ x + Real.sqrt (w : ℝ) • z)) := by
    rw [hm]
    infer_instance
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mp hp

/-- For the oracle potential `F(z) = V(sqrt(h) • z)`, the manuscript's
center `x / sqrt(h)` and radius `sqrt(w / h)` give the same standardized law.
This is a density identity, not a compiler output-law instantiation. -/
theorem primitiveLaw_oracle_coordinates (V : E → ℝ) (h : ℝ) (hh : 0 < h)
    (w : ℝ≥0) (x : E) :
    primitiveLaw (fun z ↦ V (Real.sqrt h • z))
      ((Real.sqrt h)⁻¹ • x) (Real.sqrt ((w : ℝ) / h)) =
      primitiveLaw V x (Real.sqrt (w : ℝ)) := by
  have hs : Real.sqrt h ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  have hr : Real.sqrt h * Real.sqrt ((w : ℝ) / h) = Real.sqrt (w : ℝ) := by
    rw [Real.sqrt_div w.coe_nonneg]
    field_simp
  unfold primitiveLaw
  congr 1
  funext z
  dsimp only
  congr 1
  rw [smul_add, smul_smul, smul_smul, mul_inv_cancel₀ hs, one_smul, hr]

/-- The exact bridge is affine decoding of a primitive draw plus unit Gaussian noise. -/
theorem equalWidthBridge_eq_map_forward_primitive {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x)))
    (w : ℝ≥0) (hw : 0 < w) (x : E) :
    equalWidthBridge V hV w x =
      (forward (primitiveLaw V x (Real.sqrt (w : ℝ))) 1).map
        (fun z ↦ x + (Real.sqrt (w : ℝ) / 2) • z) := by
  have := primitiveLaw_sqrt_isProbability hV hI w hw x
  have hnoise : noise (ι := Fin d) 1 = stdGaussian E := by
    simp [noise_eq_scaled_stdGaussian]
  rw [equalWidthBridge_apply hV hI, ← primitiveLaw_map_sqrt hV w hw x,
    noise_eq_scaled_stdGaussian, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rw [forward, hnoise]
  change _ = (((primitiveLaw V x (Real.sqrt (w : ℝ))).prod (stdGaussian E)).map
    (fun p ↦ p.1 + p.2)).map _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  dsimp
  module

/-- The exact `3/4 + 1/4` split, before the common affine decoder. -/
theorem equalWidthBridge_eq_map_reserve_split {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x)))
    (w : ℝ≥0) (hw : 0 < w) (x : E) :
    equalWidthBridge V hV w x =
      (forward (forward (primitiveLaw V x (Real.sqrt (w : ℝ))) (3 / 4)) (1 / 4)).map
        (fun z ↦ x + (Real.sqrt (w : ℝ) / 2) • z) := by
  rw [forward_add]
  norm_num
  exact equalWidthBridge_eq_map_forward_primitive hV hI w hw x

/-- The physical covariance of the final reserve is `w I / 16`, including at zero width. -/
theorem noise_quarter_map_decoder_scale (w : ℝ≥0) :
    (noise (ι := Fin d) (1 / 4)).map (fun z ↦ (Real.sqrt (w : ℝ) / 2) • z) =
      noise (w / 16) := by
  apply Measure.ext_of_charFun
  ext z
  rw [charFun_map_smul, charFun_noise, charFun_noise, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (w : ℝ) / 2)]
  rw [mul_pow, div_pow, Real.sq_sqrt w.coe_nonneg]
  push_cast
  congr 1
  ring

private theorem forward_map_quarter {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) (hf : Measurable f) :
    forward (μ.map f) (1 / 4) = ((μ.prod (stdGaussian E)).map
      (fun p ↦ f p.1 + (1 / 2 : ℝ) • p.2)) := by
  have hs : Real.sqrt ((1 / 4 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [forward, noise_eq_scaled_stdGaussian, hs]
  change ((μ.map f).prod ((stdGaussian E).map (fun z ↦ (1 / 2 : ℝ) • z))).map
    (fun p ↦ p.1 + p.2) = _
  rw [Measure.map_prod_map _ _ hf (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A variance-`1/4` independent reserve turns a supplied coupling's squared
displacement into exact-to-implemented KL with coefficient `2`. -/
theorem klDiv_forward_quarter_le_coupling (ξ : Measure (E × E)) [IsFiniteMeasure ξ] :
    klDiv (forward (ξ.map Prod.fst) (1 / 4)) (forward (ξ.map Prod.snd) (1 / 4)) ≤
      ∫⁻ uv, ENNReal.ofReal (2 * ‖uv.1 - uv.2‖ ^ 2) ∂ξ := by
  let A : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft
    (Units.mk0 (1 / 2 : ℝ) (by norm_num))
  have hA (z : E) : A z = (1 / 2 : ℝ) • z := rfl
  have hAinv (z : E) : A.symm z = (2 : ℝ) • z := by
    change ((1 / 2 : ℝ)⁻¹) • z = _
    norm_num
  have hcost (uv : E × E) : ENNReal.ofReal (‖A.symm (uv.1 - uv.2)‖ ^ 2 / 2) =
      ENNReal.ofReal (2 * ‖uv.1 - uv.2‖ ^ 2) := by
    rw [hAinv, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [forward_map_quarter ξ Prod.fst measurable_fst,
    forward_map_quarter ξ Prod.snd measurable_snd]
  simpa only [hA, hcost] using
    gaussian_reverse_transport ξ d A Prod.fst Prod.snd measurable_fst measurable_snd

/-- Pointwise comparison under the explicitly supplied measurable Markov coupling.
The hypotheses identify only its marginals; they assume no KL conclusion. -/
theorem cooling_localKL_pointwise_of_preCoupling
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x)))
    (w : ℝ≥0) (hw : 0 < w)
    (pre : Kernel E E) [IsMarkovKernel pre]
    (J : Kernel E (E × E)) [IsMarkovKernel J]
    (hleft : ∀ x, (J x).map Prod.fst =
      forward (primitiveLaw V x (Real.sqrt (w : ℝ))) (3 / 4))
    (hright : ∀ x, (J x).map Prod.snd = pre x) (x : E) :
    klDiv (equalWidthBridge V hV w x) (reservedDecoder pre w x) ≤
      ∫⁻ uv, ENNReal.ofReal (2 * ‖uv.1 - uv.2‖ ^ 2) ∂J x := by
  rw [equalWidthBridge_eq_map_reserve_split hV hI w hw x,
    reservedDecoder_eq_map_forward, ← hleft x, ← hright x]
  have : IsFiniteMeasure (forward ((J x).map Prod.fst) (1 / 4)) := by
    unfold forward
    infer_instance
  have : IsFiniteMeasure (forward ((J x).map Prod.snd) (1 / 4)) := by
    unfold forward
    infer_instance
  exact (klDiv_map_le _ _ (by fun_prop)).trans (klDiv_forward_quarter_le_coupling (J x))

/-- Averaged cooling supplier at the exact input law. The target Gibbs law is
written explicitly because the pinned base has no separate `targetLaw` name. -/
theorem cooling_localKL_of_preCoupling
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x)))
    (w : ℝ≥0) (hw : 0 < w)
    (pre : Kernel E E) [IsMarkovKernel pre]
    (J : Kernel E (E × E)) [IsMarkovKernel J]
    (hleft : ∀ x, (J x).map Prod.fst =
      forward (primitiveLaw V x (Real.sqrt (w : ℝ))) (3 / 4))
    (hright : ∀ x, (J x).map Prod.snd = pre x) :
    (∫⁻ x, klDiv (equalWidthBridge V hV w x)
      (reservedDecoder pre w x) ∂forward (volume.tilted (fun x ↦ -V x)) w) ≤
    ∫⁻ x, ∫⁻ uv, ENNReal.ofReal (2 * ‖uv.1 - uv.2‖ ^ 2)
      ∂J x ∂forward (volume.tilted (fun x ↦ -V x)) w := by
  exact lintegral_mono (cooling_localKL_pointwise_of_preCoupling
    hV hI w hw pre J hleft hright)

end AcceleratedLogConcave.Channels
