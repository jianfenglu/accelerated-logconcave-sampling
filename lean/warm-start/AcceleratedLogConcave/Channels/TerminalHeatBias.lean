import AcceleratedLogConcave.Gibbs.CenteredQuadratic
import AcceleratedLogConcave.Gibbs.IntegrationByParts
import AcceleratedLogConcave.Channels.GaussianForward
import AcceleratedLogConcave.Channels.GaussianReverseKL
import AcceleratedLogConcave.Probability.Entropy
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Terminal heat bias for the original Gibbs measure

The original potential is only C². Normalization, position moments, score
integrability, and the mean-zero score are derived from its Hessian bounds.
The translation law is `Law(X + z)` and KL is directed toward the original
Gibbs measure. Heat width denotes covariance and may be zero. No warmness
parameter occurs.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace AcceleratedLogConcave.Channels

private lemma terminal_density_integrable {d : ℕ}
    {V : EuclideanSpace ℝ (Fin d) → ℝ} {κ : ℝ}
    (hκ : 1 ≤ κ) (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v) :
    Integrable (fun x ↦ Real.exp (-V x)) := by
  exact Gibbs.integrable_exp_neg_of_hessian_lower hV
    (inv_pos.mpr (by linarith)) hlo

private lemma terminal_score_data {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    {V : EuclideanSpace ℝ (Fin d) → ℝ} {κ : ℝ}
    (hκ : 1 ≤ κ) (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hhi : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ ‖v‖ ^ 2)
    (hμ : μ = volume.tilted (fun x ↦ -V x)) :
    Integrable (gradient V) μ ∧ (∫ x, gradient V x ∂μ) = 0 := by
  have hm : 0 < κ⁻¹ := inv_pos.mpr (by linarith)
  have hZ := terminal_density_integrable hκ hV hlo
  have hp : Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ 2)
      (volume.tilted (fun x ↦ -V x)) := by
    apply (integrable_tilted_iff hZ _).mpr
    simpa only [smul_eq_mul, mul_comm] using
      Gibbs.integrable_norm_pow_mul_exp_neg_of_hessian_lower hV hm hlo 2
  have hu : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ 1 * ‖v‖ ^ 2 := by
    simpa only [one_mul] using hhi
  rw [hμ]
  exact ⟨Gibbs.integrable_tilted_gradient_of_hessian_bounds hV hlo hu hp,
    Gibbs.integral_tilted_gradient_eq_zero_of_hessian_bounds hV hZ hlo hu hp⟩

private lemma terminal_translation_energy {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    {V : EuclideanSpace ℝ (Fin d) → ℝ} {κ : ℝ}
    (hκ : 1 ≤ κ) (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hhi : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ ‖v‖ ^ 2)
    (hμ : μ = volume.tilted (fun x ↦ -V x))
    (z : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x ↦ V (x + z) - V x) μ ∧
      (∫ x, V (x + z) - V x ∂μ) ≤ ‖z‖ ^ 2 / 2 := by
  obtain ⟨hg, hzero⟩ := terminal_score_data μ hκ hV hlo hhi hμ
  have hs : Integrable (fun x ↦ fderiv ℝ V x z) μ := by
    simpa only [innerSL_apply_apply, inner_gradient_right, conj_trivial] using
      (innerSL ℝ z).integrable_comp hg
  have hs0 : (∫ x, fderiv ℝ V x z ∂μ) = 0 := by
    have hc := (innerSL ℝ z).integral_comp_comm hg
    simp only [innerSL_apply_apply, inner_gradient_right, conj_trivial] at hc
    rw [hzero, inner_zero_right] at hc
    exact hc
  have hup (x : EuclideanSpace ℝ (Fin d)) :
      V (x + z) - V x ≤ fderiv ℝ V x z + ‖z‖ ^ 2 / 2 := by
    have h := Gibbs.quadratic_upper_bound_at_of_hessian_upper hV
      (L := 1) (by simpa only [one_mul] using hhi) x z
    linarith
  have hlow (x : EuclideanSpace ℝ (Fin d)) :
      fderiv ℝ V x z ≤ V (x + z) - V x := by
    have h := Gibbs.quadratic_lower_bound_at_of_hessian_lower hV hlo x z
    have hn : 0 ≤ κ⁻¹ / 2 * ‖z‖ ^ 2 :=
      mul_nonneg (div_nonneg (inv_nonneg.mpr (by linarith)) (by norm_num)) (sq_nonneg _)
    linarith
  have hi : Integrable (fun x ↦ V (x + z) - V x) μ := by
    refine (hs.abs.add (integrable_const (‖z‖ ^ 2 / 2))).mono'
      ((hV.continuous.comp (continuous_id.add continuous_const)).sub
        hV.continuous).aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    apply abs_le.mpr
    constructor
    · linarith [hlow x, neg_abs_le (fderiv ℝ V x z), sq_nonneg (‖z‖)]
    · linarith [hup x, le_abs_self (fderiv ℝ V x z)]
  refine ⟨hi, ?_⟩
  have hb := integral_mono hi (hs.add (integrable_const (‖z‖ ^ 2 / 2))) hup
  simp only [Pi.add_apply] at hb
  rw [integral_add hs (integrable_const _), hs0, integral_const,
    probReal_univ, one_smul, zero_add] at hb
  exact hb

private lemma terminal_translation_kl_eq {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : Measurable V)
    (hZ : Integrable (fun x ↦ Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x ↦ -V x))
    (z : EuclideanSpace ℝ (Fin d))
    (hi : Integrable (fun x ↦ V (x + z) - V x) μ) :
    klDiv (μ.map (fun x ↦ x + z)) μ =
      ENNReal.ofReal (∫ x, V (x + z) - V x ∂μ) := by
  let ν := μ.map (fun x ↦ x + z)
  have hν : ν = volume.tilted (fun y ↦ -V (y - z)) := by
    dsimp only [ν]
    rw [hμ]
    simpa only [add_comm] using map_tilted_add (fun x ↦ -V x) z
  have hacvol : ν ≪ volume := by
    rw [hν]
    exact tilted_absolutelyContinuous _ _
  have hac : ν ≪ μ := by
    rw [hμ]
    exact hacvol.trans (absolutelyContinuous_tilted hZ)
  have hZz : Integrable (fun y ↦ Real.exp (-V (y - z))) := hZ.comp_sub_right z
  have hleft : llr ν volume =ᵐ[ν] fun y ↦
      -V (y - z) - Real.log (∫ x, Real.exp (-V x)) := by
    have h := llr_tilted_left (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
      Measure.AbsolutelyContinuous.rfl hZz (by fun_prop)
    have h' : llr ν volume =ᵐ[volume] fun y ↦
        -V (y - z) - Real.log (∫ x, Real.exp (-V x)) := by
      rw [hν]
      filter_upwards [h, llr_self (volume : Measure (EuclideanSpace ℝ (Fin d)))] with y hy hy0
      rw [hy, hy0, Pi.zero_apply, add_zero,
        integral_sub_right_eq_self (fun x : EuclideanSpace ℝ (Fin d) ↦ Real.exp (-V x)) z]
    exact hacvol.ae_le h'
  have heq : llr ν μ =ᵐ[ν] fun y ↦ V y - V (y - z) := by
    rw [hμ]
    filter_upwards [llr_tilted_right hacvol hZ, hleft] with y hy hy'
    rw [hy, hy']
    ring
  have hI : Integrable (fun y ↦ V y - V (y - z)) ν := by
    dsimp only [ν]
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    simpa only [Function.comp_def, add_sub_cancel_right] using hi
  have hllr : Integrable (llr ν μ) ν := hI.congr heq.symm
  change klDiv ν μ = _
  rw [klDiv_of_ac_of_integrable hac hllr, probReal_univ, probReal_univ, add_sub_cancel_right]
  congr 1
  calc
    (∫ y, llr ν μ y ∂ν) = ∫ y, V y - V (y - z) ∂ν := integral_congr_ae heq
    _ = ∫ x, V (x + z) - V x ∂μ := by
      dsimp only [ν]
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [add_sub_cancel_right]

namespace TerminalHeatBiasAux

variable {d : ℕ}

/-- Convexity of KL for the concrete fresh Gaussian translation mixture. -/
theorem klDiv_forward_le_lintegral_translated
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (w : ℝ≥0) (hac : ∀ z, μ.map (fun x ↦ x + z) ≪ μ) :
    klDiv (forward μ w) μ ≤
      ∫⁻ z, klDiv (μ.map (fun x ↦ x + z)) μ ∂noise w := by
  let F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) := fun p ↦ p.2 + p.1
  have hF : Measurable F := measurable_snd.add measurable_fst
  have h := klDiv_map_compProd_le_lintegral_of_ac
    (noise (ι := Fin d) w) (freshKernel μ F hF)
    (Kernel.const (EuclideanSpace ℝ (Fin d)) μ) hac Prod.snd measurable_snd
  have hleft : ((noise w ⊗ₘ freshKernel μ F hF).map Prod.snd) = forward μ w := by
    rw [compProd_freshKernel, Measure.map_map measurable_snd
      (measurable_fst.prodMk hF)]
    change ((noise w).prod μ).map (fun p ↦ p.2 + p.1) = μ ∗ noise w
    rw [Measure.conv_comm]
    congr 1
    funext p
    exact add_comm _ _
  rw [hleft] at h
  simpa only [Measure.compProd_const, Measure.map_snd_prod, measure_univ, one_smul,
    freshKernel, F, Kernel.const_apply, Kernel.coe_mk] using h

/-- A standard Gaussian has the dimension as its exact squared norm moment.
The coordinate-sum proof is adapted from `Gibbs.PrimitiveMoments` at the pinned base,
without importing its larger project dependency closure. -/
theorem integral_norm_sq_stdGaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    (∫ z : E, ‖z‖ ^ 2 ∂stdGaussian E) = (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hcoord (v : E) : ∫ z, (inner ℝ v z) ^ 2 ∂stdGaussian E = ‖v‖ ^ 2 := by
    have h := covarianceBilin_apply (IsGaussian.memLp_two_id (μ := stdGaussian E)) v v
    rw [covarianceBilin_stdGaussian] at h
    change inner ℝ v v = _ at h
    simpa only [integral_id_stdGaussian, id_eq, sub_zero, ← pow_two,
      real_inner_self_eq_norm_sq] using h.symm
  simp_rw [← b.sum_sq_inner_right]
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun z => inner ℝ (b i) z ^ 2) (stdGaussian E) := by
    simpa only [id_eq] using
      ((IsGaussian.memLp_two_id (μ := stdGaussian E)).const_inner (b i)).integrable_sq
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [hcoord, b.norm_eq_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Squared norms are integrable against every Gaussian noise, including zero variance. -/
theorem integrable_norm_sq_noise (w : ℝ≥0) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) ↦ ‖z‖ ^ 2) (noise w) := by
  unfold noise
  exact (IsGaussian.memLp_two_id (μ := multivariateGaussian 0
    ((w : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)))).norm.integrable_sq

/-- Exact second moment of the covariance-`w I` Gaussian noise, including zero variance. -/
theorem integral_norm_sq_noise (w : ℝ≥0) :
    (∫ z : EuclideanSpace ℝ (Fin d), ‖z‖ ^ 2 ∂noise w) = (d : ℝ) * (w : ℝ) := by
  rw [noise_eq_scaled_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt w.coe_nonneg]
  rw [integral_const_mul, integral_norm_sq_stdGaussian]
  simp [mul_comm]

/-- The exact Gaussian integral used by the terminal KL estimate. -/
theorem lintegral_half_norm_sq_noise (w : ℝ≥0) :
    (∫⁻ z : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (‖z‖ ^ 2 / 2) ∂noise w) =
      ENNReal.ofReal ((d : ℝ) * (w : ℝ) / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_norm_sq_noise w).div_const 2)
    (Filter.Eventually.of_forall (fun z ↦ div_nonneg (sq_nonneg ‖z‖) (by norm_num)))]
  rw [integral_div, integral_norm_sq_noise]

end TerminalHeatBiasAux

/-- Translation KL for the original normalized C² Gibbs law.
The shifted law is `Law(X + z)` and the reference is the original `μ`. -/
theorem klDiv_translate_gibbs_le {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (V : EuclideanSpace ℝ (Fin d) → ℝ) (κ : ℝ)
    (hκ : 1 ≤ κ) (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v : EuclideanSpace ℝ (Fin d),
      κ⁻¹ * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hhi : ∀ x v : EuclideanSpace ℝ (Fin d),
      (fderiv ℝ (fderiv ℝ V) x v) v ≤ ‖v‖ ^ 2)
    (hμ : μ = volume.tilted (fun x ↦ -V x))
    (z : EuclideanSpace ℝ (Fin d)) :
    klDiv (μ.map (fun x ↦ x + z)) μ ≤ ENNReal.ofReal (‖z‖ ^ 2 / 2) := by
  obtain ⟨hi, hb⟩ := terminal_translation_energy μ hκ hV hlo hhi hμ z
  rw [terminal_translation_kl_eq μ hV.continuous.measurable
    (terminal_density_integrable hκ hV hlo) hμ z hi]
  exact ENNReal.ofReal_le_ofReal hb

/-- Terminal heat KL bias, with covariance width `w ≥ 0` and no warmness input. -/
theorem klDiv_forward_gibbs_le {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (V : EuclideanSpace ℝ (Fin d) → ℝ) (κ : ℝ)
    (hκ : 1 ≤ κ) (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v : EuclideanSpace ℝ (Fin d),
      κ⁻¹ * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hhi : ∀ x v : EuclideanSpace ℝ (Fin d),
      (fderiv ℝ (fderiv ℝ V) x v) v ≤ ‖v‖ ^ 2)
    (hμ : μ = volume.tilted (fun x ↦ -V x)) (w : ℝ≥0) :
    klDiv (forward μ w) μ ≤ ENNReal.ofReal ((d : ℝ) * (w : ℝ) / 2) := by
  have ht := klDiv_translate_gibbs_le μ V κ hκ hV hlo hhi hμ
  have hac (z : EuclideanSpace ℝ (Fin d)) : μ.map (fun x ↦ x + z) ≪ μ :=
    (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (ht z))).1
  calc
    klDiv (forward μ w) μ ≤
        ∫⁻ z, klDiv (μ.map (fun x ↦ x + z)) μ ∂noise w :=
      TerminalHeatBiasAux.klDiv_forward_le_lintegral_translated μ w hac
    _ ≤ ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2 / 2) ∂noise w := lintegral_mono ht
    _ = ENNReal.ofReal ((d : ℝ) * (w : ℝ) / 2) :=
      TerminalHeatBiasAux.lintegral_half_norm_sq_noise w

/-- Terminal bias in the project's event-supremum TV convention, including `w = 0`. -/
theorem totalVariationDistance_forward_gibbs_le {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (V : EuclideanSpace ℝ (Fin d) → ℝ) (κ : ℝ)
    (hκ : 1 ≤ κ) (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v : EuclideanSpace ℝ (Fin d),
      κ⁻¹ * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hhi : ∀ x v : EuclideanSpace ℝ (Fin d),
      (fderiv ℝ (fderiv ℝ V) x v) v ≤ ‖v‖ ^ 2)
    (hμ : μ = volume.tilted (fun x ↦ -V x)) (w : ℝ≥0) :
    letI : IsProbabilityMeasure (forward μ w) := by
      unfold forward
      infer_instance
    Probability.totalVariationDistance (forward μ w) μ ≤
      Real.sqrt ((d : ℝ) * (w : ℝ)) / 2 := by
  let : IsProbabilityMeasure (forward μ w) := by
    unfold forward
    infer_instance
  have hkl := klDiv_forward_gibbs_le μ V κ hκ hV hlo hhi hμ w
  have hf : klDiv (forward μ w) μ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have hn : 0 ≤ (d : ℝ) * (w : ℝ) := mul_nonneg (Nat.cast_nonneg _) w.coe_nonneg
  have hr : (klDiv (forward μ w) μ).toReal ≤ (d : ℝ) * (w : ℝ) / 2 := by
    have h := (ENNReal.toReal_le_toReal hf ENNReal.ofReal_ne_top).mpr hkl
    rwa [ENNReal.toReal_ofReal (div_nonneg hn (show (0 : ℝ) ≤ 2 by norm_num))] at h
  have hp := Probability.two_mul_totalVariationDistance_sq_le_toReal_klDiv
    (forward μ w) μ hf
  have hs := Real.sq_sqrt hn
  have hs0 := Real.sqrt_nonneg ((d : ℝ) * (w : ℝ))
  nlinarith [sq_nonneg (Probability.totalVariationDistance (forward μ w) μ -
    Real.sqrt ((d : ℝ) * (w : ℝ)) / 2)]

end AcceleratedLogConcave.Channels
