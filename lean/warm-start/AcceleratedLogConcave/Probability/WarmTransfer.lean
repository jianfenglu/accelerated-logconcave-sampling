import AcceleratedLogConcave.Probability.Entropy

/-!
# L2-warm transfer of a mean conditional KL bound

This is the conditional Pinsker/Cauchy–Schwarz step of `lem:warm-path-kl`.
The local entropy is exact-to-implemented. Every real entropy integral has an
explicit integrability hypothesis; the extended-valued interface derives this
and almost-everywhere finiteness from its finite mean bound.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Probability

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

private lemma integral_product_sq_le (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have inner_integral (u v : X → ℝ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
      inner ℝ (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
    simp [hx, hy, RCLike.inner_apply, mul_comm]
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  simpa only [inner_integral f g hf hg, inner_integral f f hf hf,
    inner_integral g g hg hg, pow_two] using h

private lemma kernel_real_comp_apply (ν : Measure X) (P : Kernel X Y)
    [IsMarkovKernel P] (s : Set Y) (hs : MeasurableSet s) :
    (P ∘ₘ ν).real s = ∫ x, (P x).real s ∂ν := by
  change ((P ∘ₘ ν) s).toReal = ∫ x, (P x s).toReal ∂ν
  rw [Measure.bind_apply hs P.aemeasurable]
  exact (integral_toReal (P.measurable_coe hs).aemeasurable
    (Filter.Eventually.of_forall fun x => measure_lt_top (P x) s)).symm

/-- Conditional Pinsker and Cauchy–Schwarz transfer a finite mean local KL
bound through an L2-warm initial law. No uniform local error bound is used. -/
theorem totalVariationDistance_comp_le_sqrt_of_mean_kl
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P Q : Kernel X Y) [IsMarkovKernel P] [IsMarkovKernel Q]
    (hνμ : ν ≪ μ) (B D : ℝ)
    (hRN : Integrable (fun x => ((ν.rnDeriv μ x).toReal) ^ 2) μ)
    (hB : (∫ x, ((ν.rnDeriv μ x).toReal) ^ 2 ∂μ) ≤ B)
    (hfinite : ∀ᵐ x ∂μ, klDiv (P x) (Q x) ≠ ∞)
    (hKL : Integrable (fun x => (klDiv (P x) (Q x)).toReal) μ)
    (hD : (∫ x, (klDiv (P x) (Q x)).toReal ∂μ) ≤ D) :
    totalVariationDistance (P ∘ₘ ν) (Q ∘ₘ ν) ≤ Real.sqrt (B / 2 * D) := by
  let f : X → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hf : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq (Measure.measurable_rnDeriv ν μ).ennreal_toReal.aestronglyMeasurable).mpr hRN
  have hB0 : 0 ≤ B := (integral_nonneg fun x => sq_nonneg (f x)).trans hB
  apply totalVariationDistance_le_of_forall
  intro s hs
  let g : X → ℝ := fun x => (P x).real s - (Q x).real s
  have hgm : Measurable g :=
    (P.measurable_coe hs).ennreal_toReal.sub (Q.measurable_coe hs).ennreal_toReal
  have hgb : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    change |(P x).real s - (Q x).real s| ≤ 1
    have hp0 : 0 ≤ (P x).real s := measureReal_nonneg
    have hq0 : 0 ≤ (Q x).real s := measureReal_nonneg
    have hp1 : (P x).real s ≤ 1 := measureReal_le_one
    have hq1 : (Q x).real s ≤ 1 := measureReal_le_one
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hg : MemLp g 2 μ := MemLp.of_bound hgm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hgb)
  have hevent : (P ∘ₘ ν).real s - (Q ∘ₘ ν).real s = ∫ x, f x * g x ∂μ := by
    rw [integral_toReal_rnDeriv_mul hνμ]
    rw [kernel_real_comp_apply ν P s hs, kernel_real_comp_apply ν Q s hs]
    apply (integral_sub _ _).symm
    · exact (MemLp.of_bound (P.measurable_coe hs).ennreal_toReal.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
            (measureReal_le_one : (P x).real s ≤ 1)) : MemLp (fun x => (P x).real s) 1 ν).integrable (by norm_num)
    · exact (MemLp.of_bound (Q.measurable_coe hs).ennreal_toReal.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
            (measureReal_le_one : (Q x).real s ≤ 1)) : MemLp (fun x => (Q x).real s) 1 ν).integrable (by norm_num)
  have hlocal : ∀ᵐ x ∂μ, g x ^ 2 ≤ (klDiv (P x) (Q x)).toReal / 2 := by
    filter_upwards [hfinite] with x hx
    have hp := (abs_measureReal_sub_le_totalVariationDistance (P x) (Q x) s hs).trans
      (totalVariationDistance_le_sqrt_toReal_klDiv_div_two (P x) (Q x) hx)
    have hsquare := mul_self_le_mul_self (abs_nonneg (g x)) hp
    rw [← sq, ← sq, sq_abs, Real.sq_sqrt (by positivity)] at hsquare
    exact hsquare
  have hgD : (∫ x, g x ^ 2 ∂μ) ≤ D / 2 := by
    calc
      _ ≤ ∫ x, (klDiv (P x) (Q x)).toReal / 2 ∂μ :=
        integral_mono_ae hg.integrable_sq (hKL.div_const 2) hlocal
      _ = (∫ x, (klDiv (P x) (Q x)).toReal ∂μ) / 2 := integral_div 2 _
      _ ≤ D / 2 := div_le_div_of_nonneg_right hD (by norm_num)
  have hcs := integral_product_sq_le μ f g hf hg
  have hbound : (∫ x, f x * g x ∂μ) ^ 2 ≤ B / 2 * D := by
    calc
      _ ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := hcs
      _ ≤ B * (∫ x, g x ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_right hB (integral_nonneg fun x => sq_nonneg (g x))
      _ ≤ B * (D / 2) := mul_le_mul_of_nonneg_left hgD hB0
      _ = B / 2 * D := by ring
  rw [hevent]
  exact (Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hbound))

/-- Extended-KL version: a finite extended mean budget prevents either
`toReal ∞ = 0` or nonintegrable real integrals from weakening the hypothesis. -/
theorem totalVariationDistance_comp_le_sqrt_of_lintegral_kl
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P Q : Kernel X Y) [IsMarkovKernel P] [IsMarkovKernel Q]
    (hνμ : ν ≪ μ) (B D : ℝ) (hD0 : 0 ≤ D)
    (hRN : Integrable (fun x => ((ν.rnDeriv μ x).toReal) ^ 2) μ)
    (hB : (∫ x, ((ν.rnDeriv μ x).toReal) ^ 2 ∂μ) ≤ B)
    (hm : AEMeasurable (fun x => klDiv (P x) (Q x)) μ)
    (hD : (∫⁻ x, klDiv (P x) (Q x) ∂μ) ≤ ENNReal.ofReal D) :
    totalVariationDistance (P ∘ₘ ν) (Q ∘ₘ ν) ≤ Real.sqrt (B / 2 * D) := by
  have hfin : (∫⁻ x, klDiv (P x) (Q x) ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD
  have hae := ae_lt_top' hm hfin
  apply totalVariationDistance_comp_le_sqrt_of_mean_kl μ ν P Q hνμ B D hRN hB
  · exact hae.mono fun _ hx => hx.ne
  · exact integrable_toReal_of_lintegral_ne_top hm hfin
  · rw [integral_toReal hm hae]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hD).trans_eq (ENNReal.toReal_ofReal hD0)

/-- Discarding a conditional path cannot increase the transferred error.
For the manuscript apply this with the measurable terminal-state projection. -/
theorem totalVariationDistance_map_comp_le_sqrt_of_lintegral_kl
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P Q : Kernel X Y) [IsMarkovKernel P] [IsMarkovKernel Q]
    (endpoint : Y → Z) (hend : Measurable endpoint)
    (hνμ : ν ≪ μ) (B D : ℝ) (hD0 : 0 ≤ D)
    (hRN : Integrable (fun x => ((ν.rnDeriv μ x).toReal) ^ 2) μ)
    (hB : (∫ x, ((ν.rnDeriv μ x).toReal) ^ 2 ∂μ) ≤ B)
    (hm : AEMeasurable (fun x => klDiv (P x) (Q x)) μ)
    (hD : (∫⁻ x, klDiv (P x) (Q x) ∂μ) ≤ ENNReal.ofReal D) :
    totalVariationDistance ((P ∘ₘ ν).map endpoint) ((Q ∘ₘ ν).map endpoint) ≤
      Real.sqrt (B / 2 * D) :=
  (totalVariationDistance_map_le (P ∘ₘ ν) (Q ∘ₘ ν) endpoint hend).trans
    (totalVariationDistance_comp_le_sqrt_of_lintegral_kl μ ν P Q hνμ B D hD0 hRN hB hm hD)

end AcceleratedLogConcave.Probability
