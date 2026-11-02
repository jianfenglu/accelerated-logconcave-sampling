import AcceleratedLogConcave.Probability.TotalVariation
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pinsker's inequality and finite relative entropy

The Csiszár–Kemperman proof gives the exact constant `2 TV² ≤ KL`.
Mathlib provides extended KL, data processing, and the joint-measure chain rule.
Every conversion to real KL retains an explicit finiteness hypothesis.
-/

open MeasureTheory Real InformationTheory Set ProbabilityTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Probability

/-- Auxiliary function whose sign controls the monotonicity of the Pinsker comparison. -/
private noncomputable def pk (x : ℝ) : ℝ := (x + 1) * log x - 2 * (x - 1)

private theorem hasDerivAt_pk {x : ℝ} (hx : 0 < x) :
    HasDerivAt pk (log x + x⁻¹ - 1) x := by
  have h1 : HasDerivAt (fun x : ℝ => (x + 1) * log x) (1 * log x + (x + 1) * x⁻¹) x :=
    ((hasDerivAt_id x).add_const 1).mul (Real.hasDerivAt_log hx.ne')
  have h2 : HasDerivAt (fun x : ℝ => 2 * (x - 1)) (2 * 1) x :=
    ((hasDerivAt_id x).sub_const 1).const_mul 2
  have h3 : HasDerivAt (fun x : ℝ => (x + 1) * log x - 2 * (x - 1))
      (1 * log x + (x + 1) * x⁻¹ - 2 * 1) x := h1.sub h2
  refine h3.congr_deriv ?_
  field_simp
  ring

private theorem pk_monotoneOn : MonotoneOn pk (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun x hx => (hasDerivAt_pk hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_pk hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_pk hx).deriv]
    have := Real.one_sub_inv_le_log_of_pos hx
    linarith

private theorem pk_one : pk 1 = 0 := by simp [pk]

/-- Auxiliary: `h x = (4 + 2x) klFun x - 3 (x-1)^2`. -/
private noncomputable def ph (x : ℝ) : ℝ := (4 + 2 * x) * klFun x - 3 * (x - 1) ^ 2

private theorem hasDerivAt_ph {x : ℝ} (hx : 0 < x) : HasDerivAt ph (4 * pk x) x := by
  have hk : HasDerivAt klFun (log x) x := hasDerivAt_klFun hx.ne'
  have h1 : HasDerivAt (fun x : ℝ => 4 + 2 * x) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).const_add 4
  have h2 : HasDerivAt (fun x : ℝ => 3 * (x - 1) ^ 2) (3 * (2 * (x - 1))) x := by
    have := (((hasDerivAt_id x).sub_const 1).pow 2).const_mul 3
    simpa using this
  have h3 := (h1.mul hk).sub h2
  refine h3.congr_deriv ?_
  simp only [pk, klFun]
  ring

private theorem ph_one : ph 1 = 0 := by simp [ph, klFun]

/-- Pointwise bound behind the Csiszár–Kemperman proof of Pinsker's inequality. -/
theorem three_mul_sq_sub_one_le (x : ℝ) (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 ≤ (4 + 2 * x) * klFun x := by
  suffices h : 0 ≤ ph x by simpa [ph] using h
  rcases le_total 1 x with h1 | h1
  · have hmono : MonotoneOn ph (Ici 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
      · exact fun y hy => (hasDerivAt_ph (lt_of_lt_of_le one_pos hy)).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        exact (hasDerivAt_ph (lt_trans one_pos hy)).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hy0 : 0 < y := lt_trans one_pos hy
        rw [(hasDerivAt_ph hy0).deriv]
        have := pk_monotoneOn (mem_Ioi.mpr one_pos) (mem_Ioi.mpr hy0) hy.le
        rw [pk_one] at this
        linarith
    have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr h1) h1
    rwa [ph_one] at this
  · have hanti : AntitoneOn ph (Icc 0 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      · have hc : Continuous ph := by
          unfold ph; have := continuous_klFun; fun_prop
        exact hc.continuousOn
      · intro y hy
        rw [interior_Icc] at hy
        exact (hasDerivAt_ph hy.1).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hasDerivAt_ph hy.1).deriv]
        have := pk_monotoneOn (mem_Ioi.mpr hy.1) (mem_Ioi.mpr one_pos) hy.2.le
        rw [pk_one] at this
        linarith
    have := hanti (mem_Icc.mpr ⟨hx, h1⟩) (mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) h1
    rwa [ph_one] at this


section Pinsker

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem abs_le_aux (u K t A : ℝ) (hA : 0 < A) (ht : 0 < t) (hK : 3 * u ^ 2 ≤ A * K) :
    |u| ≤ t * A / 6 + K / (2 * t) := by
  have hm : 0 < t * A / 3 := by positivity
  have h1 : u ^ 2 / (t * A / 3) ≤ K / t := by
    rw [div_le_div_iff₀ hm ht]
    have : 3 * u ^ 2 * t ≤ A * K * t := mul_le_mul_of_nonneg_right hK ht.le
    nlinarith
  have h2 : 2 * |u| ≤ t * A / 3 + u ^ 2 / (t * A / 3) := by
    rw [← sub_nonneg]
    have : t * A / 3 + u ^ 2 / (t * A / 3) - 2 * |u| = (t * A / 3 - |u|) ^ 2 / (t * A / 3) := by
      field_simp
      linear_combination (-9) * sq_abs u
    rw [this]
    positivity
  have h3 : K / (2 * t) = (K / t) / 2 := by field_simp
  rw [h3]
  linarith

/-- The `L¹` form of Pinsker's inequality for the likelihood ratio. -/
private theorem integral_abs_rnDeriv_sub_one_le (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hKL : klDiv P Q ≠ ∞) :
    (∫ x, |(P.rnDeriv Q x).toReal - 1| ∂Q) ^ 2 ≤ 2 * (klDiv P Q).toReal := by
  obtain ⟨hPQ, hi⟩ := klDiv_ne_top_iff.mp hKL
  set f : Ω → ℝ := fun x => (P.rnDeriv Q x).toReal with hf
  have hfi : Integrable f Q := Measure.integrable_toReal_rnDeriv
  have hkl : Integrable (fun x => klFun (f x)) Q := (integrable_klFun_rnDeriv_iff hPQ).mpr hi
  have hfint : ∫ x, f x ∂Q = 1 := by
    have := Measure.setIntegral_toReal_rnDeriv (μ := P) (ν := Q) hPQ Set.univ
    simpa using this
  have hK : (klDiv P Q).toReal = ∫ x, klFun (f x) ∂Q := toReal_klDiv_eq_integral_klFun hPQ
  set I : ℝ := ∫ x, |f x - 1| ∂Q with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  set K : ℝ := (klDiv P Q).toReal with hKdef
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hbound : ∀ t : ℝ, 0 < t → I ≤ t + K / (2 * t) := by
    intro t ht
    have h0 : Integrable (fun x => 4 + 2 * f x) Q :=
      (integrable_const (4 : ℝ)).add (hfi.const_mul 2)
    have h1 : Integrable (fun x => t * (4 + 2 * f x) / 6) Q := (h0.const_mul t).div_const 6
    have hint : Integrable (fun x => t * (4 + 2 * f x) / 6 + klFun (f x) / (2 * t)) Q :=
      h1.add (hkl.div_const _)
    have hle : I ≤ ∫ x, (t * (4 + 2 * f x) / 6 + klFun (f x) / (2 * t)) ∂Q := by
      apply integral_mono (hfi.sub (integrable_const 1)).abs hint
      intro x
      have hx : 0 ≤ f x := ENNReal.toReal_nonneg
      apply abs_le_aux (f x - 1) (klFun (f x)) t (4 + 2 * f x) (by linarith) ht
      have := three_mul_sq_sub_one_le (f x) hx
      linarith
    have hval : ∫ x, (t * (4 + 2 * f x) / 6 + klFun (f x) / (2 * t)) ∂Q = t + K / (2 * t) := by
      rw [integral_add h1 (hkl.div_const _), integral_div (6 : ℝ), integral_const_mul,
        integral_add (integrable_const _) (hfi.const_mul 2), integral_const_mul, hfint,
        integral_div (2 * t), ← hK]
      simp
      ring
    linarith
  by_cases hK0' : K = 0
  · have : I ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have := hbound ε hε
      simpa [hK0'] using this
    have : I = 0 := le_antisymm this hI0
    simp [this, hK0']
  · have hKpos : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hK0')
    set t : ℝ := Real.sqrt (K / 2) with ht
    have htpos : 0 < t := Real.sqrt_pos.mpr (by positivity)
    have hts : t ^ 2 = K / 2 := Real.sq_sqrt (by positivity)
    have h1 := hbound t htpos
    have h2 : t + K / (2 * t) = 2 * t := by
      field_simp
      nlinarith [hts]
    rw [h2] at h1
    nlinarith [hts, hI0]

/-- **Pinsker's inequality**, exact constant: `2 TV² ≤ KL` (real form, finite entropy). -/
theorem two_mul_totalVariationDistance_sq_le_toReal_klDiv (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hKL : klDiv P Q ≠ ∞) :
    2 * totalVariationDistance P Q ^ 2 ≤ (klDiv P Q).toReal := by
  obtain ⟨hPQ, _⟩ := klDiv_ne_top_iff.mp hKL
  have hdens := totalVariationDistance_eq_integral_abs P Q Q hPQ Measure.AbsolutelyContinuous.rfl
  have hone : ∀ᵐ x ∂Q, (Q.rnDeriv Q x).toReal = 1 := by
    filter_upwards [Measure.rnDeriv_self Q] with x hx
    simp [hx]
  have : ∫ x, |(P.rnDeriv Q x).toReal - (Q.rnDeriv Q x).toReal| ∂Q
      = ∫ x, |(P.rnDeriv Q x).toReal - 1| ∂Q := by
    apply integral_congr_ae
    filter_upwards [hone] with x hx
    rw [hx]
  rw [hdens, this]
  have := integral_abs_rnDeriv_sub_one_le P Q hKL
  nlinarith

/-- **Pinsker's inequality** in extended-valued form: no finiteness hypothesis. -/
theorem ofReal_two_mul_totalVariationDistance_sq_le_klDiv (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ENNReal.ofReal (2 * totalVariationDistance P Q ^ 2) ≤ klDiv P Q := by
  by_cases hKL : klDiv P Q = ∞
  · simp [hKL]
  · rw [← ENNReal.ofReal_toReal hKL]
    exact ENNReal.ofReal_le_ofReal (two_mul_totalVariationDistance_sq_le_toReal_klDiv P Q hKL)

/-- Pinsker's inequality in the form `TV ≤ √(KL/2)`. -/
theorem totalVariationDistance_le_sqrt_toReal_klDiv_div_two (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hKL : klDiv P Q ≠ ∞) :
    totalVariationDistance P Q ≤ Real.sqrt ((klDiv P Q).toReal / 2) := by
  apply Real.le_sqrt_of_sq_le
  have := two_mul_totalVariationDistance_sq_le_toReal_klDiv P Q hKL
  linarith

end Pinsker

section Interface

/-! ### Data processing, chain rule and finiteness

These wrap Mathlib's `klDiv_map_le` and `klDiv_compProd_eq_add`, and record the finiteness
facts needed before passing to real-valued algebra. Every real-valued statement carries the
finiteness hypothesis explicitly, because `ENNReal.toReal ⊤ = 0`. -/

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Data processing inequality in real form, for finite entropy. -/
theorem toReal_klDiv_map_le (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {g : Ω → Ω'} (hg : Measurable g) (hKL : klDiv P Q ≠ ∞) :
    (klDiv (P.map g) (Q.map g)).toReal ≤ (klDiv P Q).toReal :=
  ENNReal.toReal_mono hKL (klDiv_map_le P Q hg)

/-- Entropy of a pushforward is finite whenever the entropy upstream is. -/
theorem klDiv_map_ne_top (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {g : Ω → Ω'} (hg : Measurable g) (hKL : klDiv P Q ≠ ∞) :
    klDiv (P.map g) (Q.map g) ≠ ∞ :=
  ne_top_of_le_ne_top hKL (klDiv_map_le P Q hg)

/-- Total variation of pushforwards is controlled by the entropy upstream:
data processing followed by Pinsker. -/
theorem totalVariationDistance_map_le_sqrt_toReal_klDiv_div_two
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {g : Ω → Ω'} (hg : Measurable g) (hKL : klDiv P Q ≠ ∞) :
    totalVariationDistance (P.map g) (Q.map g) ≤ Real.sqrt ((klDiv P Q).toReal / 2) := by
  refine (totalVariationDistance_le_sqrt_toReal_klDiv_div_two _ _ (klDiv_map_ne_top P Q hg hKL)).trans ?_
  apply Real.sqrt_le_sqrt
  have := toReal_klDiv_map_le P Q hg hKL
  linarith

variable {μ ν : Measure Ω} {κ η : Kernel Ω Ω'}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]

/-- Chain rule: the joint entropy is finite iff the marginal entropy and the entropy of the
kernels averaged against `μ` are both finite. -/
theorem klDiv_compProd_ne_top_iff :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞ ↔
      klDiv μ ν ≠ ∞ ∧ klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞ := by
  rw [klDiv_compProd_eq_add μ ν κ η, ENNReal.add_ne_top]

/-- Chain rule in real form. Finiteness of the joint entropy is the only hypothesis. -/
theorem toReal_klDiv_compProd_eq_add (h : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞) :
    (klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η)).toReal =
      (klDiv μ ν).toReal + (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal := by
  obtain ⟨h1, h2⟩ := klDiv_compProd_ne_top_iff.mp h
  rw [klDiv_compProd_eq_add μ ν κ η, ENNReal.toReal_add h1 h2]

/-- Chain rule for a product reference law `ν ⊗ γ`, the form used for `σ ⊗ γ_d`. -/
theorem klDiv_compProd_prod_reference (γ : Measure Ω') [IsProbabilityMeasure γ] :
    klDiv (μ ⊗ₘ κ) (ν.prod γ) =
      klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ.prod γ) := by
  have := klDiv_compProd_eq_add μ ν κ (Kernel.const Ω γ)
  rwa [Measure.compProd_const, Measure.compProd_const] at this

/-- Data processing along the first marginal: a joint entropy dominates the marginal one. -/
theorem klDiv_fst_le (P Q : Measure (Ω × Ω')) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    klDiv P.fst Q.fst ≤ klDiv P Q := by
  simpa [Measure.fst] using klDiv_map_le P Q measurable_fst

end Interface

end AcceleratedLogConcave.Probability
