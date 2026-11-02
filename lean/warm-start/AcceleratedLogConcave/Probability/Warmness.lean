import AcceleratedLogConcave.Probability.TotalVariation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Squared L2 warmness

`L2Warm μ ν B` means that the input law `ν` has squared L2 density at most `B`
relative to the reference law `μ`. Absolute continuity and integrability are
part of the predicate, so a singular law cannot acquire finite warmness through
the real-valued integral convention.

-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Probability

variable {X : Type*} [MeasurableSpace X]

/-- Squared L2 warmness, with the reference measure before the input measure. -/
def L2Warm (μ ν : Measure X) (B : ℝ) : Prop :=
  ν ≪ μ ∧ Integrable (fun x => ((ν.rnDeriv μ x).toReal) ^ 2) μ ∧
    (∫ x, ((ν.rnDeriv μ x).toReal) ^ 2 ∂μ) ≤ B

theorem L2Warm.absolutelyContinuous {μ ν : Measure X} {B : ℝ} (h : L2Warm μ ν B) :
    ν ≪ μ := h.1

theorem L2Warm.integrable_sq {μ ν : Measure X} {B : ℝ} (h : L2Warm μ ν B) :
    Integrable (fun x => ((ν.rnDeriv μ x).toReal) ^ 2) μ := h.2.1

theorem L2Warm.integral_sq_le {μ ν : Measure X} {B : ℝ} (h : L2Warm μ ν B) :
    (∫ x, ((ν.rnDeriv μ x).toReal) ^ 2 ∂μ) ≤ B := h.2.2

theorem L2Warm.mono {μ ν : Measure X} {B C : ℝ} (h : L2Warm μ ν B) (hBC : B ≤ C) :
    L2Warm μ ν C := ⟨h.1, h.2.1, h.2.2.trans hBC⟩

/-- The centered RN density has square integral equal to the RN square moment minus one. -/
theorem integral_centered_rnDeriv_sq (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hνμ : ν ≪ μ) (hRN : Integrable (fun x => ((ν.rnDeriv μ x).toReal) ^ 2) μ) :
    (∫ x, ((ν.rnDeriv μ x).toReal - 1) ^ 2 ∂μ) =
      (∫ x, ((ν.rnDeriv μ x).toReal) ^ 2 ∂μ) - 1 := by
  let f := fun x => (ν.rnDeriv μ x).toReal
  have hf : Integrable f μ := Measure.integrable_toReal_rnDeriv
  have hmass : (∫ x, f x ∂μ) = 1 := by
    simpa using Measure.integral_toReal_rnDeriv hνμ
  have he : (fun x => (f x - 1) ^ 2) = fun x => f x ^ 2 - 2 * f x + 1 := by
    funext x
    ring
  change (∫ x, (f x - 1) ^ 2 ∂μ) = (∫ x, f x ^ 2 ∂μ) - 1
  change Integrable (fun x => f x ^ 2) μ at hRN
  have hsub : Integrable (fun x => f x ^ 2 - 2 * f x) μ := hRN.sub (hf.const_mul 2)
  have hadd : (∫ x, f x ^ 2 - 2 * f x + 1 ∂μ) =
      (∫ x, f x ^ 2 - 2 * f x ∂μ) + (∫ _ : X, (1 : ℝ) ∂μ) :=
    integral_add hsub (integrable_const 1)
  rw [he, hadd, integral_sub hRN (hf.const_mul 2), integral_const_mul, hmass]
  simp
  ring

theorem L2Warm.one_le {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (h : L2Warm μ ν B) : 1 ≤ B := by
  have hc : 0 ≤ ∫ x, ((ν.rnDeriv μ x).toReal - 1) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg ((ν.rnDeriv μ x).toReal - 1))
  rw [integral_centered_rnDeriv_sq μ ν h.1 h.2.1] at hc
  linarith [h.2.2]

theorem L2Warm.memLp {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (h : L2Warm μ ν B) : MemLp (fun x => (ν.rnDeriv μ x).toReal) 2 μ :=
  (memLp_two_iff_integrable_sq
    (Measure.measurable_rnDeriv ν μ).ennreal_toReal.aestronglyMeasurable).mpr h.2.1

theorem L2Warm.memLp_centered {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ} (h : L2Warm μ ν B) :
    MemLp (fun x => (ν.rnDeriv μ x).toReal - 1) 2 μ :=
  h.memLp.sub (memLp_const 1)

theorem L2Warm.integrable_centered_sq {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ} (h : L2Warm μ ν B) :
    Integrable (fun x => ((ν.rnDeriv μ x).toReal - 1) ^ 2) μ :=
  h.memLp_centered.integrable_sq

theorem L2Warm.integral_centered_sq_le {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ} (h : L2Warm μ ν B) :
    (∫ x, ((ν.rnDeriv μ x).toReal - 1) ^ 2 ∂μ) ≤ B - 1 := by
  rw [integral_centered_rnDeriv_sq μ ν h.1 h.2.1]
  exact sub_le_sub_right h.2.2 1

/-- The centered density as an actual element of Mathlib's L2 space. -/
theorem L2Warm.norm_toLp_centered_sq {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ} (h : L2Warm μ ν B) :
    ‖h.memLp_centered.toLp (fun x => (ν.rnDeriv μ x).toReal - 1)‖ ^ 2 =
      (∫ x, ((ν.rnDeriv μ x).toReal) ^ 2 ∂μ) - 1 := by
  calc
    _ = ∫ x, ((ν.rnDeriv μ x).toReal - 1) ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [h.memLp_centered.coeFn_toLp] with x hx
      simp [hx, pow_two]
    _ = _ := integral_centered_rnDeriv_sq μ ν h.1 h.2.1

theorem L2Warm.norm_toLp_centered_le {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ} (h : L2Warm μ ν B) :
    ‖h.memLp_centered.toLp (fun x => (ν.rnDeriv μ x).toReal - 1)‖ ≤
      Real.sqrt (B - 1) := by
  apply Real.le_sqrt_of_sq_le
  rw [h.norm_toLp_centered_sq]
  exact sub_le_sub_right h.2.2 1

private theorem integral_sq_le_integral_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : MemLp f 2 μ) : (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have inner_integral (u v : X → ℝ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
      inner ℝ (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
    simp [hx, hy, RCLike.inner_apply, mul_comm]
  have h := real_inner_mul_inner_self_le (hf.toLp f) ((memLp_const (1 : ℝ)).toLp _)
  simpa only [inner_integral f (fun _ => 1) hf (memLp_const 1),
    inner_integral f f hf hf,
    inner_integral (fun _ => 1) (fun _ => 1) (memLp_const 1) (memLp_const 1),
    mul_one, one_mul, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, smul_eq_mul, pow_two] using h

/-- Probability-event TV is controlled by half the centered density's actual L2 norm. -/
theorem L2Warm.totalVariationDistance_le_half_norm_centered {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ} (h : L2Warm μ ν B) :
    totalVariationDistance ν μ ≤
      ‖h.memLp_centered.toLp (fun x => (ν.rnDeriv μ x).toReal - 1)‖ / 2 := by
  let f := fun x => (ν.rnDeriv μ x).toReal
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq
    (Measure.measurable_rnDeriv ν μ).ennreal_toReal.aestronglyMeasurable).mpr h.2.1
  have hc : MemLp (fun x => |f x - 1|) 2 μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hf.sub (memLp_const 1)).norm
  have hcs := integral_sq_le_integral_sq μ (fun x => |f x - 1|) hc
  simp only [sq_abs] at hcs
  have hbound : (∫ x, |f x - 1| ∂μ) ^ 2 ≤
      ‖h.memLp_centered.toLp (fun x => (ν.rnDeriv μ x).toReal - 1)‖ ^ 2 := by
    rw [h.norm_toLp_centered_sq]
    exact hcs.trans_eq (integral_centered_rnDeriv_sq μ ν h.1 h.2.1)
  have hL1 := (sq_le_sq₀ (integral_nonneg fun x => abs_nonneg (f x - 1))
    (norm_nonneg _)).mp hbound
  have hTV : totalVariationDistance ν μ = (∫ x, |f x - 1| ∂μ) / 2 := by
    rw [totalVariationDistance_eq_integral_abs ν μ μ h.1 Measure.AbsolutelyContinuous.rfl]
    congr 1
    apply integral_congr_ae
    filter_upwards [μ.rnDeriv_self] with x hx
    simp only [hx, ENNReal.toReal_one, f]
  rw [hTV]
  exact div_le_div_of_nonneg_right hL1 (by norm_num)

/-- The probability-event normalization gives the factor one half. -/
theorem L2Warm.totalVariationDistance_le {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ} (h : L2Warm μ ν B) :
    totalVariationDistance ν μ ≤ Real.sqrt (B - 1) / 2 :=
  h.totalVariationDistance_le_half_norm_centered.trans
    (div_le_div_of_nonneg_right h.norm_toLp_centered_le (by norm_num))

@[simp]
theorem l2Warm_self (μ : Measure X) [IsProbabilityMeasure μ] : L2Warm μ μ 1 := by
  have he : (fun x => ((μ.rnDeriv μ x).toReal) ^ 2) =ᵐ[μ] fun _ => (1 : ℝ) := by
    filter_upwards [μ.rnDeriv_self] with x hx
    simp [hx]
  refine ⟨Measure.AbsolutelyContinuous.rfl, (integrable_const 1).congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  simp

end AcceleratedLogConcave.Probability
