import AcceleratedLogConcave.Gibbs.Poincare
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Centering the actual weighted Sobolev domain

The mean is a continuous functional on weighted L2. Constants belong to the
actual closed gradient domain, so subtracting the mean preserves that domain
and its gradient. These facts allow a centered variational solution to be tested
against every member of the original domain.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson

section Mean
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The constant unit vector in scalar L2. -/
def oneL2 : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ => 1)

/-- Integration as a bounded linear functional on scalar L2. -/
def mean : Lp ℝ 2 μ →L[ℝ] ℝ := innerSL ℝ (oneL2 μ)

@[simp] theorem mean_apply (u : Lp ℝ 2 μ) : mean μ u = ∫ x, u x ∂μ := by
  change inner ℝ (oneL2 μ) u = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x hx
  change inner ℝ ((oneL2 μ) x) (u x) = u x
  rw [show (oneL2 μ) x = 1 from hx]
  simp

@[simp] theorem mean_oneL2 : mean μ (oneL2 μ) = 1 := by
  rw [mean_apply]
  calc
    _ = ∫ _, (1 : ℝ) ∂μ := integral_congr_ae (memLp_const (1 : ℝ)).coeFn_toLp
    _ = 1 := by simp

/-- The closed subspace of mean-zero scalar functions. -/
def centered : Submodule ℝ (Lp ℝ 2 μ) := (mean μ).ker

@[simp] theorem mem_centered (u : Lp ℝ 2 μ) :
    u ∈ centered μ ↔ (∫ x, u x ∂μ) = 0 := by
  change mean μ u = 0 ↔ _
  rw [mean_apply]

theorem centered_isClosed : IsClosed (centered μ : Set (Lp ℝ 2 μ)) :=
  (mean μ).isClosed_ker

end Mean

section Weighted
open WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) (V : E → ℝ)
  (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))

/-- Subtracting the actual integral preserves the closed gradient. -/
theorem exists_centered_subtract (v : Sobolev μ V hV hI hμ) :
    ∃ w : Sobolev μ V hV hI hμ,
      (∫ x, (w : Lp ℝ 2 μ) x ∂μ) = 0 ∧
      closedGradient μ V hV hI hμ w = closedGradient μ V hV hI hμ v ∧
      ∃ z : Sobolev μ V hV hI hμ,
        (z : Lp ℝ 2 μ) =ᵐ[μ] (fun _ => ∫ x, (v : Lp ℝ 2 μ) x ∂μ) ∧
        w = v - z := by
  let : IsProbabilityMeasure μ := hμ ▸ isProbabilityMeasure_tilted hI
  obtain ⟨z, hz, hDz⟩ := constants_mem_closedGradient μ V hV hI hμ
    (∫ x, (v : Lp ℝ 2 μ) x ∂μ)
  refine ⟨v - z, ?_, ?_, z, hz, rfl⟩
  · have he : mean μ (z : Lp ℝ 2 μ) = mean μ (v : Lp ℝ 2 μ) := by
      rw [mean_apply, mean_apply, integral_congr_ae hz]
      simp
    change (∫ x, ((v : Lp ℝ 2 μ) - (z : Lp ℝ 2 μ)) x ∂μ) = 0
    rw [← mean_apply, map_sub, he, sub_self]
  · rw [LinearPMap.map_sub, hDz, sub_zero]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A centered forcing pairs to zero with each constant domain element. -/
theorem inner_constant_eq_zero (f : Lp ℝ 2 μ)
    (hf : (∫ x, f x ∂μ) = 0) (z : Lp ℝ 2 μ) (c : ℝ)
    (hz : z =ᵐ[μ] (fun _ => c)) : inner ℝ f z = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, f x * c ∂μ := integral_congr_ae (by
      filter_upwards [hz] with x hx
      simp [hx, mul_comm])
    _ = 0 := by rw [integral_mul_const, hf, zero_mul]

/-- The centered variational equation implies the full-domain weak equation. -/
theorem weak_equation_of_centered (f : Lp ℝ 2 μ)
    (hf : (∫ x, f x ∂μ) = 0) (u : Sobolev μ V hV hI hμ)
    (hu : ∀ v : Sobolev μ V hV hI hμ,
      (∫ x, (v : Lp ℝ 2 μ) x ∂μ) = 0 →
      inner ℝ (closedGradient μ V hV hI hμ u) (closedGradient μ V hV hI hμ v) =
        inner ℝ f (v : Lp ℝ 2 μ)) :
    ∀ v : Sobolev μ V hV hI hμ,
      inner ℝ (closedGradient μ V hV hI hμ u) (closedGradient μ V hV hI hμ v) =
        inner ℝ f (v : Lp ℝ 2 μ) := by
  intro v
  obtain ⟨w, hw, hDw, z, hz, hwz⟩ := exists_centered_subtract μ V hV hI hμ v
  have he := hu w hw
  rw [hDw, hwz] at he
  change inner ℝ _ _ = inner ℝ f ((v : Lp ℝ 2 μ) - (z : Lp ℝ 2 μ)) at he
  rw [inner_sub_right, inner_constant_eq_zero μ f hf z _ hz, sub_zero] at he
  exact he

end Weighted
end AcceleratedLogConcave.Analysis.Poisson
