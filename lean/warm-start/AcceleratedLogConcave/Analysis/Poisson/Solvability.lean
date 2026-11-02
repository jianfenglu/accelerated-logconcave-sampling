import AcceleratedLogConcave.Analysis.Poisson.Centered
import AcceleratedLogConcave.Analysis.Poisson.CoerciveSolve

/-!
# The centered weighted Poisson equation

Existence and uniqueness use the actual closed gradient and the Poincare theorem
proved from C2 curvature bounds. No inverse, core, or coercivity certificate is
an input of the weighted theorem.
-/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) (V : E → ℝ)
  (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

include m L hm hlower hupper

/-- The unique centered weak solution for centered L2 forcing, tested on the
entire genuine weighted Sobolev domain. -/
theorem existsUnique_weak_poisson (f : Lp ℝ 2 μ) (hf : (∫ x, f x ∂μ) = 0) :
    ∃! u : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      (∫ x, (u : Lp ℝ 2 μ) x ∂μ) = 0 ∧
      ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
        inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)
          (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
        inner ℝ f (v : Lp ℝ 2 μ) := by
  let : IsProbabilityMeasure μ := hμ ▸ isProbabilityMeasure_tilted hI
  obtain ⟨u, hu, huniq⟩ := existsUnique_centered_solution
    (closedGradient μ V (hV.of_le (by norm_num)) hI hμ)
    (closedGradient_isClosed μ V (hV.of_le (by norm_num)) hI hμ)
    (mean μ) hm (fun u hu => Gibbs.closedGradient_poincare
      μ V hV hI hμ m L hm hlower hupper u ((mean_apply μ u).symm.trans hu)) f
  refine ⟨u, ⟨(mean_apply μ u).symm.trans hu.1, ?_⟩, ?_⟩
  · exact weak_equation_of_centered μ V (hV.of_le (by norm_num)) hI hμ f hf u
      (fun v hv => hu.2 v ((mean_apply μ v).trans hv))
  · intro w hw
    exact huniq w ⟨(mean_apply μ w).trans hw.1, fun v _ => hw.2 v⟩

/-- Energy and both inverse-gap estimates for the actual weak solution. -/
theorem weak_poisson_estimates (f : Lp ℝ 2 μ)
    (u : Sobolev μ V (hV.of_le (by norm_num)) hI hμ)
    (hu : (∫ x, (u : Lp ℝ 2 μ) x ∂μ) = 0)
    (hweak : ∀ v : Sobolev μ V (hV.of_le (by norm_num)) hI hμ,
      inner ℝ (closedGradient μ V (hV.of_le (by norm_num)) hI hμ u)
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ v) =
      inner ℝ f (v : Lp ℝ 2 μ)) :
    ‖closedGradient μ V (hV.of_le (by norm_num)) hI hμ u‖ ^ 2 =
        inner ℝ f (u : Lp ℝ 2 μ) ∧
      m * ‖(u : Lp ℝ 2 μ)‖ ≤ ‖f‖ ∧
      m * ‖closedGradient μ V (hV.of_le (by norm_num)) hI hμ u‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have he := hweak u
  rw [real_inner_self_eq_norm_sq] at he
  have hp := Gibbs.closedGradient_poincare μ V hV hI hμ m L hm hlower hupper u hu
  have hcs := real_inner_le_norm f (u : Lp ℝ 2 μ)
  have hn : m * ‖(u : Lp ℝ 2 μ)‖ ≤ ‖f‖ := by
    by_cases hz : ‖(u : Lp ℝ 2 μ)‖ = 0
    · simp [hz]
    · have hpos : 0 < ‖(u : Lp ℝ 2 μ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  refine ⟨he, hn, ?_⟩
  calc
    _ = m * inner ℝ f (u : Lp ℝ 2 μ) := by rw [he]
    _ ≤ m * (‖f‖ * ‖(u : Lp ℝ 2 μ)‖) := mul_le_mul_of_nonneg_left hcs hm.le
    _ ≤ ‖f‖ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg f)]

end AcceleratedLogConcave.Analysis.Poisson
