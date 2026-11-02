import AcceleratedLogConcave.Analysis.WeightedGradient.Basic
import AcceleratedLogConcave.External.Samplinglib.TechnicalLemmas.FunctionalInequalities.GibbsC1Poincare

/-!
# Strong log-concavity implies Poincare on the actual weighted gradient domain

The law is identified with its normalized density. The potential is C2 with
positive lower and finite upper Hessian bounds. No Poincare, resolvent, graph
core, or coercivity premise is supplied by the caller. The closed-domain result
is primary; the C1 variance result is a useful classical corollary.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace AcceleratedLogConcave.Gibbs
open Analysis.WeightedGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Poincare on the genuine closure of the compact smooth gradient graph.
The mean is the mean of the L2 equivalence class, not of a chosen smooth test. -/
theorem closedGradient_poincare (μ : Measure E) (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)
    (u : Sobolev μ V (hV.of_le (by norm_num)) hI hμ)
    (hu : (∫ x, (u : Lp ℝ 2 μ) x ∂μ) = 0) :
    m * ‖(u : Lp ℝ 2 μ)‖ ^ 2 ≤
      ‖closedGradient μ V (hV.of_le (by norm_num)) hI hμ u‖ ^ 2 := by
  subst μ
  exact AutoSamplingTheory.TechnicalLemmas.FunctionalInequalities.CenteredDomainPoincare.gibbs_centered_domain_poincare
    V hV hI (integral_exp_pos hI) m (max m L) hm (le_max_left _ _) hlower
    (fun x a => (hupper x a).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)))
    (compactGradient _ V (hV.of_le (by norm_num)) hI rfl)
    (compactGradient_closable _ V (hV.of_le (by norm_num)) hI rfl)
    (mem_compactGradient_graph _ V (hV.of_le (by norm_num)) hI rfl) u hu

/-- C1 test functions with square-integrable value and gradient satisfy the
variance form of Poincare. Their membership in the genuine closed domain is
proved by cutoff and smoothing, not postulated. -/
theorem c1_variance_poincare (μ : Measure E) (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x))
    (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hp : MemLp f 2 μ) (hq : MemLp (gradient f) 2 μ) :
    m * (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) ≤
      ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
  subst μ
  exact (AutoSamplingTheory.TechnicalLemmas.FunctionalInequalities.GibbsC1Poincare.gibbs_c1_variance_poincare
    V hV hI (integral_exp_pos hI) m (max m L) hm (le_max_left _ _) hlower
    (fun x a => (hupper x a).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))) f hf hp hq).2

end AcceleratedLogConcave.Gibbs
