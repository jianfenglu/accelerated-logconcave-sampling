import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Growth
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Identification

/-! The actual heat quotient, its gradient and generator belong to the moving
Gibbs spaces. Their Green identity is derived from the closed gradient. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson Analysis.WeightedGradient AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem continuous_gradient_of_C2 {q : E → ℝ} (hq : ContDiff ℝ 2 q) :
    Continuous (gradient q) := continuous_iff_continuousAt.mpr fun x =>
  (gradient_hasFDerivAt_hessian hq x).continuousAt

theorem compactHeatQuotient_memLp {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    MemLp (compactHeatQuotient F f t) 2 (F.law t) ∧
    MemLp (gradient (compactHeatQuotient F f t)) 2 (F.law t) ∧
    MemLp (weightedHeatGenerator (F.potential t) (compactHeatQuotient F f t)) 2 (F.law t) := by
  obtain ⟨C,hC,hbound⟩ := compactHeatQuotient_uniform_growth F hf hc hheat
  have hq := compactHeatQuotient_C2 F hf hc t ht
  have hg := continuous_gradient_of_C2 hq
  refine ⟨MemLp.of_bound hq.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => (hbound t ht x).1), ?_, ?_⟩
  · apply reference_memLp_of_quadratic_bound F t ht hg (2*C)
    intro x
    have hx : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
    have hh := (hbound t ht x).2.1
    nlinarith [mul_le_mul_of_nonneg_left hx hC, mul_nonneg hC (sq_nonneg ‖x‖)]
  · apply reference_memLp_of_quadratic_bound F t ht _ C
      (fun x => (hbound t ht x).2.2)
    exact (continuous_compactTestLaplacian hq).neg.add
      ((continuous_gradient_of_C2 (F.potential_C2 t)).inner hg)

/-- The source's integration by parts is valid for the actual smoothed density,
with all global integrability obligations discharged. -/
theorem compactHeatQuotient_green_energy {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    let h := compactHeatQuotient_memLp F hf hc hheat t ht
    ‖h.2.1.toLp (gradient (compactHeatQuotient F f t))‖^2 =
      inner ℝ (h.2.2.toLp (weightedHeatGenerator (F.potential t) (compactHeatQuotient F f t)))
        (h.1.toLp (compactHeatQuotient F f t)) := by
  exact weighted_green_energy (F.law t) (F.potential t) (compactHeatQuotient F f t)
    ((F.potential_C2 t).of_le (by norm_num)) (compactHeatQuotient_C2 F hf hc t ht)
    (F.integrable t ht) (F.gibbs_law t ht)
    (compactHeatQuotient_memLp F hf hc hheat t ht).1
    (compactHeatQuotient_memLp F hf hc hheat t ht).2.1
    (compactHeatQuotient_memLp F hf hc hheat t ht).2.2

end AcceleratedLogConcave.Kinetic.Reheating
