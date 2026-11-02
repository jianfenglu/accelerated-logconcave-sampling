import AcceleratedLogConcave.Kinetic.Reheating.HeatPhaseGradient
import AcceleratedLogConcave.Kinetic.Corrector

/-! The visible corrector is the actual compression of the W04 phase corrector.
The two Gaussian heat-residual estimates use its genuine Poisson gradient and
weak Hessian rows, rather than smoothness or heat estimates supplied as premises. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace ContDiff
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson Analysis.WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (ν : Measure E) [IsProbabilityMeasure ν]

/-- The actual momentum adjoint ignores the independently adjoined hidden coordinate. -/
theorem gaussianMomentumAdjoint_hiddenEmbedding (f : Lp ℝ 2 (ν.prod (stdGaussian E))) :
    gaussianMomentumAdjoint ν (Kinetic.hiddenEmbedding ν f) =
      (momentumEmbedding ν).toContinuousLinearMap.adjoint f := by
  apply ext_inner_left ℝ
  intro G
  rw [gaussianMomentumAdjoint, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (Kinetic.hiddenEmbedding ν (momentumEmbedding ν G))
    (Kinetic.hiddenEmbedding ν f) = _
  exact (Kinetic.hiddenEmbedding ν).inner_map_map _ _

omit [BorelSpace E] [IsProbabilityMeasure ν] in
/-- Fully averaging a visible embedding is actual momentum averaging. -/
theorem gaussianAverage_hiddenEmbedding (f : Lp ℝ 2 (ν.prod (stdGaussian E))) :
    gaussianAverage ν (Kinetic.hiddenEmbedding ν f) = productAverage ν (stdGaussian E) f := by
  apply ext_inner_left ℝ
  intro g
  rw [gaussianAverage, productAverage, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (Kinetic.hiddenEmbedding ν (productEmbedding ν (stdGaussian E) g))
    (Kinetic.hiddenEmbedding ν f) = _
  exact (Kinetic.hiddenEmbedding ν).inner_map_map _ _

variable (V : E → ℝ) (hV : ContDiff ℝ 2 V)
  (hI : Integrable (fun x => Real.exp (-V x)))
  (hν : ν = volume.tilted (fun x => -V x))
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m*‖a‖^2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L*‖a‖^2)

/-- The actual corrector acting on visible position-momentum densities. -/
def visibleCorrector : Lp ℝ 2 (ν.prod (stdGaussian E)) →L[ℝ] Lp ℝ 2 (ν.prod (stdGaussian E)) :=
  (productEmbedding ν (stdGaussian E)).toContinuousLinearMap.comp
    ((vectorPoissonInverse ν V hV hI hν m L hm hlower hupper).comp
      (momentumEmbedding ν).toContinuousLinearMap.adjoint)

theorem hiddenEmbedding_visibleCorrector (f : Lp ℝ 2 (ν.prod (stdGaussian E))) :
    Kinetic.hiddenEmbedding ν (visibleCorrector ν V hV hI hν m L hm hlower hupper f) =
      gaussianCorrector ν V hV hI hν m L hm hlower hupper (Kinetic.hiddenEmbedding ν f) := by
  rw [gaussianCorrector_apply, gaussianMomentumAdjoint_hiddenEmbedding]
  rfl

/-- This visible operator is precisely the isometric compression of W04. -/
theorem visibleCorrector_eq_compression :
    visibleCorrector ν V hV hI hν m L hm hlower hupper =
      (Kinetic.hiddenEmbedding ν).toContinuousLinearMap.adjoint.comp
        ((gaussianCorrector ν V hV hI hν m L hm hlower hupper).comp
          (Kinetic.hiddenEmbedding ν).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro f
  change _ = (Kinetic.hiddenEmbedding ν).toContinuousLinearMap.adjoint
    (gaussianCorrector ν V hV hI hν m L hm hlower hupper (Kinetic.hiddenEmbedding ν f))
  rw [← hiddenEmbedding_visibleCorrector]
  exact (congrArg (fun T => T (visibleCorrector ν V hV hI hν m L hm hlower hupper f))
    (Kinetic.hiddenEmbedding ν).adjoint_comp_self).symm

/-- Its adjoint uses the same actual gradient Poisson inverse. -/
theorem visibleCorrector_adjoint :
    (visibleCorrector ν V hV hI hν m L hm hlower hupper).adjoint =
      (momentumEmbedding ν).toContinuousLinearMap.comp
        ((gradientPoissonInverse ν V hV hI hν m L hm hlower hupper).comp
          (productAverage ν (stdGaussian E))) := by
  unfold visibleCorrector productAverage
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, vectorPoissonInverse_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

theorem hiddenEmbedding_visibleCorrector_adjoint (f : Lp ℝ 2 (ν.prod (stdGaussian E))) :
    Kinetic.hiddenEmbedding ν ((visibleCorrector ν V hV hI hν m L hm hlower hupper).adjoint f) =
      (gaussianCorrector ν V hV hI hν m L hm hlower hupper).adjoint (Kinetic.hiddenEmbedding ν f) := by
  rw [visibleCorrector_adjoint, gaussianCorrector_adjoint]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    gaussianAverage_hiddenEmbedding]
  rfl

/-- The visible quadratic corrector is exactly the W04 quadratic corrector. -/
theorem visibleCorrector_inner (f : Lp ℝ 2 (ν.prod (stdGaussian E))) :
    inner ℝ (visibleCorrector ν V hV hI hν m L hm hlower hupper f) f =
      inner ℝ (gaussianCorrector ν V hV hI hν m L hm hlower hupper
        (Kinetic.hiddenEmbedding ν f)) (Kinetic.hiddenEmbedding ν f) := by
  rw [← hiddenEmbedding_visibleCorrector]
  exact ((Kinetic.hiddenEmbedding ν).inner_map_map _ _).symm

section HeatBounds
variable (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (ht : 0 ≤ t)
  (hheat : heatedLaw μ t = volume.tilted (fun x => -V x))
include ht

/-- The actual corrector's heat residual is controlled by its genuine closed gradient. -/
theorem phaseHeatCentered_visibleCorrector_bound
    (f : Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E))) :
    ‖phaseHeatCenteredPullback μ t
      (visibleCorrector (heatedLaw μ t) V hV hI hheat m L hm hlower hupper f)‖^2 ≤ t*‖f‖^2 := by
  let F := Kinetic.hiddenEmbedding (heatedLaw μ t) f
  have hg := gaussianCorrectorPositionGradient_graph (heatedLaw μ t) V hV hI hheat
    m L hm hlower hupper F
  obtain ⟨u, hu, hDu⟩ := (LinearPMap.mem_graph_iff _).mp hg
  have hu' : productEmbedding (heatedLaw μ t) (stdGaussian E) (u : Lp ℝ 2 (heatedLaw μ t)) =
      visibleCorrector (heatedLaw μ t) V hV hI hheat m L hm hlower hupper f := by
    rw [hu]
    change productEmbedding (heatedLaw μ t) (stdGaussian E)
      (vectorPoissonInverse (heatedLaw μ t) V hV hI hheat m L hm hlower hupper
        (gaussianMomentumAdjoint (heatedLaw μ t) (Kinetic.hiddenEmbedding (heatedLaw μ t) f))) = _
    rw [gaussianMomentumAdjoint_hiddenEmbedding]
    rfl
  have hb := phaseHeatCentered_position_closedGradient μ t ht V (hV.of_le (by norm_num)) hI hheat u
  rw [hu'] at hb
  have hn : ‖closedGradient (heatedLaw μ t) V (hV.of_le (by norm_num)) hI hheat u‖ ≤ ‖f‖ := by
    rw [hDu]
    have hh := ContinuousLinearMap.le_of_opNorm_le _
      (gaussianCorrectorPositionGradient_norm_le (heatedLaw μ t) V hV hI hheat m L hm hlower hupper) F
    simpa only [one_mul, F, (Kinetic.hiddenEmbedding (heatedLaw μ t)).norm_map] using hh
  exact hb.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn) ht)

/-- The actual adjoint-corrector residual uses the proved weak Bochner rows. -/
theorem phaseHeatCentered_visibleCorrector_adjoint_bound
    (f : Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E))) :
    ‖phaseHeatCenteredPullback μ t
      ((visibleCorrector (heatedLaw μ t) V hV hI hheat m L hm hlower hupper).adjoint f)‖^2 ≤ t*‖f‖^2 := by
  obtain ⟨R,hR,hbound⟩ := gaussianCorrectorAdjoint_spatial_rows (heatedLaw μ t) V hV hI hheat
    m L hm hlower hupper (Kinetic.hiddenEmbedding (heatedLaw μ t) f)
  simp only [gaussianAverage_hiddenEmbedding] at hR
  have hb := phaseHeatCentered_momentum_rows μ t ht V (hV.of_le (by norm_num)) hI hheat
    (gradientPoissonInverse (heatedLaw μ t) V hV hI hheat m L hm hlower hupper
      (productAverage (heatedLaw μ t) (stdGaussian E) f)) R hR
  rw [visibleCorrector_adjoint]
  change ‖phaseHeatCenteredPullback μ t (momentumEmbedding (heatedLaw μ t) _)‖^2 ≤ _
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ ht
  simpa only [(Kinetic.hiddenEmbedding (heatedLaw μ t)).norm_map] using hbound

theorem phaseHeatCentered_visibleCorrector_norm
    (f : Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E))) :
    ‖phaseHeatCenteredPullback μ t
      (visibleCorrector (heatedLaw μ t) V hV hI hheat m L hm hlower hupper f)‖ ≤ Real.sqrt t*‖f‖ := by
  have hb := phaseHeatCentered_visibleCorrector_bound V hV hI m L hm hlower hupper μ t ht hheat f
  have hs := Real.sq_sqrt ht
  have hn := mul_nonneg (Real.sqrt_nonneg t) (norm_nonneg f)
  nlinarith [sq_nonneg (‖phaseHeatCenteredPullback μ t
    (visibleCorrector (heatedLaw μ t) V hV hI hheat m L hm hlower hupper f)‖ - Real.sqrt t*‖f‖)]

theorem phaseHeatCentered_visibleCorrector_adjoint_norm
    (f : Lp ℝ 2 ((heatedLaw μ t).prod (stdGaussian E))) :
    ‖phaseHeatCenteredPullback μ t
      ((visibleCorrector (heatedLaw μ t) V hV hI hheat m L hm hlower hupper).adjoint f)‖ ≤ Real.sqrt t*‖f‖ := by
  have hb := phaseHeatCentered_visibleCorrector_adjoint_bound V hV hI m L hm hlower hupper μ t ht hheat f
  have hs := Real.sq_sqrt ht
  have hn := mul_nonneg (Real.sqrt_nonneg t) (norm_nonneg f)
  nlinarith [sq_nonneg (‖phaseHeatCenteredPullback μ t
    ((visibleCorrector (heatedLaw μ t) V hV hI hheat m L hm hlower hupper).adjoint f)‖ - Real.sqrt t*‖f‖)]
end HeatBounds

end AcceleratedLogConcave.Kinetic.Reheating

