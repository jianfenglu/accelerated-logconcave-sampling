import AcceleratedLogConcave.Kinetic.Corrector
import AcceleratedLogConcave.Kinetic.MovingCorrector
import AcceleratedLogConcave.Analysis.Poisson.Pullback

/-!
# Unitary phase pullback and Gaussian corrector transport

Only the position coordinate is transported. The Gaussian momentum and
auxiliary coordinates are unchanged, so both Gaussian embeddings intertwine
with ordinary scalar and vector spatial composition.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace ContDiff
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson

section Abstract
variable {H₁ H₂ V₁ V₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]

private theorem unitary_adjoint_intertwine
    (P : H₁ ≃ₗᵢ[ℝ] H₂) (Q : V₁ ≃ₗᵢ[ℝ] V₂)
    (J₁ : V₁ →L[ℝ] H₁) (J₂ : V₂ →L[ℝ] H₂)
    (h : ∀ v, P (J₁ v) = J₂ (Q v)) (f : H₁) :
    J₂.adjoint (P f) = Q (J₁.adjoint f) := by
  apply ext_inner_left ℝ
  intro v
  calc
    inner ℝ v (J₂.adjoint (P f)) = inner ℝ (J₂ v) (P f) := J₂.adjoint_inner_right _ _
    _ = inner ℝ (P (J₁ (Q.symm v))) (P f) := by rw [h, Q.apply_symm_apply]
    _ = inner ℝ (J₁ (Q.symm v)) f := P.inner_map_map _ _
    _ = inner ℝ (Q.symm v) (J₁.adjoint f) := (J₁.adjoint_inner_right _ _).symm
    _ = inner ℝ v (Q (J₁.adjoint f)) := by
      rw [← Q.inner_map_map, Q.apply_symm_apply]
end Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Lift a spatial equivalence while leaving both Gaussian coordinates fixed. -/
def gaussianPhaseEquiv (e : E ≃ᵐ E) : GaussianPhase E ≃ᵐ GaussianPhase E :=
  (e.prodCongr (MeasurableEquiv.refl E)).prodCongr (MeasurableEquiv.refl E)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[simp] theorem gaussianPhaseEquiv_apply (e : E ≃ᵐ E) (z : GaussianPhase E) :
    gaussianPhaseEquiv e z = ((e z.1.1, z.1.2), z.2) := rfl

omit [BorelSpace E] [IsProbabilityMeasure ν] in
theorem gaussianPhaseEquiv_measurePreserving (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν) :
    MeasurePreserving (gaussianPhaseEquiv e) (gaussianPhaseMeasure μ) (gaussianPhaseMeasure ν) :=
  (he.prod (MeasurePreserving.id (stdGaussian E))).prod (MeasurePreserving.id (stdGaussian E))

/-- Actual unitary phase composition along the spatial transport. -/
def gaussianPhasePullback (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν) :
    Lp ℝ 2 (gaussianPhaseMeasure ν) ≃ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  pullback (gaussianPhaseEquiv e) (gaussianPhaseEquiv_measurePreserving e he)

omit [BorelSpace E] [IsProbabilityMeasure ν] in
theorem gaussianPhasePullback_coe (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (f : Lp ℝ 2 (gaussianPhaseMeasure ν)) :
    gaussianPhasePullback e he f =ᵐ[gaussianPhaseMeasure μ]
      fun z => f ((e z.1.1, z.1.2), z.2) :=
  pullback_coeFn _ _ _

omit [BorelSpace E] [IsProbabilityMeasure ν] in
/-- Position embedding commutes with actual phase and scalar spatial pullbacks. -/
theorem gaussianPhasePullback_positionEmbedding (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (f : Lp ℝ 2 ν) :
    gaussianPhasePullback e he (positionEmbedding ν f) = positionEmbedding μ (pullback e he f) := by
  apply Lp.ext
  filter_upwards [gaussianPhasePullback_coe e he (positionEmbedding ν f),
    (gaussianPhaseEquiv_measurePreserving e he).quasiMeasurePreserving.ae
      (positionEmbedding_coe ν f), positionEmbedding_coe μ (pullback e he f),
    measurePreserving_fst.quasiMeasurePreserving.ae
      (measurePreserving_fst.quasiMeasurePreserving.ae (pullback_coeFn e he f))]
    with z hp hi hj hf
  exact hp.trans (hi.trans (hf.symm.trans hj.symm))

/-- The momentum chaos intertwines with ordinary vector composition, with no
Jacobian multiplying the vector field. -/
theorem gaussianPhasePullback_momentumEmbedding (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (G : Lp E 2 ν) :
    gaussianPhasePullback e he (gaussianMomentumEmbedding ν G) =
      gaussianMomentumEmbedding μ (pullback e he G) := by
  apply Lp.ext
  filter_upwards [gaussianPhasePullback_coe e he (gaussianMomentumEmbedding ν G),
    (gaussianPhaseEquiv_measurePreserving e he).quasiMeasurePreserving.ae
      (gaussianMomentumEmbedding_coe ν G), gaussianMomentumEmbedding_coe μ (pullback e he G),
    measurePreserving_fst.quasiMeasurePreserving.ae
      (measurePreserving_fst.quasiMeasurePreserving.ae (pullback_coeFn e he G))]
    with z hp hi hj hG
  change (pullback e he G) z.1.1 = G (e z.1.1) at hG
  change (gaussianMomentumEmbedding ν G) ((e z.1.1, z.1.2), z.2) =
    inner ℝ (G (e z.1.1)) z.1.2 at hi
  rw [hp, hi, hj, hG]

omit [BorelSpace E] [IsProbabilityMeasure ν] in
/-- Gaussian averaging intertwines as the adjoint of the position embedding. -/
theorem gaussianAverage_phasePullback (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (f : Lp ℝ 2 (gaussianPhaseMeasure ν)) :
    gaussianAverage μ (gaussianPhasePullback e he f) = pullback e he (gaussianAverage ν f) :=
  unitary_adjoint_intertwine (gaussianPhasePullback e he) (pullback (F := ℝ) e he)
    (positionEmbedding ν).toContinuousLinearMap (positionEmbedding μ).toContinuousLinearMap
    (gaussianPhasePullback_positionEmbedding e he) f

/-- The Gaussian momentum coefficient intertwines as the adjoint of its chaos embedding. -/
theorem gaussianMomentumAdjoint_phasePullback (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (f : Lp ℝ 2 (gaussianPhaseMeasure ν)) :
    gaussianMomentumAdjoint μ (gaussianPhasePullback e he f) =
      pullback e he (gaussianMomentumAdjoint ν f) :=
  unitary_adjoint_intertwine (gaussianPhasePullback e he) (pullback (F := E) e he)
    (gaussianMomentumEmbedding ν).toContinuousLinearMap
    (gaussianMomentumEmbedding μ).toContinuousLinearMap
    (gaussianPhasePullback_momentumEmbedding e he) f

omit [BorelSpace E] [IsProbabilityMeasure ν] in
theorem gaussianPositionProjection_phasePullback (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (f : Lp ℝ 2 (gaussianPhaseMeasure ν)) :
    gaussianPositionProjection μ (gaussianPhasePullback e he f) =
      gaussianPhasePullback e he (gaussianPositionProjection ν f) := by
  change positionEmbedding μ (gaussianAverage μ (gaussianPhasePullback e he f)) = _
  rw [gaussianAverage_phasePullback, ← gaussianPhasePullback_positionEmbedding]
  rfl


/-- The gradient inverse transported by ordinary vector and scalar composition. -/
def spatialGradientConjugate (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (G : Lp ℝ 2 ν →L[ℝ] Lp E 2 ν) : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ :=
  (pullback (F := E) e he : Lp E 2 ν →L[ℝ] Lp E 2 μ).comp
    (G.comp ((pullback (F := ℝ) e he).symm : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν))

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem spatialGradientConjugate_apply (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (G : Lp ℝ 2 ν →L[ℝ] Lp E 2 ν) (u : Lp ℝ 2 μ) :
    spatialGradientConjugate e he G u = pullback e he (G ((pullback e he).symm u)) := rfl

omit [BorelSpace E] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem spatialGradientConjugate_adjoint_apply (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (G : Lp ℝ 2 ν →L[ℝ] Lp E 2 ν) (v : Lp E 2 ν) :
    (spatialGradientConjugate e he G).adjoint (pullback e he v) = pullback e he (G.adjoint v) := by
  apply unitary_adjoint_intertwine (pullback (F := E) e he) (pullback (F := ℝ) e he) G
    (spatialGradientConjugate e he G) _ v
  intro u
  simp only [spatialGradientConjugate_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The corrector built from the transported gradient inverse is exactly the
phase conjugate of the target corrector. -/
theorem referenceCorrector_phasePullback (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (G : Lp ℝ 2 ν →L[ℝ] Lp E 2 ν) (f : Lp ℝ 2 (gaussianPhaseMeasure ν)) :
    referenceCorrector μ (spatialGradientConjugate e he G) (gaussianPhasePullback e he f) =
      gaussianPhasePullback e he (referenceCorrector ν G f) := by
  change positionEmbedding μ ((spatialGradientConjugate e he G).adjoint
    (gaussianMomentumAdjoint μ (gaussianPhasePullback e he f))) =
      gaussianPhasePullback e he (positionEmbedding ν (G.adjoint (gaussianMomentumAdjoint ν f)))
  rw [gaussianMomentumAdjoint_phasePullback, spatialGradientConjugate_adjoint_apply,
    gaussianPhasePullback_positionEmbedding]

theorem referenceCorrector_phase_conjugacy (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (G : Lp ℝ 2 ν →L[ℝ] Lp E 2 ν) :
    (gaussianPhasePullback e he : Lp ℝ 2 (gaussianPhaseMeasure ν) →L[ℝ]
      Lp ℝ 2 (gaussianPhaseMeasure μ)).comp
      ((referenceCorrector ν G).comp ((gaussianPhasePullback e he).symm :
        Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ] Lp ℝ 2 (gaussianPhaseMeasure ν))) =
      referenceCorrector μ (spatialGradientConjugate e he G) := by
  apply ContinuousLinearMap.ext
  intro f
  change gaussianPhasePullback e he (referenceCorrector ν G ((gaussianPhasePullback e he).symm f)) = _
  rw [← referenceCorrector_phasePullback, LinearIsometryEquiv.apply_symm_apply]

/-- The concrete weighted Poisson corrector is the Gaussian lift of its genuine
gradient inverse, so the preceding conjugacy applies without an abstract identification premise. -/
theorem gaussianCorrector_eq_referenceCorrector (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hν : ν = volume.tilted (fun x => -V x)) (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2) :
    gaussianCorrector ν V hV hI hν m L hm hlower hupper =
      referenceCorrector ν (gradientPoissonInverse ν V hV hI hν m L hm hlower hupper) := by
  unfold gaussianCorrector referenceCorrector
  rw [gradientPoissonInverse_adjoint]

/-- Exact phase conjugacy for the actual weighted Poisson corrector. -/
theorem gaussianCorrector_phase_conjugacy (e : E ≃ᵐ E) (he : MeasurePreserving e μ ν)
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hν : ν = volume.tilted (fun x => -V x)) (m L : ℝ) (hm : 0 < m)
    (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
    (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2) :
    (gaussianPhasePullback e he : Lp ℝ 2 (gaussianPhaseMeasure ν) →L[ℝ]
      Lp ℝ 2 (gaussianPhaseMeasure μ)).comp
      ((gaussianCorrector ν V hV hI hν m L hm hlower hupper).comp
        ((gaussianPhasePullback e he).symm : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ]
          Lp ℝ 2 (gaussianPhaseMeasure ν))) =
      referenceCorrector μ (spatialGradientConjugate e he
        (gradientPoissonInverse ν V hV hI hν m L hm hlower hupper)) := by
  rw [gaussianCorrector_eq_referenceCorrector]
  exact referenceCorrector_phase_conjugacy e he _

end AcceleratedLogConcave.Kinetic
