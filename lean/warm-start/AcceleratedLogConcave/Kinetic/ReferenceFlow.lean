import AcceleratedLogConcave.Kinetic.ReferenceFlow.Continuity
import AcceleratedLogConcave.Kinetic.ReferenceFlow.GaussianDensity
import AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonLocal
import AcceleratedLogConcave.Kinetic.GaussianEmbedding

/-!
# The actual coupled reference flow

Starting from the classical W04 Gibbs-density family, the drift is constructed
as `(ell*y-c(t)*gradient U, -ell*gradient U)`. Its complete invertible C1 flow
and transport of the true product Gaussian law are conclusions. The proof
combines the spatial density continuity equation with the derived Gibbs score
and Gaussian score; Hamiltonian cancellation is proved pointwise.

The source specializes `c(t)=a*t`. A genuinely local family enters through
`LocalReferencePoissonFamily.toFamily`; no flow or transport premise is added.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function
open scoped Topology NNReal ENNReal
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson OAI.LogConcaveSampling.GlobalODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual spatial Gibbs law times standard Gaussian momentum, represented
in the Hilbert product for the Euclidean continuity equation. -/
def coupledPhaseMeasure (μ : Measure E) : Measure (CoupledPhase E) :=
  (μ.prod (stdGaussian E)).map (WithLp.toLp 2)

instance coupledPhaseMeasure_probability (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (coupledPhaseMeasure μ) := by
  unfold coupledPhaseMeasure
  infer_instance

theorem coupledPhaseMeasure_density (μ : Measure E) (r : E → ℝ)
    (hr : Continuous r) (hpos : ∀ x, 0 ≤ r x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (r x))) :
    coupledPhaseMeasure μ = volume.withDensity (fun z =>
      ENNReal.ofReal (coupledDensity r standardGaussianDensity z)) := by
  rw [coupledPhaseMeasure, hμ, stdGaussian_eq_volume_density,
    prod_withDensity hr.measurable.ennreal_ofReal
      standardGaussianDensity_contDiff.continuous.measurable.ennreal_ofReal]
  rw [← Measure.volume_eq_prod]
  change (volume.withDensity (fun z : E × E => ENNReal.ofReal (r z.1) *
    ENNReal.ofReal (standardGaussianDensity z.2))).map (MeasurableEquiv.toLp 2 (E × E)) = _
  rw [map_withDensity_of_measurePreserving (MeasurableEquiv.toLp 2 (E × E)) volume volume
    (WithLp.volume_preserving_toLp E E)]
  congr 1
  funext z
  exact (ENNReal.ofReal_mul (hpos z.fst)).symm

variable {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell : ℝ)

/-- The trajectory in ordinary position--momentum coordinates. -/
def referenceCoupledTrajectory (z : E × E) : ℝ → E × E :=
  fun t => WithLp.ofLp (coupledFlow F.potential ell F.scale (fun s _ => F.potential_C2 s)
    F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
    F.hessian_nonneg F.hessian_upper F.leftTime (WithLp.toLp 2 z) t)

theorem referenceCoupledTrajectory_initial (z : E × E) : referenceCoupledTrajectory F ell z a = z :=
  congrArg WithLp.ofLp (coupledFlow_initial F.potential ell F.scale (fun s _ => F.potential_C2 s)
    F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
    F.hessian_nonneg F.hessian_upper F.leftTime (WithLp.toLp 2 z))

/-- Both coordinate equations of the manuscript's coupled ODE. -/
theorem referenceCoupledTrajectory_deriv (z : E × E) (t : ℝ) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (referenceCoupledTrajectory F ell z)
      (ell • (referenceCoupledTrajectory F ell z t).2 -
        F.scale t • gradient (F.potential t) (referenceCoupledTrajectory F ell z t).1,
       -ell • gradient (F.potential t) (referenceCoupledTrajectory F ell z t).1) (Icc a b) t :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t
    (coupledFlow_deriv F.potential ell F.scale (fun s _ => F.potential_C2 s)
      F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
      F.hessian_nonneg F.hessian_upper F.leftTime (WithLp.toLp 2 z) t ht)

/-- The actual coupled flow from the source left endpoint. -/
def referenceCoupledFlow (t : Icc a b) : CoupledPhase E ≃ₜ CoupledPhase E :=
  coupledFlowHomeomorph F.potential ell F.scale (fun s _ => F.potential_C2 s)
    F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
    F.hessian_nonneg F.hessian_upper F.leftTime t

/-- The same actual flow on ordinary position--momentum pairs. -/
def referenceCoupledPairFlow (t : Icc a b) : (E × E) ≃ₜ (E × E) :=
  coupledPairFlowHomeomorph F.potential ell F.scale (fun s _ => F.potential_C2 s)
    F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
    F.hessian_nonneg F.hessian_upper F.leftTime t

theorem referenceCoupledFlow_contDiff (t : Icc a b) : ContDiff ℝ 1 (referenceCoupledFlow F ell t) :=
  coupledFlowHomeomorph_contDiff F.potential ell F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime t

theorem referenceCoupledFlow_symm_contDiff (t : Icc a b) :
    ContDiff ℝ 1 (referenceCoupledFlow F ell t).symm :=
  coupledFlowHomeomorph_symm_contDiff F.potential ell F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime t

/-- Actual law transport follows from the derived product-density PDE. -/
theorem referenceCoupledFlow_measurePreserving (t : Icc a b) :
    MeasurePreserving (referenceCoupledFlow F ell t)
      (coupledPhaseMeasure (F.law a)) (coupledPhaseMeasure (F.law t)) := by
  let R := fun s z => coupledDensity (F.density s) standardGaussianDensity z
  let Rt := fun s (z : CoupledPhase E) => F.densityVelocity s z.fst * standardGaussianDensity z.snd
  have hfst : Continuous (fun z : CoupledPhase E => z.fst) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).continuous.fst
  have hsnd : Continuous (fun z : CoupledPhase E => z.snd) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).continuous.snd
  have hR : ContinuousOn (uncurry R) (Icc a b ×ˢ (univ : Set (CoupledPhase E))) :=
    (F.density_continuous.comp
      (continuous_fst.prodMk (hfst.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)).mul
    (standardGaussianDensity_contDiff.continuous.comp (hsnd.comp continuous_snd)).continuousOn
  have hRt : ContinuousOn (uncurry Rt) (Ioo a b ×ˢ (univ : Set (CoupledPhase E))) :=
    (F.densityVelocity_continuous.comp
      (continuous_fst.prodMk (hfst.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)).mul
    (standardGaussianDensity_contDiff.continuous.comp (hsnd.comp continuous_snd)).continuousOn
  exact measurePreserving_flow_family_of_density_continuity F.ordered
    (coupledDrift_continuous F.potential ell F.scale F.gradient_continuous F.scale_continuous)
    (fun s hs => coupledDrift_lipschitz F.potential ell F.scale s (F.potential_C2 s)
      (F.hessian_nonneg s hs) (F.hessian_upper s hs) F.scaleBound (F.scale_bounded s hs))
    (coupledDriftDerivative_continuous F.potential ell F.scale F.hessian_continuous F.scale_continuous)
    (fun s z => coupledDrift_hasFDerivAt F.potential ell F.scale s z (F.potential_C2 s))
    R Rt hR hRt
    (fun s hs z => (F.density_hasDerivAt s hs z.fst).mul_const (standardGaussianDensity z.snd))
    (fun s hs => ((F.density_C1 s hs).comp
      ((ContinuousLinearMap.fst ℝ E E).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap).contDiff).mul
      (standardGaussianDensity_contDiff.comp
        ((ContinuousLinearMap.snd ℝ E E).comp
          (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap).contDiff))
    (fun s hs z => coupledDensity_continuity_equation F ell standardGaussianDensity
      standardGaussianDensity_hasFDerivAt s hs z)
    (fun s => coupledPhaseMeasure (F.law s))
    (fun s hs => coupledPhaseMeasure_density (F.law s) (F.density s)
      (F.density_continuous.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨hs, mem_univ x⟩)) (F.density_nonneg s hs) (F.density_law s hs))
    (fun s hs z => mul_nonneg (F.density_nonneg s hs z.fst)
      (standardGaussianDensity_pos z.snd).le) t

/-- Transport in the actual ordinary pair coordinates used by the kernel. -/
theorem referenceCoupledPairFlow_measurePreserving (t : Icc a b) :
    MeasurePreserving (referenceCoupledPairFlow F ell t)
      ((F.law a).prod (stdGaussian E)) ((F.law t).prod (stdGaussian E)) := by
  have he (μ : Measure E) : MeasurePreserving (MeasurableEquiv.toLp 2 (E × E))
      (μ.prod (stdGaussian E)) (coupledPhaseMeasure μ) :=
    ⟨(MeasurableEquiv.toLp 2 (E × E)).measurable, rfl⟩
  exact ((he (F.law t)).symm).comp ((referenceCoupledFlow_measurePreserving F ell t).comp (he (F.law a)))

/-- The dormant coordinate remains fixed during the parent flow. -/
def referenceExtendedFlow (t : Icc a b) : GaussianPhase E ≃ₜ GaussianPhase E :=
  (referenceCoupledPairFlow F ell t).prodCongr (Homeomorph.refl E)

theorem referenceExtendedFlow_measurePreserving (t : Icc a b) :
    MeasurePreserving (referenceExtendedFlow F ell t)
      (gaussianPhaseMeasure (F.law a)) (gaussianPhaseMeasure (F.law t)) :=
  (referenceCoupledPairFlow_measurePreserving F ell t).prod (MeasurePreserving.id _)

/-- Deterministic reference transport is an actual L2 unitary on full phase space. -/
def referenceExtendedPullback (t : Icc a b) :
    Lp ℝ 2 (gaussianPhaseMeasure (F.law t)) ≃ₗᵢ[ℝ] Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) :=
  pullback (referenceExtendedFlow F ell t).toMeasurableEquiv
    (referenceExtendedFlow_measurePreserving F ell t)

/-- The unitary is actual composition with the deterministic parent flow. -/
theorem referenceExtendedPullback_coe (t : Icc a b)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law t))) :
    referenceExtendedPullback F ell t f =ᵐ[gaussianPhaseMeasure (F.law a)]
      fun z => f (referenceExtendedFlow F ell t z) :=
  pullback_coeFn _ _ f

/-- The reference density transport has exactly constant L2 norm. -/
theorem referenceExtendedPullback_norm (t : Icc a b)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law t))) :
    ‖referenceExtendedPullback F ell t f‖ = ‖f‖ :=
  (referenceExtendedPullback F ell t).norm_map f

/-- Centering is preserved by the actual reference transport. -/
theorem referenceExtendedPullback_integral (t : Icc a b)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law t))) :
    (∫ z, referenceExtendedPullback F ell t f z ∂gaussianPhaseMeasure (F.law a)) =
      ∫ z, f z ∂gaussianPhaseMeasure (F.law t) :=
  integral_pullback _ _ f

end AcceleratedLogConcave.Kinetic
