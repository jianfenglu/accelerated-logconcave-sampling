import AcceleratedLogConcave.Kinetic.ReferenceFlow
import AcceleratedLogConcave.Kinetic.MomentumSplit
import AcceleratedLogConcave.Kinetic.ConditionalContraction.DormantKernel
import AcceleratedLogConcave.Kinetic.Reheating.HeatChannel
import AcceleratedLogConcave.Kinetic.Reheating.OUGaussian

/-! Actual random-tape geometry of a fixed-clock phase step. The conditional
dormant collision is an arbitrary Markov kernel with Gaussian invariant fibers.
All marginal identities below follow from the prescribed maps and reference laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Mix the retained hidden coordinate with one fresh independent Gaussian. -/
def hiddenNoiseMix (n s : ℝ) (z : GaussianPhase E × E) : GaussianPhase E :=
  (z.1.1, n • z.1.2 + s • z.2)

theorem hiddenNoiseMix_measurePreserving (μ : Measure E) [IsProbabilityMeasure μ]
    (n s : ℝ) (hns : n^2+s^2=1) :
    MeasurePreserving (hiddenNoiseMix (E := E) n s)
      ((gaussianPhaseMeasure μ).prod (stdGaussian E)) (gaussianPhaseMeasure μ) := by
  have hm := (measurePreserving_fst (μ := stdGaussian E) (ν := stdGaussian E)).comp
    (gaussianSplit_measurePreserving (E := E) n s hns)
  exact ((MeasurePreserving.id (μ.prod (stdGaussian E))).prod hm).comp
    (measurePreserving_prodAssoc (μ.prod (stdGaussian E)) (stdGaussian E) (stdGaussian E))

/-- The manuscript's correlated reheating map, retaining momentum. -/
def correlatedHeatObservation (τ n s : ℝ) (z : GaussianPhase E × E) : E × E :=
  (z.1.1.1 + Real.sqrt τ • (n • z.1.2 + s • z.2), z.1.1.2)

theorem correlatedHeatObservation_measurePreserving (μ : Measure E) [IsProbabilityMeasure μ]
    (τ n s : ℝ) (hns : n^2+s^2=1) :
    MeasurePreserving (correlatedHeatObservation (E := E) τ n s)
      ((gaussianPhaseMeasure μ).prod (stdGaussian E))
      ((heatedLaw μ τ).prod (stdGaussian E)) :=
  (heatObservation_measurePreserving μ τ).comp (hiddenNoiseMix_measurePreserving μ n s hns)

variable {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell : ℝ)
  (t : Icc a b) (s n : ℝ) (hsn : s^2+n^2=1)

/-- Initial split followed by the actual coupled flow, before the collision. -/
def preCollisionMap : GaussianPhase E ≃ₜ GaussianPhase E :=
  (phaseSplit (E := E) s n hsn).trans (referenceExtendedFlow F ell t)

theorem preCollisionMap_measurePreserving :
    MeasurePreserving (preCollisionMap F ell t s n hsn)
      (gaussianPhaseMeasure (F.law a)) (gaussianPhaseMeasure (F.law t)) :=
  (referenceExtendedFlow_measurePreserving F ell t).comp
    (phaseSplit_measurePreserving (F.law a) s n hsn)

variable (κ : Kernel (GaussianPhase E) E) [IsMarkovKernel κ]

/-- The fixed-clock tape contains the old and new dormant coordinates, followed
by independent reheating and momentum-refresh Gaussians. -/
def fixedClockTape : Measure (((GaussianPhase E × E) × E) × E) :=
  ((dormantJoint ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ).prod
    (stdGaussian E)).prod (stdGaussian E)

instance fixedClockTape_probability : IsProbabilityMeasure (fixedClockTape F t κ) := by
  unfold fixedClockTape
  infer_instance

/-- Recover the visible input from the pre-collision state on the tape. -/
def fixedClockInput (z : ((GaussianPhase E × E) × E) × E) : E × E :=
  ((preCollisionMap F ell t s n hsn).symm z.1.1.1).1

theorem fixedClockInput_measurePreserving :
    MeasurePreserving (fixedClockInput F ell t s n hsn)
      (fixedClockTape F t κ) ((F.law a).prod (stdGaussian E)) := by
  have hbase := (dormantOld_preserving ((F.law t).prod (stdGaussian E))
    (stdGaussian E) κ).comp
    ((measurePreserving_fst (μ := dormantJoint ((F.law t).prod (stdGaussian E))
      (stdGaussian E) κ) (ν := stdGaussian E)).comp
      (measurePreserving_fst (μ := (dormantJoint ((F.law t).prod (stdGaussian E))
        (stdGaussian E) κ).prod (stdGaussian E)) (ν := stdGaussian E)))
  have hback := (preCollisionMap_measurePreserving F ell t s n hsn).symm
    (preCollisionMap F ell t s n hsn).toMeasurableEquiv
  exact measurePreserving_fst.comp (hback.comp hbase)

/-- Perform the dormant replacement, final rotation, correlated reheat and OU. -/
def fixedClockOutput (τ Γ : ℝ) (z : ((GaussianPhase E × E) × E) × E) : E × E :=
  let newPhase := phaseRotate (E := E) s n hsn (dormantNewState z.1.1)
  let reheated := correlatedHeatObservation τ n s (newPhase, z.1.2)
  (reheated.1, gaussianMix E Γ (reheated.2, z.2))

theorem fixedClockOutput_measurePreserving
    (hκ : ConditionallyInvariant (stdGaussian E) κ) (τ Γ : ℝ) (hΓ : 0 ≤ Γ) :
    MeasurePreserving (fixedClockOutput s n hsn τ Γ)
      (fixedClockTape F t κ) ((heatedLaw (F.law t) τ).prod (stdGaussian E)) := by
  have hpost := (phaseRotate_measurePreserving (F.law t) s n hsn).comp
    (dormantNew_preserving ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ hκ)
  have hheat := (correlatedHeatObservation_measurePreserving (F.law t) τ n s
    (by nlinarith [hsn])).comp (hpost.prod (MeasurePreserving.id (stdGaussian E)))
  have hou := ((MeasurePreserving.id (heatedLaw (F.law t) τ)).prod
    (gaussianMix_measurePreserving E Γ hΓ)).comp
    (measurePreserving_prodAssoc (heatedLaw (F.law t) τ) (stdGaussian E) (stdGaussian E))
  exact hou.comp (hheat.prod (MeasurePreserving.id (stdGaussian E)))

/-- The actual fixed-clock test operator, defined from its physical joint law. -/
def fixedClockChannel (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ) :
    Lp ℝ 2 ((heatedLaw (F.law t) τ).prod (stdGaussian E)) →L[ℝ]
      Lp ℝ 2 ((F.law a).prod (stdGaussian E)) :=
  referenceChannel (fixedClockInput_measurePreserving F ell t s n hsn κ)
    (fixedClockOutput_measurePreserving F t s n hsn κ hκ τ Γ hΓ)

theorem fixedClockChannel_norm_le (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ) :
    ‖fixedClockChannel F ell t s n hsn κ hκ τ Γ hΓ‖ ≤ 1 :=
  referenceChannel_norm_le _ _

/-- The physical density step is the actual L2 adjoint of the test step. -/
def fixedClockDensity (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ) :
    Lp ℝ 2 ((F.law a).prod (stdGaussian E)) →L[ℝ]
      Lp ℝ 2 ((heatedLaw (F.law t) τ).prod (stdGaussian E)) :=
  (fixedClockChannel F ell t s n hsn κ hκ τ Γ hΓ).adjoint

/-- Exact input/output pairing on the prescribed physical tape. -/
theorem fixedClockDensity_pairing (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ)
    (f : Lp ℝ 2 ((F.law a).prod (stdGaussian E)))
    (g : Lp ℝ 2 ((heatedLaw (F.law t) τ).prod (stdGaussian E))) :
    inner ℝ (fixedClockDensity F ell t s n hsn κ hκ τ Γ hΓ f) g =
      ∫ z, f (fixedClockInput F ell t s n hsn z) *
        g (fixedClockOutput s n hsn τ Γ z) ∂fixedClockTape F t κ := by
  rw [fixedClockDensity, ContinuousLinearMap.adjoint_inner_left]
  exact referenceChannel_pairing _ _ f g

/-- The heat convolution identity closes the reference law after the step.
This is a marginal identity, not a mixing or dissipation assumption. -/
def returningClockChannel (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ) (hreturn : heatedLaw (F.law t) τ = F.law a) :
    Lp ℝ 2 ((F.law a).prod (stdGaussian E)) →L[ℝ]
      Lp ℝ 2 ((F.law a).prod (stdGaussian E)) :=
  referenceChannel (fixedClockInput_measurePreserving F ell t s n hsn κ)
    (by rw [← hreturn]; exact fixedClockOutput_measurePreserving F t s n hsn κ hκ τ Γ hΓ)

theorem returningClockChannel_norm_le (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ) (hreturn : heatedLaw (F.law t) τ = F.law a) :
    ‖returningClockChannel F ell t s n hsn κ hκ τ Γ hΓ hreturn‖ ≤ 1 :=
  referenceChannel_norm_le _ _

theorem returningClockChannel_mean (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ) (hreturn : heatedLaw (F.law t) τ = F.law a)
    (f : Lp ℝ 2 ((F.law a).prod (stdGaussian E))) :
    mean ((F.law a).prod (stdGaussian E))
      (returningClockChannel F ell t s n hsn κ hκ τ Γ hΓ hreturn f) =
      mean ((F.law a).prod (stdGaussian E)) f := referenceChannel_mean _ _ f

theorem returningClockChannel_one (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ) (hreturn : heatedLaw (F.law t) τ = F.law a) :
    returningClockChannel F ell t s n hsn κ hκ τ Γ hΓ hreturn
      (oneL2 ((F.law a).prod (stdGaussian E))) =
      oneL2 ((F.law a).prod (stdGaussian E)) := referenceChannel_one _ _

theorem returningClockChannel_adjoint_mean (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ) (hreturn : heatedLaw (F.law t) τ = F.law a)
    (f : Lp ℝ 2 ((F.law a).prod (stdGaussian E))) :
    mean ((F.law a).prod (stdGaussian E))
      ((returningClockChannel F ell t s n hsn κ hκ τ Γ hΓ hreturn).adjoint f) =
      mean ((F.law a).prod (stdGaussian E)) f := referenceChannel_adjoint_mean _ _ f

end AcceleratedLogConcave.Kinetic
