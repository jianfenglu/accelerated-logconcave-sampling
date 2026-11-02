import AcceleratedLogConcave.Kinetic.Mixing.DiscretePhase
import AcceleratedLogConcave.Kinetic.ConditionalContraction.MomentumReheatingLoss

/-! Exact stage factorization of the prescribed fixed-clock physical tape. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating ConditionalContraction
set_option backward.isDefEq.respectTransparency false

section IndependentNoise
variable {X Y Z W Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace W] [MeasurableSpace Ω]
  {μ : Measure X} {ν : Measure Y} {γ : Measure Z} {ξ : Measure W} {η : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
  [IsProbabilityMeasure ξ] [IsProbabilityMeasure η]
  {p : Ω → X} {q : Ω → Y} {r : Y×Z → W}

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ] in
/-- Adjoining a genuinely independent innovation composes the actual channels. -/
theorem referenceChannel_independent_noise (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η ν) (hr : MeasurePreserving r (ν.prod γ) ξ) :
    referenceChannel (hp.comp (measurePreserving_fst (ν := γ)))
      (hr.comp (hq.prod (MeasurePreserving.id γ))) =
      (referenceChannel hp hq).comp (referenceChannel (measurePreserving_fst (ν := γ)) hr) := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℝ
  intro f
  rw [ContinuousLinearMap.comp_apply, referenceChannel_pairing, referenceChannel_pairing]
  have hi := ((Lp.memLp f).comp_measurePreserving (hp.comp (measurePreserving_fst (ν := γ)))).integrable_mul
    ((Lp.memLp g).comp_measurePreserving (hr.comp (hq.prod (MeasurePreserving.id γ))))
  change Integrable (fun z : Ω×Z => f (p z.1) * g (r (q z.1,z.2))) (η.prod γ) at hi
  change (∫ z : Ω×Z, f (p z.1) * g (r (q z.1,z.2)) ∂η.prod γ) = _
  rw [integral_prod _ hi]
  apply integral_congr_ae
  have hc := hq.quasiMeasurePreserving.ae (referenceChannel_fst_coe ν γ hr g)
  filter_upwards [hc] with z hz
  rw [hz, integral_const_mul]
end IndependentNoise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell : ℝ)
  (t : Icc a b) (s n : ℝ) (hsn : s^2+n^2=1)

/-- Actual density transport through the initial split and coupled full flow. -/
def preCollisionDensity : Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) →ₗᵢ[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure (F.law t)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (preCollisionMap F ell t s n hsn).symm
    ((preCollisionMap_measurePreserving F ell t s n hsn).symm
      (preCollisionMap F ell t s n hsn).toMeasurableEquiv)

/-- The transported density is literal composition with the inverse split-flow map. -/
theorem preCollisionDensity_coe (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    preCollisionDensity F ell t s n hsn f =ᵐ[gaussianPhaseMeasure (F.law t)]
      fun z => f ((preCollisionMap F ell t s n hsn).symm z) :=
  Lp.coeFn_compMeasurePreserving f _

/-- The initial split and the actual coupled-flow density transports are separate stages. -/
theorem preCollisionDensity_split_flow (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    preCollisionDensity F ell t s n hsn f =
      (referenceExtendedPullback F ell t).symm
        (Lp.compMeasurePreservingₗᵢ ℝ (phaseSplit s n hsn).symm
          ((phaseSplit_measurePreserving (F.law a) s n hsn).symm
            (phaseSplit (E := E) s n hsn).toMeasurableEquiv) f) := by
  exact Lp.compMeasurePreserving_comp_apply f
    ((phaseSplit_measurePreserving (F.law a) s n hsn).symm
      (phaseSplit (E := E) s n hsn).toMeasurableEquiv)
    ((referenceExtendedFlow_measurePreserving F ell t).symm
      (referenceExtendedFlow F ell t).toMeasurableEquiv)

variable (κ : Kernel (GaussianPhase E) E) [IsMarkovKernel κ]

/-- Visible input read from the dormant-collision tape before fresh noises. -/
def collisionTapeInput (z : GaussianPhase E × E) : E×E :=
  ((preCollisionMap F ell t s n hsn).symm z.1).1

theorem collisionTapeInput_preserving : MeasurePreserving (collisionTapeInput F ell t s n hsn)
    (dormantJoint ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ)
    ((F.law a).prod (stdGaussian E)) :=
  measurePreserving_fst.comp
    (((preCollisionMap_measurePreserving F ell t s n hsn).symm
      (preCollisionMap F ell t s n hsn).toMeasurableEquiv).comp
      (dormantOld_preserving ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ))

theorem collisionTapeOutput_preserving (hκ : ConditionallyInvariant (stdGaussian E) κ) :
    MeasurePreserving (fun z : GaussianPhase E × E => phaseRotate s n hsn (dormantNewState z))
      (dormantJoint ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ)
      (gaussianPhaseMeasure (F.law t)) :=
  (phaseRotate_measurePreserving (F.law t) s n hsn).comp
    (dormantNew_preserving ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ hκ)

/-- Stagewise density immediately after the dormant replacement and physical rotation. -/
def rotatedCollisionDensity (hκ : ConditionallyInvariant (stdGaussian E) κ) :
    Lp ℝ 2 ((F.law a).prod (stdGaussian E)) →L[ℝ] Lp ℝ 2 (gaussianPhaseMeasure (F.law t)) :=
  (phaseRotationPullback (F.law t) s n hsn).toContinuousLinearEquiv.toContinuousLinearMap.adjoint.comp
    (((dormantChannel ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ hκ).adjoint).comp
      ((preCollisionDensity F ell t s n hsn).toContinuousLinearMap.comp
        (Kinetic.hiddenEmbedding (F.law a)).toContinuousLinearMap))

/-- The collision-stage factorization follows from the literal old/new tape maps. -/
theorem rotatedCollisionDensity_eq_referenceChannel (hκ : ConditionallyInvariant (stdGaussian E) κ) :
    rotatedCollisionDensity F ell t s n hsn κ hκ =
      (referenceChannel (collisionTapeInput_preserving F ell t s n hsn κ)
        (collisionTapeOutput_preserving F t s n hsn κ hκ)).adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  change inner ℝ ((phaseRotationPullback (F.law t) s n hsn).toContinuousLinearEquiv.toContinuousLinearMap.adjoint
    ((dormantChannel ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ hκ).adjoint
      (preCollisionDensity F ell t s n hsn (Kinetic.hiddenEmbedding (F.law a) f)))) g = _
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  have hd := (dormantChannel ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ hκ).adjoint_inner_left
    (phaseRotationPullback (F.law t) s n hsn g)
    (preCollisionDensity F ell t s n hsn (Kinetic.hiddenEmbedding (F.law a) f))
  apply hd.trans
  rw [referenceChannel_pairing]
  change inner ℝ (preCollisionDensity F ell t s n hsn (Kinetic.hiddenEmbedding (F.law a) f))
    (referenceChannel (dormantOld_preserving ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ)
      (dormantNew_preserving ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ hκ)
      (phaseRotationPullback (F.law t) s n hsn g)) = _
  apply (referenceChannel_pairing
    (dormantOld_preserving ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ)
    (dormantNew_preserving ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ hκ)
    (preCollisionDensity F ell t s n hsn (Kinetic.hiddenEmbedding (F.law a) f))
    (phaseRotationPullback (F.law t) s n hsn g)).trans
  apply integral_congr_ae
  have hpre := (Lp.coeFn_compMeasurePreserving (Kinetic.hiddenEmbedding (F.law a) f)
    ((preCollisionMap_measurePreserving F ell t s n hsn).symm
      (preCollisionMap F ell t s n hsn).toMeasurableEquiv)).trans
    (((preCollisionMap_measurePreserving F ell t s n hsn).symm
      (preCollisionMap F ell t s n hsn).toMeasurableEquiv).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving f measurePreserving_fst))
  have hrot := pullback_coeFn (phaseRotate s n hsn).toMeasurableEquiv
    (phaseRotate_measurePreserving (F.law t) s n hsn) g
  filter_upwards [(dormantOld_preserving ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ).quasiMeasurePreserving.ae hpre,
    (dormantNew_preserving ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ hκ).quasiMeasurePreserving.ae hrot]
    with z hz hr
  change preCollisionDensity F ell t s n hsn (Kinetic.hiddenEmbedding (F.law a) f) z.1 = _ at hz
  change phaseRotationPullback (F.law t) s n hsn g (dormantNewState z) = _ at hr
  rw [hz, hr]
  rfl

/-- Exact factorization of the physical fixed-clock tape into the collision
stage, correlated reheating, and visible momentum OU. -/
theorem fixedClockChannel_factorization (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ) :
    fixedClockChannel F ell t s n hsn κ hκ τ Γ hΓ =
      (referenceChannel (collisionTapeInput_preserving F ell t s n hsn κ)
        (collisionTapeOutput_preserving F t s n hsn κ hκ)).comp
      ((referenceChannel (measurePreserving_fst (ν := stdGaussian E))
        (correlatedHeatObservation_measurePreserving (F.law t) τ n s (by nlinarith [hsn]))).comp
        (ouProduct (heatedLaw (F.law t) τ) Γ hΓ)) := by
  let hp := collisionTapeInput_preserving F ell t s n hsn κ
  let hq := collisionTapeOutput_preserving F t s n hsn κ hκ
  let hheat := correlatedHeatObservation_measurePreserving (F.law t) τ n s (by nlinarith [hsn])
  let hou := ouProductObservation_measurePreserving (E := E) (heatedLaw (F.law t) τ) Γ hΓ
  have h1 := referenceChannel_independent_noise hp hq hheat
  have h2 := referenceChannel_independent_noise
    (hp.comp (measurePreserving_fst (ν := stdGaussian E)))
    (hheat.comp (hq.prod (MeasurePreserving.id (stdGaussian E)))) hou
  change fixedClockChannel F ell t s n hsn κ hκ τ Γ hΓ =
    (referenceChannel (hp.comp (measurePreserving_fst (ν := stdGaussian E)))
      (hheat.comp (hq.prod (MeasurePreserving.id (stdGaussian E))))).comp
        (ouProduct (heatedLaw (F.law t) τ) Γ hΓ) at h2
  rw [h2, h1, ContinuousLinearMap.comp_assoc]

/-- Source-coefficient density factorization of the actual fixed-clock kernel.
Every factor is the actual map or conditional channel appearing in the tape. -/
theorem fixedClockDensity_factorization
    (hκ : ConditionallyInvariant (stdGaussian E) κ) (τ Γ : ℝ) (hΓ : 0 ≤ Γ) :
    fixedClockDensity F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ τ Γ hΓ =
      (ouProduct (heatedLaw (F.law t) τ) Γ hΓ).comp
        ((reheatingDensity (F.law t) τ).comp
          (rotatedCollisionDensity F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ)) := by
  have h := congrArg ContinuousLinearMap.adjoint
    (fixedClockChannel_factorization F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ τ Γ hΓ)
  have hheat : (referenceChannel (measurePreserving_fst (μ := gaussianPhaseMeasure (F.law t)) (ν := stdGaussian E))
      (correlatedHeatObservation_measurePreserving (F.law t) τ (Real.sqrt 3/2) (1/2)
        (by nlinarith [source_split_coefficients]))).adjoint = reheatingDensity (F.law t) τ :=
    (reheatingDensity_eq_referenceChannel_adjoint (F.law t) τ).symm
  change fixedClockDensity F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ τ Γ hΓ = _ at h
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ouProduct_adjoint, hheat, ← rotatedCollisionDensity_eq_referenceChannel F ell t
      (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ] at h
  exact h.trans (ContinuousLinearMap.comp_assoc _ _ _)

/-- Applied form displays each physical density stage in source order. -/
theorem fixedClockDensity_factorization_apply
    (hκ : ConditionallyInvariant (stdGaussian E) κ) (τ Γ : ℝ) (hΓ : 0 ≤ Γ)
    (f : Lp ℝ 2 ((F.law a).prod (stdGaussian E))) :
    fixedClockDensity F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ τ Γ hΓ f =
      ouProduct (heatedLaw (F.law t) τ) Γ hΓ
        (reheatingDensity (F.law t) τ
          ((phaseRotationPullback (F.law t) (1/2) (Real.sqrt 3/2) source_split_coefficients).symm
            ((dormantChannel ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ hκ).adjoint
              (preCollisionDensity F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients
                (Kinetic.hiddenEmbedding (F.law a) f))))) := by
  rw [fixedClockDensity_factorization]
  simp only [ContinuousLinearMap.comp_apply, rotatedCollisionDensity]
  rw [(phaseRotationPullback (F.law t) (1/2) (Real.sqrt 3/2) source_split_coefficients).adjoint_eq_symm]
  rfl

end AcceleratedLogConcave.Kinetic
