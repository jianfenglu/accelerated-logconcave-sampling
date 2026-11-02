import AcceleratedLogConcave.Kinetic.Mixing.Factorization
import AcceleratedLogConcave.Kinetic.ReferenceFlow.PhysicalLaw

/-! Alignment of the literal split/flow/collision tape with the actual physical
transport used by the Hamiltonian energy estimate. The initial hidden sign
cancels on visible densities by their genuine hidden-coordinate independence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating ConditionalContraction
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)

/-- Full L2 density transport through the actual physical reference flow. -/
def physicalDensityTransport (t : Icc a b) :
    Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (gaussianPhaseMeasure (F.law t)) :=
  (pullback (physicalReferenceFlow F ell s n hsn t).toMeasurableEquiv
    (physicalReferenceFlow_measurePreserving F ell s n hsn t)).symm

/-- Actual representative of the transported density. -/
theorem physicalDensityTransport_coe (t : Icc a b)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    physicalDensityTransport F ell s n hsn t f =ᵐ[gaussianPhaseMeasure (F.law t)]
      fun z => f ((physicalReferenceFlow F ell s n hsn t).symm z) :=
  Lp.coeFn_compMeasurePreserving f _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The split inverse and the final rotation have the same visible coordinates.
The only difference is the unused hidden sign. -/
theorem phaseSplit_symm_visible (z : GaussianPhase E) :
    ((phaseSplit s n hsn).symm z).1 = (phaseRotate s n hsn z).1 := rfl

/-- The full physical flow is the identity at the initial clock. -/
theorem physicalReferenceFlow_initial (z : GaussianPhase E) :
    physicalReferenceFlow F ell s n hsn F.leftTime z = z := by
  rw [← flow_eq_physicalReferenceFlow]
  exact OAI.LogConcaveSampling.GlobalODE.flow_initial
    (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_continuous F ell s n hsn) F.leftTime z

/-- Physical transport agrees with the actual backward compact test curve at
initial terminal time. This permits the proved core energy estimate to apply
to the same L2 operator that appears in the literal tape. -/
theorem physicalDensityTransport_eq_physicalTransportLp
    {φ : GaussianPhase E → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    physicalDensityTransport F ell s n hsn ⟨t, ht.1.le, ht.2.le⟩
      ((hφ.continuous.memLp_of_hasCompactSupport (μ := gaussianPhaseMeasure (F.law a)) (p := 2) hc).toLp φ) =
      physicalTransportLp F ell s n hsn F.leftTime hφ hc t ht := by
  apply Lp.ext
  have hp := physicalDensityTransport_coe F ell s n hsn ⟨t, ht.1.le, ht.2.le⟩
    ((hφ.continuous.memLp_of_hasCompactSupport (μ := gaussianPhaseMeasure (F.law a)) (p := 2) hc).toLp φ)
  have hi := ((physicalReferenceFlow_measurePreserving F ell s n hsn ⟨t, ht.1.le, ht.2.le⟩).symm
    (physicalReferenceFlow F ell s n hsn ⟨t, ht.1.le, ht.2.le⟩).toMeasurableEquiv).quasiMeasurePreserving.ae
      (hφ.continuous.memLp_of_hasCompactSupport (μ := gaussianPhaseMeasure (F.law a)) (p := 2) hc).coeFn_toLp
  have htcoe := (physicalTransportTest_memLp F ell s n hsn F.leftTime hφ hc t ht).coeFn_toLp
  filter_upwards [hp, hi, htcoe] with z hpz hiz htz
  change (physicalTransportLp F ell s n hsn F.leftTime hφ hc t ht) z =
    physicalTransportTest F ell s n hsn F.leftTime φ t z at htz
  apply hpz.trans
  apply hiz.trans
  rw [htz, physicalTransportTest_eq F ell s n hsn F.leftTime φ t ⟨ht.1.le, ht.2.le⟩ z,
    physicalReferenceFlow_initial]
  rfl

/-- The moving-frame core is the spatial unitary applied to the actual full
physical density transport, on precisely the compact core used in transport. -/
theorem physicalMovingCoreLp_eq_densityTransport
    {φ : GaussianPhase E → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    physicalMovingCoreLp F ell s n hsn F.leftTime hφ.continuous hc t =
      F.phaseUnitary ⟨t, ht.1.le, ht.2.le⟩
        (physicalDensityTransport F ell s n hsn ⟨t, ht.1.le, ht.2.le⟩
          ((hφ.continuous.memLp_of_hasCompactSupport
            (μ := gaussianPhaseMeasure (F.law a)) hc).toLp φ)) := by
  rw [physicalMovingCoreLp_eq_phaseUnitary F ell s n hsn F.leftTime hφ hc t ht,
    physicalDensityTransport_eq_physicalTransportLp F ell s n hsn hφ hc t ht]

/-- Rotating the literal split-flow density gives exactly physical transport
of the visible density. No symmetry assumption on that visible density is used. -/
theorem preCollisionDensity_rotate_hidden (t : Icc a b)
    (f : Lp ℝ 2 ((F.law a).prod (stdGaussian E))) :
    (phaseRotationPullback (F.law t) s n hsn).symm
      (preCollisionDensity F ell t s n hsn (Kinetic.hiddenEmbedding (F.law a) f)) =
      physicalDensityTransport F ell s n hsn t (Kinetic.hiddenEmbedding (F.law a) f) := by
  apply Lp.ext
  let hrot := (phaseRotate_measurePreserving (F.law t) s n hsn).symm
    (phaseRotate (E := E) s n hsn).toMeasurableEquiv
  let hpre := (preCollisionMap_measurePreserving F ell t s n hsn).symm
    (preCollisionMap F ell t s n hsn).toMeasurableEquiv
  let hphys := (physicalReferenceFlow_measurePreserving F ell s n hsn t).symm
    (physicalReferenceFlow F ell s n hsn t).toMeasurableEquiv
  have hleft := Lp.coeFn_compMeasurePreserving
    (preCollisionDensity F ell t s n hsn (Kinetic.hiddenEmbedding (F.law a) f)) hrot
  have hprecoe := hrot.quasiMeasurePreserving.ae
    (preCollisionDensity_coe F ell t s n hsn (Kinetic.hiddenEmbedding (F.law a) f))
  have hhleft := (hpre.comp hrot).quasiMeasurePreserving.ae
    (Lp.coeFn_compMeasurePreserving f measurePreserving_fst)
  have hright := physicalDensityTransport_coe F ell s n hsn t (Kinetic.hiddenEmbedding (F.law a) f)
  have hhright := hphys.quasiMeasurePreserving.ae
    (Lp.coeFn_compMeasurePreserving f measurePreserving_fst)
  filter_upwards [hleft,hprecoe,hhleft,hright,hhright] with z hl hp hhl hr hhr
  change ((phaseRotationPullback (F.law t) s n hsn).symm
    (preCollisionDensity F ell t s n hsn (Kinetic.hiddenEmbedding (F.law a) f))) z = _ at hl
  simp only [Function.comp_apply] at hl hhl hhr
  change (Kinetic.hiddenEmbedding (F.law a) f)
    ((preCollisionMap F ell t s n hsn).symm ((phaseRotate s n hsn).symm z)) = _ at hhl
  change (Kinetic.hiddenEmbedding (F.law a) f)
    ((physicalReferenceFlow F ell s n hsn t).symm z) = _ at hhr
  exact hl.trans (hp.trans (hhl.trans (hhr.symm.trans hr.symm)))

section DormantRotation
variable (μ : Measure E) [IsProbabilityMeasure μ]
  (κ : Kernel (GaussianPhase E) E) [IsMarkovKernel κ]
  (hκ : ConditionallyInvariant (stdGaussian E) κ)

/-- Both sides of the actual dormant joint law expressed in physical coordinates. -/
def physicalDormantOld (z : GaussianPhase E × E) := phaseRotate s n hsn z.1

def physicalDormantNew (z : GaussianPhase E × E) := phaseRotate s n hsn (dormantNewState z)

theorem physicalDormantOld_preserving :
    MeasurePreserving (physicalDormantOld s n hsn)
      (dormantJoint (μ.prod (stdGaussian E)) (stdGaussian E) κ) (gaussianPhaseMeasure μ) :=
  (phaseRotate_measurePreserving μ s n hsn).comp
    (dormantOld_preserving (μ.prod (stdGaussian E)) (stdGaussian E) κ)

include hκ in
theorem physicalDormantNew_preserving :
    MeasurePreserving (physicalDormantNew s n hsn)
      (dormantJoint (μ.prod (stdGaussian E)) (stdGaussian E) κ) (gaussianPhaseMeasure μ) :=
  (phaseRotate_measurePreserving μ s n hsn).comp
    (dormantNew_preserving (μ.prod (stdGaussian E)) (stdGaussian E) κ hκ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The literal collision keeps the position fixed even after rotation. -/
theorem physicalDormant_position (z : GaussianPhase E × E) :
    (physicalDormantOld s n hsn z).1.1 = (physicalDormantNew s n hsn z).1.1 := rfl

/-- Actual physical-coordinate conditional channel, constructed from its joint law. -/
def physicalDormantChannel : Lp ℝ 2 (gaussianPhaseMeasure μ) →L[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure μ) :=
  referenceChannel (physicalDormantOld_preserving s n hsn μ κ)
    (physicalDormantNew_preserving s n hsn μ κ hκ)

/-- Rotating the joint law conjugates its actual density channel by the Gaussian
unitary. This is an equality of constructed channels, not a kernel premise. -/
theorem physicalDormantChannel_adjoint_apply (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    (physicalDormantChannel s n hsn μ κ hκ).adjoint f =
      (phaseRotationPullback μ s n hsn).symm
        ((dormantChannel (μ.prod (stdGaussian E)) (stdGaussian E) κ hκ).adjoint
          (phaseRotationPullback μ s n hsn f)) := by
  let U := phaseRotationPullback μ s n hsn
  let Q := dormantChannel (μ.prod (stdGaussian E)) (stdGaussian E) κ hκ
  apply ext_inner_right ℝ
  intro g
  have hr : inner ℝ (U.symm (Q.adjoint (U f))) g = inner ℝ (U f) (Q (U g)) := by
    rw [← U.inner_map_map, U.apply_symm_apply]
    exact Q.adjoint_inner_left _ _
  change inner ℝ ((physicalDormantChannel s n hsn μ κ hκ).adjoint f) g =
    inner ℝ (U.symm (Q.adjoint (U f))) g
  rw [hr, ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ f (referenceChannel (physicalDormantOld_preserving s n hsn μ κ)
    (physicalDormantNew_preserving s n hsn μ κ hκ) g) = inner ℝ (U f) (Q (U g))
  rw [referenceChannel_pairing]
  change _ = inner ℝ (U f)
    (referenceChannel (dormantOld_preserving (μ.prod (stdGaussian E)) (stdGaussian E) κ)
      (dormantNew_preserving (μ.prod (stdGaussian E)) (stdGaussian E) κ hκ) (U g))
  apply Eq.trans ?_ (referenceChannel_pairing
    (dormantOld_preserving (μ.prod (stdGaussian E)) (stdGaussian E) κ)
    (dormantNew_preserving (μ.prod (stdGaussian E)) (stdGaussian E) κ hκ) (U f) (U g)).symm
  apply integral_congr_ae
  have hf := (dormantOld_preserving (μ.prod (stdGaussian E)) (stdGaussian E) κ).quasiMeasurePreserving.ae
    (pullback_coeFn (phaseRotate s n hsn).toMeasurableEquiv (phaseRotate_measurePreserving μ s n hsn) f)
  have hg := (dormantNew_preserving (μ.prod (stdGaussian E)) (stdGaussian E) κ hκ).quasiMeasurePreserving.ae
    (pullback_coeFn (phaseRotate s n hsn).toMeasurableEquiv (phaseRotate_measurePreserving μ s n hsn) g)
  filter_upwards [hf,hg] with z hfz hgz
  change (U f) z.1 = f (physicalDormantOld s n hsn z) at hfz
  change (U g) (dormantNewState z) = g (physicalDormantNew s n hsn z) at hgz
  rw [hfz,hgz]

end DormantRotation

/-- Exact physical-density factorization of the pre-reheating collision stage. -/
theorem rotatedCollisionDensity_physical (t : Icc a b)
    (κ : Kernel (GaussianPhase E) E) [IsMarkovKernel κ]
    (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (f : Lp ℝ 2 ((F.law a).prod (stdGaussian E))) :
    rotatedCollisionDensity F ell t s n hsn κ hκ f =
      (physicalDormantChannel s n hsn (F.law t) κ hκ).adjoint
        (physicalDensityTransport F ell s n hsn t (Kinetic.hiddenEmbedding (F.law a) f)) := by
  rw [physicalDormantChannel_adjoint_apply]
  have hp := congrArg (phaseRotationPullback (F.law t) s n hsn)
    (preCollisionDensity_rotate_hidden F ell s n hsn t f)
  simp only [LinearIsometryEquiv.apply_symm_apply] at hp
  rw [← hp]
  change (phaseRotationPullback (F.law t) s n hsn).toContinuousLinearEquiv.toContinuousLinearMap.adjoint
    ((dormantChannel ((F.law t).prod (stdGaussian E)) (stdGaussian E) κ hκ).adjoint
      (preCollisionDensity F ell t s n hsn (Kinetic.hiddenEmbedding (F.law a) f))) = _
  rw [(phaseRotationPullback (F.law t) s n hsn).adjoint_eq_symm]
  rfl

/-- The actual fixed-clock density is physical transport, the actual rotated
conditional collision, correlated reheating, and the actual momentum OU. -/
theorem fixedClockDensity_physical_factorization (t : Icc a b)
    (κ : Kernel (GaussianPhase E) E) [IsMarkovKernel κ]
    (hκ : ConditionallyInvariant (stdGaussian E) κ)
    (τ Γ : ℝ) (hΓ : 0 ≤ Γ)
    (f : Lp ℝ 2 ((F.law a).prod (stdGaussian E))) :
    fixedClockDensity F ell t (1/2) (Real.sqrt 3/2) source_split_coefficients κ hκ τ Γ hΓ f =
      ouProduct (heatedLaw (F.law t) τ) Γ hΓ
        (reheatingDensity (F.law t) τ
          ((physicalDormantChannel (1/2) (Real.sqrt 3/2) source_split_coefficients (F.law t) κ hκ).adjoint
            (physicalDensityTransport F ell (1/2) (Real.sqrt 3/2) source_split_coefficients t
              (Kinetic.hiddenEmbedding (F.law a) f)))) := by
  rw [fixedClockDensity_factorization]
  simp only [ContinuousLinearMap.comp_apply]
  rw [rotatedCollisionDensity_physical]

end AcceleratedLogConcave.Kinetic
