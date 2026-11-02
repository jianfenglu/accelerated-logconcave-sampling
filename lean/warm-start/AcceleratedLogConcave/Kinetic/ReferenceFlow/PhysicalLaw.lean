import AcceleratedLogConcave.Kinetic.ReferenceFlow.PhysicalFlow
import AcceleratedLogConcave.Kinetic.ReferenceFlow.PhysicalPairing
import AcceleratedLogConcave.Kinetic.ConditionalContraction.CoreCentering

/-! The actual physical-coordinate flow transports the true Gaussian phase law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)

def physicalReferenceFlow (t : Icc a b) : GaussianPhase E ≃ₜ GaussianPhase E :=
  (phaseRotate s n hsn).symm.trans ((referenceExtendedFlow F ell t).trans (phaseRotate s n hsn))

theorem physicalReferenceFlow_measurePreserving (t : Icc a b) :
    MeasurePreserving (physicalReferenceFlow F ell s n hsn t)
      (gaussianPhaseMeasure (F.law a)) (gaussianPhaseMeasure (F.law t)) :=
  (phaseRotate_measurePreserving (F.law t) s n hsn).comp
    ((referenceExtendedFlow_measurePreserving F ell t).comp
      ((phaseRotate_measurePreserving (F.law a) s n hsn).symm
        (phaseRotate s n hsn).toMeasurableEquiv))

theorem flow_eq_physicalReferenceFlow (t : Icc a b) (z : GaussianPhase E) :
    flow (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_continuous F ell s n hsn)
      F.leftTime z t = physicalReferenceFlow F ell s n hsn t z := by
  rw [physicalFlow_eq]
  rfl

theorem flowHomeomorph_eq_physicalReferenceFlow (t : Icc a b) :
    flowHomeomorph (physicalDrift_lipschitz F ell s n hsn)
      (physicalDrift_continuous F ell s n hsn) F.leftTime t = physicalReferenceFlow F ell s n hsn t := by
  apply Homeomorph.ext
  intro z
  exact flow_eq_physicalReferenceFlow F ell s n hsn t z

theorem physicalTransportTest_eq (T : Icc a b) (φ : GaussianPhase E → ℝ)
    (t : ℝ) (ht : t ∈ Icc a b) (z : GaussianPhase E) :
    physicalTransportTest F ell s n hsn T φ t z =
      φ (physicalReferenceFlow F ell s n hsn T ((physicalReferenceFlow F ell s n hsn ⟨t,ht⟩).symm z)) := by
  unfold physicalTransportTest backwardTest spaceTimeBackward
  simp only [projIcc_of_mem _ ht]
  change φ (flowHomeomorph (physicalDrift_lipschitz F ell s n hsn)
    (physicalDrift_continuous F ell s n hsn) F.leftTime T
      ((flowHomeomorph (physicalDrift_lipschitz F ell s n hsn)
        (physicalDrift_continuous F ell s n hsn) F.leftTime ⟨t,ht⟩).symm z)) = _
  rw [flowHomeomorph_eq_physicalReferenceFlow, flowHomeomorph_eq_physicalReferenceFlow]

/-- The actual backward density map sends the time-t law to the terminal law. -/
theorem physicalTransport_map_measurePreserving (T t : Icc a b) :
    MeasurePreserving (fun z => physicalReferenceFlow F ell s n hsn T
      ((physicalReferenceFlow F ell s n hsn t).symm z))
      (gaussianPhaseMeasure (F.law t)) (gaussianPhaseMeasure (F.law T)) :=
  (physicalReferenceFlow_measurePreserving F ell s n hsn T).comp
    ((physicalReferenceFlow_measurePreserving F ell s n hsn t).symm
      (physicalReferenceFlow F ell s n hsn t).toMeasurableEquiv)

/-- Transport preserves the actual density norm exactly. -/
theorem physicalTransportLp_norm_sq (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    ‖physicalTransportLp F ell s n hsn T hφ hc t ht‖^2 =
      ∫ z, (φ z)^2 ∂gaussianPhaseMeasure (F.law T) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  let e := (physicalReferenceFlow F ell s n hsn ⟨t,ht.1.le,ht.2.le⟩).toMeasurableEquiv.symm.trans
    (physicalReferenceFlow F ell s n hsn T).toMeasurableEquiv
  have hi : (∫ z, inner ℝ ((physicalTransportLp F ell s n hsn T hφ hc t ht) z)
      ((physicalTransportLp F ell s n hsn T hφ hc t ht) z) ∂gaussianPhaseMeasure (F.law t)) =
      ∫ z, (φ (e z))^2 ∂gaussianPhaseMeasure (F.law t) := by
    apply integral_congr_ae
    filter_upwards [(physicalTransportTest_memLp F ell s n hsn T hφ hc t ht).coeFn_toLp] with z hz
    change (physicalTransportLp F ell s n hsn T hφ hc t ht) z = _ at hz
    rw [hz, physicalTransportTest_eq F ell s n hsn T φ t ⟨ht.1.le,ht.2.le⟩ z]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    rfl
  rw [hi]
  exact (physicalTransport_map_measurePreserving F ell s n hsn T ⟨t,ht.1.le,ht.2.le⟩).integral_comp
    e.measurableEmbedding (fun z => (φ z)^2)

/-- A genuinely centered terminal core stays centered under the actual flow. -/
theorem physicalTransportLp_mean (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    mean (F.law t) (gaussianAverage (F.law t) (physicalTransportLp F ell s n hsn T hφ hc t ht)) =
      ∫ z, φ z ∂gaussianPhaseMeasure (F.law T) := by
  rw [ConditionalContraction.mean_gaussianAverage, mean_apply]
  let e := (physicalReferenceFlow F ell s n hsn ⟨t,ht.1.le,ht.2.le⟩).toMeasurableEquiv.symm.trans
    (physicalReferenceFlow F ell s n hsn T).toMeasurableEquiv
  have he : (physicalTransportLp F ell s n hsn T hφ hc t ht) =ᵐ[gaussianPhaseMeasure (F.law t)]
      fun z => φ (e z) := by
    filter_upwards [(physicalTransportTest_memLp F ell s n hsn T hφ hc t ht).coeFn_toLp] with z hz
    change (physicalTransportLp F ell s n hsn T hφ hc t ht) z = _ at hz
    rw [hz, physicalTransportTest_eq F ell s n hsn T φ t ⟨ht.1.le,ht.2.le⟩ z]
    rfl
  rw [integral_congr_ae he]
  exact (physicalTransport_map_measurePreserving F ell s n hsn T ⟨t,ht.1.le,ht.2.le⟩).integral_comp
    e.measurableEmbedding φ

end AcceleratedLogConcave.Kinetic
