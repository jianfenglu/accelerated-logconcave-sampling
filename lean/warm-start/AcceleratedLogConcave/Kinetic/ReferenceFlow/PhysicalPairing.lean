import AcceleratedLogConcave.Kinetic.ReferenceFlow.PhysicalTransport

/-! Actual L2 core identification with the moving corrector's spatial unitary. -/
noncomputable section
set_option maxHeartbeats 1600000
open Set Function MeasureTheory InnerProductSpace
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)

 theorem physicalTransportTest_contDiff (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    ContDiff ℝ 1 (physicalTransportTest F ell s n hsn T φ t) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  exact (backwardTest_contDiffAt_one F.ordered (physicalDrift_continuous F ell s n hsn)
    (physicalDrift_lipschitz F ell s n hsn) (physicalDriftDerivative_continuous F ell s n hsn)
    (physicalDrift_hasFDerivAt F ell s n hsn) T hφ (t,z) ht).comp z
      (contDiffAt_const.prodMk contDiffAt_id)

 theorem physicalTransportTest_hasCompactSupport (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hc : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (physicalTransportTest F ell s n hsn T φ t) := by
  obtain ⟨S,hS,hzero⟩ := backwardTest_common_compact_support F.ordered
    (physicalDrift_continuous F ell s n hsn) (physicalDrift_lipschitz F ell s n hsn) T hc
  exact HasCompactSupport.intro hS (hzero t)

 theorem physicalTransportTest_memLp (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    MemLp (physicalTransportTest F ell s n hsn T φ t) 2 (gaussianPhaseMeasure (F.law t)) :=
  (physicalTransportTest_contDiff F ell s n hsn T hφ t ht).continuous.memLp_of_hasCompactSupport
    (physicalTransportTest_hasCompactSupport F ell s n hsn T hc t)

def physicalTransportLp (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :=
  (physicalTransportTest_memLp F ell s n hsn T hφ hc t ht).toLp _

 theorem physicalMovingCoreLp_eq_phaseUnitary (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    physicalMovingCoreLp F ell s n hsn T hφ.continuous hc t =
      F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ (physicalTransportLp F ell s n hsn T hφ hc t ht) := by
  apply Lp.ext
  have hcoe := (movingFrameCore_memLp F.ordered
    (physicalDrift_continuous F ell s n hsn) (physicalDrift_continuous F 0 s n hsn)
    (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_lipschitz F 0 s n hsn)
    (gaussianPhaseMeasure (F.law a)) T hφ.continuous hc t).coeFn_toLp
  have hp := gaussianPhasePullback_coe (F.flow ⟨t,ht.1.le,ht.2.le⟩).toMeasurableEquiv
    (F.flow_measurePreserving ⟨t,ht.1.le,ht.2.le⟩)
    (physicalTransportLp F ell s n hsn T hφ hc t ht)
  have htcoe := (gaussianPhaseEquiv_measurePreserving
    (F.flow ⟨t,ht.1.le,ht.2.le⟩).toMeasurableEquiv
    (F.flow_measurePreserving ⟨t,ht.1.le,ht.2.le⟩)).quasiMeasurePreserving.ae
      (physicalTransportTest_memLp F ell s n hsn T hφ hc t ht).coeFn_toLp
  filter_upwards [hcoe,hp,htcoe] with z hz hpz htz
  change (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc t) z =
    physicalMovingCore F ell s n hsn T φ (t,z) at hz
  change (F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ (physicalTransportLp F ell s n hsn T hφ hc t ht)) z =
    (physicalTransportLp F ell s n hsn T hφ hc t ht) ((F.flow ⟨t,ht.1.le,ht.2.le⟩ z.1.1,z.1.2),z.2) at hpz
  change (physicalTransportLp F ell s n hsn T hφ hc t ht) ((F.flow ⟨t,ht.1.le,ht.2.le⟩ z.1.1,z.1.2),z.2) =
    physicalTransportTest F ell s n hsn T φ t ((F.flow ⟨t,ht.1.le,ht.2.le⟩ z.1.1,z.1.2),z.2) at htz
  rw [hz,hpz,htz]
  change physicalTransportTest F ell s n hsn T φ t
    (spaceTimeForward F.ordered (physicalDrift_continuous F 0 s n hsn)
      (physicalDrift_lipschitz F 0 s n hsn) (t,z)).2 = _
  rw [physicalFrame_eq F s n hsn t ⟨ht.1.le,ht.2.le⟩]

end AcceleratedLogConcave.Kinetic
