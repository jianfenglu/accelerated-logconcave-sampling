import AcceleratedLogConcave.Kinetic.ReferenceFlow.PhysicalPairing

/-! The actual L2 Hamiltonian derivative of transported compact tests. -/
noncomputable section
set_option maxHeartbeats 1600000
open Set Function MeasureTheory InnerProductSpace
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 theorem hamiltonianTestDerivative_memLp (μ : Measure (GaussianPhase E)) [IsFiniteMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (s n : ℝ)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    MemLp (hamiltonianTestDerivative V s n φ) 2 μ := by
  have he : hamiltonianTestDerivative V s n φ = fun z =>
      fderiv ℝ φ z ((s • z.1.2 - n • z.2, -s • gradient V z.1.1), n • gradient V z.1.1) :=
    funext (hamiltonianTestDerivative_eq_fderiv V s n φ)
  rw [he]
  have hg : Continuous (gradient V) := continuous_iff_continuousAt.mpr
    (fun x => (gradient_hasFDerivAt_hessian hV x).continuousAt)
  have hd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hv : Continuous (fun z : GaussianPhase E =>
      ((s • z.1.2 - n • z.2, -s • gradient V z.1.1), n • gradient V z.1.1)) := by fun_prop
  apply (hd.clm_apply hv).memLp_of_hasCompactSupport
  apply HasCompactSupport.intro hc
  intro z hz
  rw [fderiv_of_notMem_tsupport ℝ hz]
  rfl

variable {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)

def physicalHamiltonianLp (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :=
  (hamiltonianTestDerivative_memLp (gaussianPhaseMeasure (F.law t))
    (F.potential t) (F.potential_C2 t) s n (physicalTransportTest F ell s n hsn T φ t)
    (physicalTransportTest_contDiff F ell s n hsn T hφ t ht)
    (physicalTransportTest_hasCompactSupport F ell s n hsn T hc t)).toLp _

theorem physicalMovingCoreLp_hamiltonian_derivative (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc)
      (-ell • F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ (physicalHamiltonianLp F ell s n hsn T hφ hc t ht)) t := by
  obtain ⟨d,hd,hrep⟩ := physicalMovingCoreLp_hasDerivAt F ell s n hsn T hφ hc t ht
  suffices he : d = -ell • F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩
      (physicalHamiltonianLp F ell s n hsn T hφ hc t ht) by simpa only [he] using hd
  apply Lp.ext
  have hp := gaussianPhasePullback_coe (F.flow ⟨t,ht.1.le,ht.2.le⟩).toMeasurableEquiv
    (F.flow_measurePreserving ⟨t,ht.1.le,ht.2.le⟩) (physicalHamiltonianLp F ell s n hsn T hφ hc t ht)
  have hmem := hamiltonianTestDerivative_memLp (gaussianPhaseMeasure (F.law t))
    (F.potential t) (F.potential_C2 t) s n (physicalTransportTest F ell s n hsn T φ t)
    (physicalTransportTest_contDiff F ell s n hsn T hφ t ht)
    (physicalTransportTest_hasCompactSupport F ell s n hsn T hc t)
  have hco := (gaussianPhaseEquiv_measurePreserving
    (F.flow ⟨t,ht.1.le,ht.2.le⟩).toMeasurableEquiv
    (F.flow_measurePreserving ⟨t,ht.1.le,ht.2.le⟩)).quasiMeasurePreserving.ae hmem.coeFn_toLp
  filter_upwards [hrep,hp,hco, Lp.coeFn_smul (-ell)
    (F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ (physicalHamiltonianLp F ell s n hsn T hφ hc t ht))] with z hz hpz hcz hsz
  change (F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ (physicalHamiltonianLp F ell s n hsn T hφ hc t ht)) z =
    (physicalHamiltonianLp F ell s n hsn T hφ hc t ht) ((F.flow ⟨t,ht.1.le,ht.2.le⟩ z.1.1,z.1.2),z.2) at hpz
  change (physicalHamiltonianLp F ell s n hsn T hφ hc t ht) ((F.flow ⟨t,ht.1.le,ht.2.le⟩ z.1.1,z.1.2),z.2) =
    hamiltonianTestDerivative (F.potential t) s n (physicalTransportTest F ell s n hsn T φ t)
      ((F.flow ⟨t,ht.1.le,ht.2.le⟩ z.1.1,z.1.2),z.2) at hcz
  rw [hz,hsz]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hpz,hcz,physicalMovingCore_derivative_eq F ell s n hsn T hφ t ht z]

end AcceleratedLogConcave.Kinetic
