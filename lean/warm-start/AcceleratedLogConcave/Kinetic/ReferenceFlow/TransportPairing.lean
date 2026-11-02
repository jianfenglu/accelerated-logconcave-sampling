import AcceleratedLogConcave.Kinetic.ReferenceFlow.HamiltonianCore
import AcceleratedLogConcave.Kinetic.ConditionalContraction.TransportCurrent

/-! The two differentiated corrector pairings are the true Hamiltonian current. -/
noncomputable section
set_option maxHeartbeats 1600000
open Set Function MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell : ℝ)

 theorem physicalHamiltonian_current (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    let f := physicalTransportLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t ht;
    let k := physicalHamiltonianLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t ht;
    let A := F.physicalCorrector ⟨t,ht.1.le,ht.2.le⟩;
    -(inner ℝ k (A f)) - inner ℝ f (A k) =
      hamiltonianCorrectorCurrent (F.law t) (F.potential t) (F.potential_C2 t)
        (F.integrable t ⟨ht.1.le,ht.2.le⟩) (F.gibbs_law t ⟨ht.1.le,ht.2.le⟩)
        (F.lower t) 1 (F.lower_pos t ⟨ht.1.le,ht.2.le⟩)
        (F.hessian_lower t ⟨ht.1.le,ht.2.le⟩)
        (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1.le,ht.2.le⟩) f
        (physicalTransportTest F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T φ t) := by
  dsimp only
  let f := physicalTransportLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t ht
  let k := physicalHamiltonianLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t ht
  let A := F.physicalCorrector ⟨t,ht.1.le,ht.2.le⟩
  have hk := (hamiltonianTestDerivative_memLp (gaussianPhaseMeasure (F.law t))
    (F.potential t) (F.potential_C2 t) (1/2) (Real.sqrt 3/2)
    (physicalTransportTest F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T φ t)
    (physicalTransportTest_contDiff F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ t ht)
    (physicalTransportTest_hasCompactSupport F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hc t)).coeFn_toLp
  change k =ᵐ[gaussianPhaseMeasure (F.law t)] _ at hk
  have hp (v : Lp ℝ 2 (gaussianPhaseMeasure (F.law t))) :
      inner ℝ k v = ∫ z, v z * hamiltonianTestDerivative (F.potential t) (1/2) (Real.sqrt 3/2)
        (physicalTransportTest F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T φ t) z
        ∂gaussianPhaseMeasure (F.law t) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hk] with z hz
    rw [hz]
    rfl
  change -(inner ℝ k (A f)) - inner ℝ f (A k) = _
  rw [← A.adjoint_inner_left k f, real_inner_comm k (A.adjoint f),
    hp, hp]
  unfold hamiltonianCorrectorCurrent
  dsimp only [A, f, ReferencePoissonFamily.physicalCorrector]
  ring

theorem corrector_apply_phaseUnitary (t : ℝ) (ht : t ∈ Ioo a b)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law t))) :
    F.corrector t (F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ f) =
      F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ (F.physicalCorrector ⟨t,ht.1.le,ht.2.le⟩ f) := by
  rw [F.corrector_eq_physical t ht]
  change F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩
    (F.physicalCorrector ⟨t,ht.1.le,ht.2.le⟩
      ((F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩).symm (F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem transported_corrector_pairings (t : ℝ) (ht : t ∈ Ioo a b)
    (f k : Lp ℝ 2 (gaussianPhaseMeasure (F.law t))) :
    inner ℝ (-ell • F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ k)
      (F.corrector t (F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ f)) +
    inner ℝ (F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ f)
      (F.corrector t (-ell • F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ k)) =
    ell * (-inner ℝ k (F.physicalCorrector ⟨t,ht.1.le,ht.2.le⟩ f) -
      inner ℝ f (F.physicalCorrector ⟨t,ht.1.le,ht.2.le⟩ k)) := by
  rw [map_smul, corrector_apply_phaseUnitary F t ht, corrector_apply_phaseUnitary F t ht]
  simp only [real_inner_smul_left, real_inner_smul_right, LinearIsometryEquiv.inner_map_map]
  ring

/-- The actual compact-core moving current differentiates into the proved
Hamiltonian current and W04's material-corrector term. -/
theorem physicalCoreCurrent_hasDerivAt (T : Icc a b) {φ : GaussianPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    let g := physicalMovingCoreLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ.continuous hc;
    let f := physicalTransportLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t ht;
    HasDerivAt (fun u => inner ℝ (g u) (F.corrector u (g u)))
      (ell * hamiltonianCorrectorCurrent (F.law t) (F.potential t) (F.potential_C2 t)
        (F.integrable t ⟨ht.1.le,ht.2.le⟩) (F.gibbs_law t ⟨ht.1.le,ht.2.le⟩)
        (F.lower t) 1 (F.lower_pos t ⟨ht.1.le,ht.2.le⟩)
        (F.hessian_lower t ⟨ht.1.le,ht.2.le⟩)
        (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1.le,ht.2.le⟩) f
        (physicalTransportTest F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T φ t) +
      inner ℝ (g t) (F.materialCorrector t ht (g t))) t := by
  dsimp only
  have hd := physicalMovingCoreLp_hamiltonian_derivative F ell (1/2) (Real.sqrt 3/2)
    source_split_coefficients T hφ hc t ht
  have hj := F.corrector_quadratic_hasDerivAt t ht _ _ hd
  rw [physicalMovingCoreLp_eq_phaseUnitary F ell (1/2) (Real.sqrt 3/2)
    source_split_coefficients T hφ hc t ht,
    transported_corrector_pairings F ell t ht,
    physicalHamiltonian_current F ell T hφ hc t ht] at hj
  rw [physicalMovingCoreLp_eq_phaseUnitary F ell (1/2) (Real.sqrt 3/2)
    source_split_coefficients T hφ hc t ht]
  exact hj

end AcceleratedLogConcave.Kinetic
