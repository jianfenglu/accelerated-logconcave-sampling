import AcceleratedLogConcave.Kinetic.ReferenceFlow.TransportPairing

/-! The transport-current estimate for the actual transported compact core. -/
noncomputable section
set_option maxHeartbeats 1600000
open Set MeasureTheory InnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b)

 theorem phaseUnitary_macro_norm (t : Icc a b) (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law t))) :
    ‖gaussianPositionProjection (F.law a) (F.phaseUnitary t f)‖ =
      ‖gaussianPositionProjection (F.law t) f‖ := by
  change ‖gaussianPositionProjection (F.law a)
    (gaussianPhasePullback (F.flow t).toMeasurableEquiv (F.flow_measurePreserving t) f)‖ = _
  have hh := gaussianPositionProjection_phasePullback (F.flow t).toMeasurableEquiv
    (F.flow_measurePreserving t) f
  rw [hh, LinearIsometryEquiv.norm_map]

 theorem phaseUnitary_micro_norm (t : Icc a b) (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law t))) :
    ‖F.phaseUnitary t f - gaussianPositionProjection (F.law a) (F.phaseUnitary t f)‖ =
      ‖f - gaussianPositionProjection (F.law t) f‖ := by
  change ‖gaussianPhasePullback (F.flow t).toMeasurableEquiv (F.flow_measurePreserving t) f -
    gaussianPositionProjection (F.law a)
      (gaussianPhasePullback (F.flow t).toMeasurableEquiv (F.flow_measurePreserving t) f)‖ = _
  have hh := gaussianPositionProjection_phasePullback (F.flow t).toMeasurableEquiv
    (F.flow_measurePreserving t) f
  rw [hh, ← map_sub, LinearIsometryEquiv.norm_map]

 theorem transport_current_scalar (ell c M R N J B : ℝ) (hell : 0 ≤ ell)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hc : c ≤ ell/4)
    (hsplit : N = M^2+R^2) (hJ : J ≤ -M^2/4+9*R^2/4)
    (hB : B ≤ c*M*R) :
    ell*J+B ≤ -ell*N/8+3*ell*R^2 := by
  have h1 := mul_le_mul_of_nonneg_left hJ hell
  have h2 := mul_le_mul_of_nonneg_right hc (mul_nonneg hM hR)
  have h3 := mul_nonneg hell (sq_nonneg (M-R))
  have h4 := mul_nonneg hell (sq_nonneg R)
  rw [hsplit]
  nlinarith

/-- The actual core current obeys the manuscript transport estimate. -/
theorem physicalCoreCurrent_derivative_le (ell : ℝ) (hell : 0 ≤ ell)
    (T : Icc a b) {φ : GaussianPhase E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b)
    (hscale : |F.scale t| ≤ ell/4)
    (hmean : mean (F.law t) (gaussianAverage (F.law t)
      (physicalTransportLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t ht)) = 0) :
    let g := physicalMovingCoreLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ.continuous hc;
    let f := physicalTransportLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t ht;
    ∃ D : ℝ, HasDerivAt (fun u => inner ℝ (g u) (F.corrector u (g u))) D t ∧
      D ≤ -ell*‖f‖^2/8 + 3*ell*‖f-gaussianPositionProjection (F.law t) f‖^2 := by
  dsimp only
  refine ⟨_, physicalCoreCurrent_hasDerivAt F ell T hφ hc t ht, ?_⟩
  let f := physicalTransportLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t ht
  have hJ := hamiltonianCorrectorCurrent_le (F.law t) (F.potential t) (F.potential_C2 t)
    (F.integrable t ⟨ht.1.le,ht.2.le⟩) (F.gibbs_law t ⟨ht.1.le,ht.2.le⟩)
    (F.lower t) 1 (F.lower_pos t ⟨ht.1.le,ht.2.le⟩)
    (F.hessian_lower t ⟨ht.1.le,ht.2.le⟩)
    (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1.le,ht.2.le⟩) f hmean
    (physicalTransportTest F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T φ t)
    (physicalTransportTest_contDiff F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ t ht)
    (physicalTransportTest_hasCompactSupport F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hc t)
    (physicalTransportTest_memLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t ht).coeFn_toLp
  rw [physicalMovingCoreLp_eq_phaseUnitary F ell (1/2) (Real.sqrt 3/2)
    source_split_coefficients T hφ hc t ht]
  have hB := F.materialCorrector_macro_micro_bound t ht
    (F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ f) (F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ f)
  rw [phaseUnitary_macro_norm,phaseUnitary_micro_norm] at hB
  apply transport_current_scalar ell |F.scale t|
    ‖gaussianPositionProjection (F.law t) f‖ ‖f-gaussianPositionProjection (F.law t) f‖ (‖f‖^2)
    _ _ hell (norm_nonneg _) (norm_nonneg _) hscale
  · exact (gaussianPositionProjection_norm_sq (F.law t) f).symm
  · linarith
  · exact (le_abs_self _).trans hB

end AcceleratedLogConcave.Kinetic
