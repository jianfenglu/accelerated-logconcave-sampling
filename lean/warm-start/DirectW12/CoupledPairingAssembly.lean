import DirectW12.MovingTestCancellation

/-!

-/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function Filter
open scoped Topology NNReal RealInnerProductSpace
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic.DirectW12
open Analysis.Poisson Analysis.WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ}

abbrev phaseToPair : CoupledPhase E ≃L[ℝ] E × E :=
  WithLp.prodContinuousLinearEquiv 2 ℝ E E

/-- Ordinary-pair tests are converted by the actual linear phase equivalence. -/
def pairTestLift (ψ : E × E → E) : CoupledPhase E → E := ψ ∘ phaseToPair

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem pairTestLift_contDiff {ψ : E × E → E} (hψ : ContDiff ℝ 1 ψ) :
    ContDiff ℝ 1 (pairTestLift ψ) := hψ.comp (phaseToPair (E := E)).contDiff

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem pairTestLift_compact {ψ : E × E → E} (hc : HasCompactSupport ψ) :
    HasCompactSupport (pairTestLift ψ) := hc.comp_homeomorph phaseToPair.toHomeomorph

def coordinatePairTest (e : E) (ψ : E × E → E) : CoupledPhase E → ℝ :=
  fun z => inner ℝ e (pairTestLift ψ z)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem coordinatePairTest_contDiff (e : E) {ψ : E × E → E}
    (hψ : ContDiff ℝ 1 ψ) : ContDiff ℝ 1 (coordinatePairTest e ψ) :=
  (innerSL ℝ e).contDiff.comp (pairTestLift_contDiff hψ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem coordinatePairTest_compact (e : E) {ψ : E × E → E}
    (hc : HasCompactSupport ψ) : HasCompactSupport (coordinatePairTest e ψ) :=
  (pairTestLift_compact hc).comp_left (show (innerSL ℝ e) 0 = 0 by simp)

theorem physicalMovingCoreLp_coe (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (T : Icc a b) {φ : CoupledPhase E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (s : ℝ) :
    physicalMovingCoreLp P ell T hφ hc s =ᵐ[coupledPhaseMeasure (P.law a)]
      fun z => physicalMovingCore P ell T φ (s,z) := by
  unfold physicalMovingCoreLp movingFrameCoreLp physicalMovingCore
  exact MemLp.coeFn_toLp _

theorem physicalMovingCoreDerivativeLp_coe (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (T : Icc a b) {φ : CoupledPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    physicalMovingCoreDerivativeLp P ell T hφ hc t ht
      =ᵐ[coupledPhaseMeasure (P.law a)]
        fun z => fderiv ℝ (physicalMovingCore P ell T φ) (t,z) (1,0) := by
  unfold physicalMovingCoreDerivativeLp physicalMovingCore
  exact MemLp.coeFn_toLp _

/-- The coordinate sum is an integral of the vector inner product. Its
integrability is proved from the actual coordinate L² classes, not assumed. -/
theorem finite_coordinate_pairing_eq (P : ReferencePoissonFamily E a b)
    (u : Lp E 2 (P.law a))
    (q : Fin (Module.finrank ℝ E) → Lp ℝ 2 (coupledPhaseMeasure (P.law a)))
    (w : CoupledPhase E → E)
    (hq : ∀ i, q i =ᵐ[coupledPhaseMeasure (P.law a)]
      fun z => inner ℝ ((stdOrthonormalBasis ℝ E) i) (w z)) :
    (∑ i, inner ℝ (physicalCoordinate P ((stdOrthonormalBasis ℝ E) i) u) (q i)) =
      ∫ z, inner ℝ (u z.fst) (w z) ∂coupledPhaseMeasure (P.law a) := by
  let B := stdOrthonormalBasis ℝ E
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun z => inner ℝ
        (physicalCoordinate P (B i) u z) (q i z)) (coupledPhaseMeasure (P.law a)) :=
    L2.integrable_inner _ _
  simp only [L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  have ha := ae_all_iff.mpr (fun i => physicalCoordinate_coe P (B i) u)
  have hb := ae_all_iff.mpr hq
  filter_upwards [ha,hb] with z hz hqz
  simp only [hz, hqz, RCLike.inner_apply, conj_trivial]
  calc
    _ = ∑ i, inner ℝ (u z.fst) (B i) * inner ℝ (B i) (w z) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm (u z.fst) (B i)]
      ring
    _ = _ := B.sum_inner_mul_inner (u z.fst) (w z)

/-- Exact reference-frame change of variables, including the WithLp map. -/
theorem phase_reference_integral (P : ReferencePoissonFamily E a b)
    (t : Icc a b) (F : E × E → ℝ) :
    (∫ z : CoupledPhase E, F (phaseToPair (referenceCoupledFlow P 0 t z))
      ∂coupledPhaseMeasure (P.law a)) =
      ∫ z, F z ∂(P.law t).prod (stdGaussian E) := by
  rw [(referenceCoupledFlow_measurePreserving P 0 t).integral_comp
    (referenceCoupledFlow P 0 t).toMeasurableEquiv.measurableEmbedding
    (fun z : CoupledPhase E => F (phaseToPair z))]
  let hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (E × E))
      ((P.law t).prod (stdGaussian E)) (coupledPhaseMeasure (P.law t)) :=
    ⟨(MeasurableEquiv.toLp 2 (E × E)).measurable, rfl⟩
  exact hmp.symm.integral_comp
    (MeasurableEquiv.toLp 2 (E × E)).symm.measurableEmbedding F

/-- Reconstruction after pulling the genuine current-law vector into the
fixed Hilbert space. The a.e. sets may depend on this one fixed time. -/
theorem coordinate_pairing_current_eq (P : ReferencePoissonFamily E a b)
    (t : Icc a b) (v : Lp E 2 (P.law t))
    (q : Fin (Module.finrank ℝ E) → Lp ℝ 2 (coupledPhaseMeasure (P.law a)))
    (w : E × E → E)
    (hq : ∀ i, q i =ᵐ[coupledPhaseMeasure (P.law a)]
      fun z => inner ℝ ((stdOrthonormalBasis ℝ E) i)
        (w (phaseToPair (referenceCoupledFlow P 0 t z)))) :
    (∑ i, inner ℝ
      (physicalCoordinate P ((stdOrthonormalBasis ℝ E) i) (P.unitary t v)) (q i)) =
    ∫ z, inner ℝ (v z.1) (w z) ∂(P.law t).prod (stdGaussian E) := by
  rw [finite_coordinate_pairing_eq P _ q _ hq]
  have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (E × E))
      ((P.law a).prod (stdGaussian E)) (coupledPhaseMeasure (P.law a)) :=
    ⟨(MeasurableEquiv.toLp 2 (E × E)).measurable, rfl⟩
  have hv := hmp.symm.quasiMeasurePreserving.ae
    (measurePreserving_fst.quasiMeasurePreserving.ae
      (pullback_coeFn (P.flow t).toMeasurableEquiv (P.flow_measurePreserving t) v))
  calc
    _ = ∫ z : CoupledPhase E,
        inner ℝ (v (phaseToPair (referenceCoupledFlow P 0 t z)).1)
          (w (phaseToPair (referenceCoupledFlow P 0 t z)))
        ∂coupledPhaseMeasure (P.law a) := by
      apply integral_congr_ae
      filter_upwards [hv] with z hz
      rw [referenceCoupledFlow_zero_apply]
      exact congrArg (fun x => inner ℝ x (w (P.flow t z.fst, z.snd))) hz
    _ = _ := phase_reference_integral P t (fun z => inner ℝ (v z.1) (w z))

/-- Value-level conjugacy of ordinary-pair and Hilbert phase flows. -/
theorem inverse_phase_pair_conjugacy (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (t : Icc a b) (z : CoupledPhase E) :
    phaseToPair ((referenceCoupledFlow P ell t).symm z) =
      (referenceCoupledPairFlow P ell t).symm (phaseToPair z) := rfl

theorem physical_coordinate_test_coe (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (t : Icc a b) (e : E) (ψ : E × E → E)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    physicalMovingCoreLp P ell P.leftTime
      (coordinatePairTest_contDiff e hψ).continuous (coordinatePairTest_compact e hc) t
      =ᵐ[coupledPhaseMeasure (P.law a)] fun z =>
        inner ℝ e (coupledMovingVectorTest P ell t ψ
          (phaseToPair (referenceCoupledFlow P 0 t z))) := by
  filter_upwards [physicalMovingCoreLp_coe P ell P.leftTime
    (coordinatePairTest_contDiff e hψ).continuous (coordinatePairTest_compact e hc) t]
      with z hz
  rw [hz, physicalMovingCore_leftTime_eq]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Spatial derivative chain rule through the ordinary-pair conjugacy.
This is the derivative-level bridge, not just a value-level identification. -/
theorem pair_coordinate_fderiv (e : E) (Ψ : E × E → E)
    (hΨ : ContDiff ℝ 1 Ψ) (z w : CoupledPhase E) :
    fderiv ℝ (fun y => inner ℝ e (Ψ (phaseToPair y))) z w =
      inner ℝ e (fderiv ℝ Ψ (phaseToPair z) (phaseToPair w)) := by
  have hd := (innerSL ℝ e).hasFDerivAt.comp z
    (((hΨ.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp z
      phaseToPair.toContinuousLinearMap.hasFDerivAt)
  change HasFDerivAt (fun y => inner ℝ e (Ψ (phaseToPair y))) _ z at hd
  exact congrArg (fun L : CoupledPhase E →L[ℝ] ℝ => L w) hd.fderiv

theorem physical_coordinate_derivative_eq (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (e : E) (ψ : E × E → E) (hψ : ContDiff ℝ 1 ψ)
    (t : ℝ) (ht : t ∈ Ioo a b) (x : CoupledPhase E) :
    let s : Icc a b := ⟨t,ht.1.le,ht.2.le⟩
    let z := phaseToPair (referenceCoupledFlow P 0 s x)
    fderiv ℝ (physicalMovingCore P ell P.leftTime (coordinatePairTest e ψ))
      (t,x) (1,0) =
      inner ℝ e ((-ell) • fderiv ℝ (coupledMovingVectorTest P ell s ψ) z
        (z.2, -gradient (P.potential t) z.1)) := by
  dsimp only
  rw [physicalMovingCore_derivative_eq P ell P.leftTime
    (coordinatePairTest_contDiff e hψ) t ht x]
  simp only [backwardTest_eq, spaceTimeForward,
    projIcc_of_mem P.ordered (show t ∈ Icc a b from ⟨ht.1.le,ht.2.le⟩)]
  change (-ell) * fderiv ℝ
    (fun y => inner ℝ e (coupledMovingVectorTest P ell ⟨t,ht.1.le,ht.2.le⟩ ψ
      (phaseToPair y))) (referenceCoupledFlow P 0 ⟨t,ht.1.le,ht.2.le⟩ x)
      (WithLp.toLp 2
        ((referenceCoupledFlow P 0 ⟨t,ht.1.le,ht.2.le⟩ x).snd,
         -gradient (P.potential t)
           (referenceCoupledFlow P 0 ⟨t,ht.1.le,ht.2.le⟩ x).fst)) = _
  rw [pair_coordinate_fderiv e _ (coupledMovingVectorTest_contDiff P ell _ hψ)]
  simp only [inner_smul_right]
  rfl

theorem physical_coordinate_derivative_coe (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (e : E) (ψ : E × E → E)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    let s : Icc a b := ⟨t,ht.1.le,ht.2.le⟩
    physicalMovingCoreDerivativeLp P ell P.leftTime
      (coordinatePairTest_contDiff e hψ) (coordinatePairTest_compact e hc) t ht
      =ᵐ[coupledPhaseMeasure (P.law a)] fun x =>
        let z := phaseToPair (referenceCoupledFlow P 0 s x)
        inner ℝ e ((-ell) • fderiv ℝ (coupledMovingVectorTest P ell s ψ) z
          (z.2, -gradient (P.potential t) z.1)) := by
  filter_upwards [physicalMovingCoreDerivativeLp_coe P ell P.leftTime
    (coordinatePairTest_contDiff e hψ) (coordinatePairTest_compact e hc) t ht] with x hx
  exact hx.trans (physical_coordinate_derivative_eq P ell e ψ hψ t ht x)

/-- The genuine physical scalar path, including unchanged physical endpoint
values. Projection only extends its domain; differentiation is interior. -/
def physicalCoupledPairing (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (g : Lp ℝ 2 (P.law a)) (ψ : E × E → E) (u : ℝ) : ℝ :=
  let s := projIcc a b P.ordered u
  ∫ z, inner ℝ (physicalGradient P g s (referenceCoupledPairFlow P ell s z).1)
    (ψ z) ∂(P.law a).prod (stdGaussian E)

/-- Material derivative in the current law; it is not the initial-law
representative evaluated at a coupled physical position. -/
def physicalMaterial (P : ReferencePoissonFamily E a b)
    (g : Lp ℝ 2 (P.law a)) (t : ℝ) (ht : t ∈ Ioo a b) :
    Lp E 2 (P.law t) :=
  (P.unitary ⟨t,ht.1.le,ht.2.le⟩).symm (P.materialOperator t ht g)

/-- Final physical pairing derivative. Rows are actual closed gradients of
physical Poisson coordinates, and retain the sharp inverse energy bound.
The two terms are deliberately displayed as separate integrals so the
material and Hamiltonian contributions remain auditable. -/
theorem physical_poisson_gradient_coupled_pairing_hasDerivAt
    (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (g : Lp ℝ 2 (P.law a)) (ψ : E × E → E)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    let s : Icc a b := ⟨t,ht.1.le,ht.2.le⟩
    ∃ rows : Fin (Module.finrank ℝ E) → Lp E 2 (P.law t),
      (∀ i, ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).compLp
        (physicalGradient P g s), rows i) ∈
        (closedGradient (P.law t) (P.potential t)
          ((P.potential_C2 t).of_le (by norm_num))
          (P.integrable t s.property) (P.gibbs_law t s.property)).graph) ∧
      ‖gaussianHessianVector (P.law t) rows‖ ^ 2 ≤ ‖g‖ ^ 2 ∧
      HasDerivAt (physicalCoupledPairing P ell g ψ)
        ((∫ z, inner ℝ (physicalMaterial P g t ht
            (referenceCoupledPairFlow P ell s z).1) (ψ z)
          ∂(P.law a).prod (stdGaussian E)) +
         ell * (∫ z, inner ℝ
            (gaussianHessianVector (P.law t) rows (referenceCoupledPairFlow P ell s z))
            (ψ z) ∂(P.law a).prod (stdGaussian E))) t := by
  let s : Icc a b := ⟨t,ht.1.le,ht.2.le⟩
  let B := stdOrthonormalBasis ℝ E
  let hφ := fun i => coordinatePairTest_contDiff (B i) hψ
  let hcφ := fun i => coordinatePairTest_compact (B i) hc
  let q := fun u i => physicalMovingCoreLp P ell P.leftTime (hφ i).continuous (hcφ i) u
  let dq := fun i => physicalMovingCoreDerivativeLp P ell P.leftTime (hφ i) (hcφ i) t ht
  let Ψ := coupledMovingVectorTest P ell s ψ
  let v := physicalGradient P g s
  let m := physicalMaterial P g t ht
  obtain ⟨rows,hrows,hbound,hH,hG,hcancel⟩ :=
    physicalGradient_moving_test_cancellation P ell g s ψ hψ hc
  refine ⟨rows,hrows,hbound,?_⟩
  have hpath (u : ℝ) (hu : u ∈ Icc a b) :
      (∑ i, inner ℝ (physicalCoordinate P (B i) (physicalReferenceGradient P g u))
        (q u i)) = physicalCoupledPairing P ell g ψ u := by
    let r : Icc a b := ⟨u,hu⟩
    have hrep : physicalReferenceGradient P g u = P.unitary r (physicalGradient P g r) := by
      unfold physicalReferenceGradient
      rw [projIcc_of_mem P.ordered hu]
    rw [hrep, coordinate_pairing_current_eq P r (physicalGradient P g r) (q u)
      (coupledMovingVectorTest P ell r ψ)
      (fun i => physical_coordinate_test_coe P ell r (B i) ψ hψ hc)]
    unfold physicalCoupledPairing
    rw [projIcc_of_mem P.ordered hu]
    exact (coupled_pairing_changeVariables P ell r
      (fun z => physicalGradient P g r z.1) ψ).symm
  have hmaterial :
      (∑ i, inner ℝ (physicalCoordinate P (B i) (P.materialOperator t ht g)) (q t i)) =
      ∫ z, inner ℝ (m (referenceCoupledPairFlow P ell s z).1) (ψ z)
        ∂(P.law a).prod (stdGaussian E) := by
    have hm : P.materialOperator t ht g = P.unitary s m := by
      exact (P.unitary s).apply_symm_apply _ |>.symm
    rw [hm, coordinate_pairing_current_eq P s m (q t) Ψ
      (fun i => physical_coordinate_test_coe P ell s (B i) ψ hψ hc)]
    exact (coupled_pairing_changeVariables P ell s (fun z => m z.1) ψ).symm
  have htransport :
      (∑ i, inner ℝ (physicalCoordinate P (B i) (physicalReferenceGradient P g t))
        (dq i)) = ell * (∫ z, inner ℝ
          (gaussianHessianVector (P.law t) rows (referenceCoupledPairFlow P ell s z))
          (ψ z) ∂(P.law a).prod (stdGaussian E)) := by
    have hv : physicalReferenceGradient P g t = P.unitary s v := by
      unfold physicalReferenceGradient
      rw [projIcc_of_mem P.ordered s.property]
    rw [hv, coordinate_pairing_current_eq P s v dq
      (fun z => (-ell) • fderiv ℝ Ψ z (z.2, -gradient (P.potential t) z.1))
      (fun i => physical_coordinate_derivative_coe P ell (B i) ψ hψ hc t ht)]
    simp only [inner_smul_right]
    rw [integral_const_mul, hcancel,
      ← coupled_pairing_changeVariables P ell s (gaussianHessianVector (P.law t) rows) ψ]
    ring
  have hd := physical_vector_moving_pairing_hasDerivAt P ell g P.leftTime
    (pairTestLift ψ) (pairTestLift_contDiff hψ) (pairTestLift_compact hc) t ht
  change HasDerivAt
    (fun u => ∑ i, inner ℝ
      (physicalCoordinate P (B i) (physicalReferenceGradient P g u)) (q u i))
    (∑ i, (inner ℝ
      (physicalCoordinate P (B i) (physicalReferenceGradient P g t)) (dq i) +
      inner ℝ (physicalCoordinate P (B i) (P.materialOperator t ht g)) (q t i))) t at hd
  rw [Finset.sum_add_distrib, htransport, hmaterial, add_comm] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
  exact (hpath u ⟨hu.1.le,hu.2.le⟩).symm

end AcceleratedLogConcave.Kinetic.DirectW12
