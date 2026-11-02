import DirectW12.PhysicalEndpoints
import DirectW12.CoupledPairingAssembly

/-!

-/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function Filter
open scoped Topology NNReal RealInnerProductSpace
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic.DirectW12
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ}

theorem physicalReferenceGradient_continuous (P : ReferencePoissonFamily E a b)
    (g : Lp ℝ 2 (P.law a)) : Continuous (physicalReferenceGradient P g) := by
  exact (P.physicalGradientPullback_continuous g).comp continuous_projIcc


/-- Compact continuous tests admit a global bound. -/
private theorem compact_test_bound {X : Type*} [TopologicalSpace X]
    {φ : X → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C := by
  obtain ⟨C,hC⟩ := hc.isCompact.exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport φ
  · exact (hC x hx).trans (le_max_left _ _)
  · have hz : φ x = 0 := by
      by_contra hz
      exact hx (subset_tsupport φ (Function.mem_support.mpr hz))
    rw [hz, norm_zero]
    exact le_max_right _ _

/-- Strong continuity of the actual moving tests uses their genuine jointly
continuous representative and its inherited bounded range. -/
theorem physicalMovingCoreLp_continuous (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (T : Icc a b) {φ : CoupledPhase E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Continuous (physicalMovingCoreLp P ell T hφ hc) := by
  have hjoint : Continuous (physicalMovingCore P ell T φ) := by
    unfold physicalMovingCore
    exact movingFrameCore_continuous _ _ _ _ _ _ hφ
  obtain ⟨C,hC⟩ := compact_test_bound hφ hc
  have hb (s : ℝ) (x : CoupledPhase E) :
      ‖physicalMovingCore P ell T φ (s,x)‖ ≤ C := by
    exact hC _
  apply continuous_iff_continuousAt.mpr
  intro t
  exact tendsto_L2_of_dominated_core_representatives
    (physicalMovingCoreLp P ell T hφ hc) (physicalMovingCoreLp P ell T hφ hc t)
    (fun s x => physicalMovingCore P ell T φ (s,x))
    (fun x => physicalMovingCore P ell T φ (t,x))
    (physicalMovingCoreLp_coe P ell T hφ hc)
    (physicalMovingCoreLp_coe P ell T hφ hc t)
    (fun _ => 2*C) (integrable_const _)
    (Eventually.of_forall fun s => Eventually.of_forall fun x =>
      (norm_sub_le _ _).trans (by linarith [hb s x, hb t x]))
    (Eventually.of_forall fun x =>
      (hjoint.comp (continuous_id.prodMk continuous_const)).continuousAt)

/-- The exact coordinate expression for the physical coupled scalar path. -/
theorem physicalCoupledPairing_eq_coordinates (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (g : Lp ℝ 2 (P.law a)) (ψ : E × E → E)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (u : ℝ) (hu : u ∈ Icc a b) :
    physicalCoupledPairing P ell g ψ u =
      ∑ i, inner ℝ
        (physicalCoordinate P ((stdOrthonormalBasis ℝ E) i)
          (physicalReferenceGradient P g u))
        (physicalMovingCoreLp P ell P.leftTime
          (coordinatePairTest_contDiff ((stdOrthonormalBasis ℝ E) i) hψ).continuous
          (coordinatePairTest_compact ((stdOrthonormalBasis ℝ E) i) hc) u) := by
  let r : Icc a b := ⟨u,hu⟩
  have hrep : physicalReferenceGradient P g u = P.unitary r (physicalGradient P g r) := by
    unfold physicalReferenceGradient
    rw [projIcc_of_mem P.ordered hu]
  rw [hrep, coordinate_pairing_current_eq P r (physicalGradient P g r) _
    (coupledMovingVectorTest P ell r ψ)
    (fun i => physical_coordinate_test_coe P ell r ((stdOrthonormalBasis ℝ E) i) ψ hψ hc)]
  unfold physicalCoupledPairing
  rw [projIcc_of_mem P.ordered hu]
  exact coupled_pairing_changeVariables P ell r (fun z => physicalGradient P g r z.1) ψ

/-- Closed-endpoint continuity, with the PHYSICAL inverse at both endpoints. -/
theorem physicalCoupledPairing_continuousOn (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (g : Lp ℝ 2 (P.law a)) (ψ : E × E → E)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    ContinuousOn (physicalCoupledPairing P ell g ψ) (Icc a b) := by
  have hcont : Continuous (fun u => ∑ i, inner ℝ
      (physicalCoordinate P ((stdOrthonormalBasis ℝ E) i) (physicalReferenceGradient P g u))
      (physicalMovingCoreLp P ell P.leftTime
        (coordinatePairTest_contDiff ((stdOrthonormalBasis ℝ E) i) hψ).continuous
        (coordinatePairTest_compact ((stdOrthonormalBasis ℝ E) i) hc) u)) := by
    apply continuous_finsetSum
    intro i _
    exact ((physicalCoordinate P ((stdOrthonormalBasis ℝ E) i)).continuous.comp
      (physicalReferenceGradient_continuous P g)).inner
      (physicalMovingCoreLp_continuous P ell P.leftTime
        (coordinatePairTest_contDiff ((stdOrthonormalBasis ℝ E) i) hψ).continuous
        (coordinatePairTest_compact ((stdOrthonormalBasis ℝ E) i) hc))
  exact hcont.continuousOn.congr
    (fun u hu => physicalCoupledPairing_eq_coordinates P ell g ψ hψ hc u hu)

/-- Vector test as an actual L² class in the initial phase measure. -/
def pairTestLp (P : ReferencePoissonFamily E a b) (ψ : E × E → E)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Lp E 2 ((P.law a).prod (stdGaussian E)) :=
  (hψ.memLp_of_hasCompactSupport hc).toLp ψ

/-- Actual coupled pullback of a current phase-space vector. -/
def coupledPullback (P : ReferencePoissonFamily E a b) (ell : ℝ) (t : Icc a b) :
    Lp E 2 ((P.law t).prod (stdGaussian E)) →ₗᵢ[ℝ]
      Lp E 2 ((P.law a).prod (stdGaussian E)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (referenceCoupledPairFlow P ell t)
    (referenceCoupledPairFlow_measurePreserving P ell t)

/-- Cauchy--Schwarz after the ACTUAL coupled pullback, whose norm is preserved. -/
theorem abs_coupled_integral_le (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (t : Icc a b) (v : Lp E 2 ((P.law t).prod (stdGaussian E)))
    (ψ : E × E → E) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    |∫ z, inner ℝ (v (referenceCoupledPairFlow P ell t z)) (ψ z)
      ∂(P.law a).prod (stdGaussian E)| ≤ ‖v‖ * ‖pairTestLp P ψ hψ hc‖ := by
  have he : (∫ z, inner ℝ (v (referenceCoupledPairFlow P ell t z)) (ψ z)
      ∂(P.law a).prod (stdGaussian E)) =
      inner ℝ (coupledPullback P ell t v) (pairTestLp P ψ hψ hc) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving v
      (referenceCoupledPairFlow_measurePreserving P ell t),
      (hψ.memLp_of_hasCompactSupport hc).coeFn_toLp] with z hv htest
    change coupledPullback P ell t v z = v (referenceCoupledPairFlow P ell t z) at hv
    change pairTestLp P ψ hψ hc z = ψ z at htest
    rw [hv, htest]
  rw [he]
  simpa only [(coupledPullback P ell t).norm_map] using abs_real_inner_le_norm
    (coupledPullback P ell t v) (pairTestLp P ψ hψ hc)

/-- The actual material term has its sharp source bound. -/
theorem abs_material_integral_le (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (g : Lp ℝ 2 (P.law a)) (t : ℝ) (ht : t ∈ Ioo a b)
    (ψ : E × E → E) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    |∫ z, inner ℝ (physicalMaterial P g t ht
        (referenceCoupledPairFlow P ell ⟨t,ht.1.le,ht.2.le⟩ z).1) (ψ z)
      ∂(P.law a).prod (stdGaussian E)| ≤
      |P.scale t| * ‖g‖ * ‖pairTestLp P ψ hψ hc‖ := by
  let s : Icc a b := ⟨t,ht.1.le,ht.2.le⟩
  let m := physicalMaterial P g t ht
  let v : Lp E 2 ((P.law t).prod (stdGaussian E)) :=
    Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst m
  have he : (∫ z, inner ℝ (m (referenceCoupledPairFlow P ell s z).1) (ψ z)
      ∂(P.law a).prod (stdGaussian E)) =
      ∫ z, inner ℝ (v (referenceCoupledPairFlow P ell s z)) (ψ z)
        ∂(P.law a).prod (stdGaussian E) := by
    apply integral_congr_ae
    filter_upwards [(referenceCoupledPairFlow_measurePreserving P ell s).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving m measurePreserving_fst)] with z hz
    change v (referenceCoupledPairFlow P ell s z) =
      m (referenceCoupledPairFlow P ell s z).1 at hz
    rw [hz]
  rw [he]
  have hm : ‖v‖ ≤ |P.scale t| * ‖g‖ := by
    change ‖Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst m‖ ≤ _
    rw [LinearIsometry.norm_map]
    change ‖(P.unitary s).symm (P.materialOperator t ht g)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact (P.materialOperator t ht).le_of_opNorm_le (P.materialOperator_norm_le t ht) g
  exact (abs_coupled_integral_le P ell s v ψ hψ hc).trans
    (mul_le_mul_of_nonneg_right hm (norm_nonneg _))

/-- No row selection over time is needed: the derivative is unique, and at each
one time its actual rows give the sharp bound. -/
theorem physicalCoupledPairing_deriv_bound (P : ReferencePoissonFamily E a b)
    {ell : ℝ} (hell : 0 ≤ ell) (g : Lp ℝ 2 (P.law a))
    (ψ : E × E → E) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    |deriv (physicalCoupledPairing P ell g ψ) t| ≤
      (ell + |P.scale t|) * ‖g‖ * ‖pairTestLp P ψ hψ.continuous hc‖ := by
  obtain ⟨rows, _, hb, hd⟩ :=
    physical_poisson_gradient_coupled_pairing_hasDerivAt P ell g ψ hψ hc t ht
  have hrows : ‖gaussianHessianVector (P.law t) rows‖ ≤ ‖g‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hb
  have hH := (abs_coupled_integral_le P ell ⟨t,ht.1.le,ht.2.le⟩
    (gaussianHessianVector (P.law t) rows) ψ hψ.continuous hc).trans
      (mul_le_mul_of_nonneg_right hrows (norm_nonneg _))
  have hm := abs_material_integral_le P ell g t ht ψ hψ.continuous hc
  rw [hd.deriv]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ |P.scale t| * ‖g‖ * ‖pairTestLp P ψ hψ.continuous hc‖ +
        ell * (‖g‖ * ‖pairTestLp P ψ hψ.continuous hc‖) := by
      rw [abs_mul, abs_of_nonneg hell]
      exact add_le_add hm (mul_le_mul_of_nonneg_left hH hell)
    _ = _ := by ring

/-- Closed-clock physical scalar increment. All continuity and differentiability
inputs are the named physical constructions above, not theorem hypotheses. -/
theorem physicalCoupledPairing_increment_le (P : ReferencePoissonFamily E a b)
    {ell A u R : ℝ} (hell : 0 ≤ ell) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (huR : u ≤ R) (huI : u ∈ Icc a b) (hRI : R ∈ Icc a b)
    (hscale : ∀ r ∈ Ioo u R, P.scale r = A*r)
    (g : Lp ℝ 2 (P.law a)) (ψ : E × E → E)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    |physicalCoupledPairing P ell g ψ R - physicalCoupledPairing P ell g ψ u| ≤
      (ell*(R-u) + A*(R^2-u^2)/2) * ‖g‖ * ‖pairTestLp P ψ hψ.continuous hc‖ := by
  let F := physicalCoupledPairing P ell g ψ
  have hmem (r : ℝ) (hr : r ∈ Ioo u R) : r ∈ Ioo a b :=
    ⟨huI.1.trans_lt hr.1, hr.2.trans_le hRI.2⟩
  have hd (r : ℝ) (hr : r ∈ Ioo u R) : HasDerivAt F (deriv F r) r := by
    obtain ⟨rows, _, _, hd⟩ :=
      physical_poisson_gradient_coupled_pairing_hasDerivAt P ell g ψ hψ hc r (hmem r hr)
    exact hd.differentiableAt.hasDerivAt
  have hb (r : ℝ) (hr : r ∈ Ioo u R) :
      |deriv F r| ≤ (ell+A*r) * ‖g‖ * ‖pairTestLp P ψ hψ.continuous hc‖ := by
    have h := physicalCoupledPairing_deriv_bound P hell g ψ hψ hc r (hmem r hr)
    rw [hscale r hr, abs_of_nonneg (mul_nonneg hA (hu.trans hr.1.le))] at h
    exact h
  -- Apply the already compiled dense scalar/Hilbert integration theorem with H=ℝ.
  have hi := dense_pairing_increment_le_affine F univ dense_univ
    (fun r z => deriv F r * z) hell hA
    (mul_nonneg (norm_nonneg g) (norm_nonneg (pairTestLp P ψ hψ.continuous hc))) hu huR
    (fun z _ => by
      have hf := (physicalCoupledPairing_continuousOn P ell g ψ hψ hc).mono
        (show Icc u R ⊆ Icc a b from fun r hr =>
          ⟨huI.1.trans hr.1, hr.2.trans hRI.2⟩)
      simpa only [RCLike.inner_apply, conj_trivial] using
        hf.const_mul z)
    (fun z _ r hr => by
      simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using (hd r hr).mul_const z)
    (fun z _ r hr => by
      simpa only [abs_mul, Real.norm_eq_abs, mul_assoc] using
        mul_le_mul_of_nonneg_right (hb r hr) (abs_nonneg z))
  simpa only [Real.norm_eq_abs, mul_assoc] using hi

end AcceleratedLogConcave.Kinetic.DirectW12
