import AcceleratedLogConcave.Kinetic.ReferenceFlow
import AcceleratedLogConcave.Kinetic.ReferenceFlow.MovingFrameCore
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!

-/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function Filter
open scoped Topology NNReal RealInnerProductSpace
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic.DirectW12
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ}

/-- The genuine physical inverse, including at the endpoints. -/
def physicalGradient (P : ReferencePoissonFamily E a b)
    (g : Lp ℝ 2 (P.law a)) (s : Icc a b) : Lp E 2 (P.law s) :=
  gradientPoissonInverse (P.law s) (P.potential s) (P.potential_C2 s)
    (P.integrable s s.property) (P.gibbs_law s s.property)
    (P.lower s) 1 (P.lower_pos s s.property)
    (P.hessian_lower s s.property)
    (by simpa only [one_mul] using P.hessian_upper s s.property)
    ((P.unitary s).symm g)

/-- A globally defined path of *physical* inverses on the reference Hilbert
space. Projection is only a domain extension; no endpoint theorem follows. -/
def physicalReferenceGradient (P : ReferencePoissonFamily E a b)
    (g : Lp ℝ 2 (P.law a)) (s : ℝ) : Lp E 2 (P.law a) :=
  P.unitary (projIcc a b P.ordered s)
    (physicalGradient P g (projIcc a b P.ordered s))

theorem physicalReferenceGradient_eventuallyEq
    (P : ReferencePoissonFamily E a b) (g : Lp ℝ 2 (P.law a))
    (t : ℝ) (ht : t ∈ Ioo a b) :
    physicalReferenceGradient P g =ᶠ[𝓝 t] fun s => P.gradientInverse s g := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  unfold physicalReferenceGradient
  rw [projIcc_of_mem P.ordered ⟨hs.1.le, hs.2.le⟩]
  exact (P.gradientInverse_eq_physical s hs g).symm

theorem physicalReferenceGradient_hasDerivAt
    (P : ReferencePoissonFamily E a b) (g : Lp ℝ 2 (P.law a))
    (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (physicalReferenceGradient P g) (P.materialOperator t ht g) t :=
  (P.gradientInverse_hasDerivAt t ht g).congr_of_eventuallyEq
    (physicalReferenceGradient_eventuallyEq P g t ht)

/-- Fixed position embedding into the genuine Hilbert phase measure. -/
def phasePositionEmbedding (μ : Measure E) [IsProbabilityMeasure μ] :
    Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (coupledPhaseMeasure μ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (MeasurableEquiv.toLp 2 (E × E)).symm
    (MeasurePreserving.symm (MeasurableEquiv.toLp 2 (E × E))
      (show MeasurePreserving (MeasurableEquiv.toLp 2 (E × E))
        (μ.prod (stdGaussian E)) (coupledPhaseMeasure μ) from
        ⟨(MeasurableEquiv.toLp 2 (E × E)).measurable, rfl⟩))).comp
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst)

omit [BorelSpace E] in
theorem phasePositionEmbedding_coe (μ : Measure E) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) :
    phasePositionEmbedding μ f =ᵐ[coupledPhaseMeasure μ]
      fun z : CoupledPhase E => f z.fst := by
  let hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (E × E))
      (μ.prod (stdGaussian E)) (coupledPhaseMeasure μ) :=
    ⟨(MeasurableEquiv.toLp 2 (E × E)).measurable, rfl⟩
  exact (Lp.coeFn_compMeasurePreserving
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst f) hmp.symm).trans
      (hmp.symm.quasiMeasurePreserving.ae
        (Lp.coeFn_compMeasurePreserving f measurePreserving_fst))

/-- A coordinate of the actual vector inverse in the fixed source phase L². -/
def physicalCoordinate (P : ReferencePoissonFamily E a b) (e : E) :
    Lp E 2 (P.law a) →L[ℝ] Lp ℝ 2 (coupledPhaseMeasure (P.law a)) :=
  (phasePositionEmbedding (P.law a)).toContinuousLinearMap.comp
    ((innerSL ℝ e).compLpL 2 (P.law a))

theorem physicalCoordinate_coe (P : ReferencePoissonFamily E a b)
    (e : E) (f : Lp E 2 (P.law a)) :
    physicalCoordinate P e f =ᵐ[coupledPhaseMeasure (P.law a)]
      fun z : CoupledPhase E => inner ℝ e (f z.fst) := by
  let hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (E × E))
      ((P.law a).prod (stdGaussian E)) (coupledPhaseMeasure (P.law a)) :=
    ⟨(MeasurableEquiv.toLp 2 (E × E)).measurable, rfl⟩
  exact (phasePositionEmbedding_coe (P.law a) ((innerSL ℝ e).compLp f)).trans
    (hmp.symm.quasiMeasurePreserving.ae
      (measurePreserving_fst.quasiMeasurePreserving.ae
        ((innerSL ℝ e).coeFn_compLp f)))

private theorem driftContinuous (P : ReferencePoissonFamily E a b) (ell : ℝ) :
    Continuous (uncurry (coupledDrift P.potential ell P.scale)) :=
  coupledDrift_continuous P.potential ell P.scale P.gradient_continuous P.scale_continuous

private theorem driftLipschitz (P : ReferencePoissonFamily E a b) (ell : ℝ) :
    ∀ t ∈ Icc a b, LipschitzWith (2 * ‖ell‖₊ + P.scaleBound)
      (coupledDrift P.potential ell P.scale t) :=
  fun t ht => coupledDrift_lipschitz P.potential ell P.scale t (P.potential_C2 t)
    (P.hessian_nonneg t ht) (P.hessian_upper t ht) P.scaleBound (P.scale_bounded t ht)

private theorem driftDerivativeContinuous (P : ReferencePoissonFamily E a b) (ell : ℝ) :
    Continuous (uncurry (coupledDriftDerivative P.potential ell P.scale)) :=
  coupledDriftDerivative_continuous P.potential ell P.scale
    P.hessian_continuous P.scale_continuous

private theorem driftHasFDerivAt (P : ReferencePoissonFamily E a b) (ell : ℝ) :
    ∀ t z, HasFDerivAt (coupledDrift P.potential ell P.scale t)
      (coupledDriftDerivative P.potential ell P.scale t z) z :=
  fun t z => coupledDrift_hasFDerivAt P.potential ell P.scale t z (P.potential_C2 t)

/-- The actual ell-flow backward test observed in the actual zero-ell flow.
Both flows are constructed, not supplied as an assumption. T can be a. -/
def physicalMovingCore (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (T : Icc a b) (φ : CoupledPhase E → ℝ) (p : ℝ × CoupledPhase E) : ℝ :=
  movingFrameCore P.ordered (driftContinuous P ell) (driftContinuous P 0)
    (driftLipschitz P ell) (driftLipschitz P 0) T φ p

def physicalMovingCoreLp (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (T : Icc a b) {φ : CoupledPhase E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (s : ℝ) :
    Lp ℝ 2 (coupledPhaseMeasure (P.law a)) :=
  movingFrameCoreLp P.ordered (driftContinuous P ell) (driftContinuous P 0)
    (driftLipschitz P ell) (driftLipschitz P 0)
    (coupledPhaseMeasure (P.law a)) T hφ hc s

def physicalMovingCoreDerivativeLp (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (T : Icc a b) {φ : CoupledPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (t : ℝ) (ht : t ∈ Ioo a b) : Lp ℝ 2 (coupledPhaseMeasure (P.law a)) :=
  (movingFrameCore_derivative_memLp P.ordered
    (driftContinuous P ell) (driftContinuous P 0)
    (driftLipschitz P ell) (driftLipschitz P 0)
    (driftDerivativeContinuous P ell) (driftDerivativeContinuous P 0)
    (driftHasFDerivAt P ell) (driftHasFDerivAt P 0)
    (coupledPhaseMeasure (P.law a)) T hφ hc t ht).toLp _

theorem physicalMovingCoreLp_hasDerivAt
    (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (T : Icc a b) {φ : CoupledPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (physicalMovingCoreLp P ell T hφ.continuous hc)
      (physicalMovingCoreDerivativeLp P ell T hφ hc t ht) t :=
  movingFrameCoreLp_hasDerivAt P.ordered
    (driftContinuous P ell) (driftContinuous P 0)
    (driftLipschitz P ell) (driftLipschitz P 0)
    (driftDerivativeContinuous P ell) (driftDerivativeContinuous P 0)
    (driftHasFDerivAt P ell) (driftHasFDerivAt P 0)
    (coupledPhaseMeasure (P.law a)) T hφ hc t ht

/-- The missing Hilbert product rule, specialized to the genuine physical
Poisson inverse and actual full-versus-pure moving test. The formula contains
both terms; in particular it does not drop the moving-test derivative. -/
theorem physical_coordinate_moving_pairing_hasDerivAt
    (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (g : Lp ℝ 2 (P.law a)) (e : E)
    (T : Icc a b) {φ : CoupledPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt
      (fun s => inner ℝ
        (physicalCoordinate P e (physicalReferenceGradient P g s))
        (physicalMovingCoreLp P ell T hφ.continuous hc s))
      (inner ℝ (physicalCoordinate P e (physicalReferenceGradient P g t))
          (physicalMovingCoreDerivativeLp P ell T hφ hc t ht) +
       inner ℝ (physicalCoordinate P e (P.materialOperator t ht g))
          (physicalMovingCoreLp P ell T hφ.continuous hc t)) t := by
  have hG := (physicalCoordinate P e).hasFDerivAt.comp_hasDerivAt t
    (physicalReferenceGradient_hasDerivAt P g t ht)
  exact hG.inner ℝ (physicalMovingCoreLp_hasDerivAt P ell T hφ hc t ht)

/-- Integral version: all factors are actual L² elements, so these pairings
are genuine integrable products. This is not a formal differentiated integral. -/
theorem physical_coordinate_moving_integral_hasDerivAt
    (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (g : Lp ℝ 2 (P.law a)) (e : E)
    (T : Icc a b) {φ : CoupledPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt
      (fun s => ∫ z,
        (physicalCoordinate P e (physicalReferenceGradient P g s) z) *
        (physicalMovingCoreLp P ell T hφ.continuous hc s z)
        ∂coupledPhaseMeasure (P.law a))
      ((∫ z, (physicalCoordinate P e (physicalReferenceGradient P g t) z) *
          (physicalMovingCoreDerivativeLp P ell T hφ hc t ht z)
          ∂coupledPhaseMeasure (P.law a)) +
       (∫ z, (physicalCoordinate P e (P.materialOperator t ht g) z) *
          (physicalMovingCoreLp P ell T hφ.continuous hc t z)
          ∂coupledPhaseMeasure (P.law a))) t := by
  simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using
    physical_coordinate_moving_pairing_hasDerivAt P ell g e T hφ hc t ht

/-- Componentwise lifting for an arbitrary compact C¹ vector test, without
requiring the test to be separable in position and momentum. -/
theorem physical_vector_moving_pairing_hasDerivAt
    (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (g : Lp ℝ 2 (P.law a)) (T : Icc a b)
    (ψ : CoupledPhase E → E) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (t : ℝ) (ht : t ∈ Ioo a b) :
    let B := stdOrthonormalBasis ℝ E
    let hφ := fun i => (innerSL ℝ (B i)).contDiff.comp hψ
    let hcφ := fun i => hc.comp_left (show (innerSL ℝ (B i)) 0 = 0 by simp)
    HasDerivAt
      (fun s => ∑ i, inner ℝ
        (physicalCoordinate P (B i) (physicalReferenceGradient P g s))
        (physicalMovingCoreLp P ell T (hφ i).continuous (hcφ i) s))
      (∑ i, (inner ℝ
          (physicalCoordinate P (B i) (physicalReferenceGradient P g t))
          (physicalMovingCoreDerivativeLp P ell T (hφ i) (hcφ i) t ht) +
        inner ℝ (physicalCoordinate P (B i) (P.materialOperator t ht g))
          (physicalMovingCoreLp P ell T (hφ i).continuous (hcφ i) t))) t := by
  dsimp only
  apply HasDerivAt.fun_sum
  intro i _
  exact physical_coordinate_moving_pairing_hasDerivAt P ell g
    ((stdOrthonormalBasis ℝ E) i) T
    ((innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).contDiff.comp hψ)
    (hc.comp_left (by simp)) t ht

/-- The drift difference is exactly minus ell times the Hamiltonian field.
This algebra uses no time differentiability of the potential. -/
theorem physical_drift_difference (P : ReferencePoissonFamily E a b)
    (ell t : ℝ) (z : CoupledPhase E) :
    coupledDrift P.potential 0 P.scale t z -
      coupledDrift P.potential ell P.scale t z =
      (-ell) • WithLp.toLp 2 (z.snd, -gradient (P.potential t) z.fst) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E E).injective
  ext <;> simp [coupledDrift, sub_eq_add_neg, smul_neg, neg_smul]

/-- At zero coupling the constructed phase flow is exactly the constructed
position reference flow times the identity. Proven by trajectory uniqueness,
not postulated as a transport hypothesis. -/
theorem coupledFlow_zero_eq_reference (P : ReferencePoissonFamily E a b)
    (s t : Icc a b) (z : CoupledPhase E) :
    coupledFlow P.potential 0 P.scale (fun u _ => P.potential_C2 u)
      P.gradient_continuous P.scale_continuous P.scaleBound P.scale_bounded
      P.hessian_nonneg P.hessian_upper s z t =
    WithLp.toLp 2
      (referenceFlow P.potential P.scale (fun u _ => P.potential_C2 u)
        P.gradient_continuous P.scale_continuous P.scaleBound P.scale_bounded
        P.hessian_nonneg P.hessian_upper s z.fst t, z.snd) := by
  let R := referenceFlow P.potential P.scale (fun u _ => P.potential_C2 u)
    P.gradient_continuous P.scale_continuous P.scaleBound P.scale_bounded
    P.hessian_nonneg P.hessian_upper s z.fst
  let Q : ℝ → CoupledPhase E := fun u => WithLp.toLp 2 (R u, z.snd)
  have hR : Continuous R := referenceFlow_continuous P.potential P.scale
    (fun u _ => P.potential_C2 u) P.gradient_continuous P.scale_continuous
    P.scaleBound P.scale_bounded P.hessian_nonneg P.hessian_upper s z.fst
  have hQ : Continuous Q :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.continuous.comp
      (hR.prodMk continuous_const)
  have hd (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivWithinAt Q (coupledDrift P.potential 0 P.scale u (Q u)) (Icc a b) u := by
    have hr := referenceFlow_deriv P.potential P.scale
      (fun u _ => P.potential_C2 u) P.gradient_continuous P.scale_continuous
      P.scaleBound P.scale_bounded P.hessian_nonneg P.hessian_upper s z.fst u hu
    have hp := hr.prodMk (hasDerivWithinAt_const u (Icc a b) z.snd)
    let L : (E × E) →L[ℝ] CoupledPhase E :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap
    have hL : HasFDerivAt (fun q : E × E => L q) L (R u, z.snd) :=
      L.hasFDerivAt
    have hh := hL.comp_hasDerivWithinAt u hp
    change HasDerivWithinAt (fun q => WithLp.toLp 2 (R q, z.snd))
      (WithLp.toLp 2 (referenceDrift P.potential P.scale u (R u), 0))
      (Icc a b) u at hh
    simpa only [Q, R, coupledDrift, referenceDrift, zero_smul, zero_sub,
      neg_zero, neg_smul, WithLp.toLp_fst] using hh
  have hh := trajectory_dist (driftLipschitz P 0)
    (flow_continuous (driftLipschitz P 0) (driftContinuous P 0) s z).continuousOn
    (flow_deriv (driftLipschitz P 0) (driftContinuous P 0) s z)
    hQ.continuousOn hd s t
  have hinit : Q s = z := by
    dsimp [Q, R]
    rw [referenceFlow_initial]
    rfl
  rw [flow_initial, hinit, dist_self, zero_mul] at hh
  exact dist_le_zero.mp hh

/-- The zero-coupling homeomorphism transports only position, fixing momentum. -/
theorem referenceCoupledFlow_zero_apply (P : ReferencePoissonFamily E a b)
    (t : Icc a b) (z : CoupledPhase E) :
    referenceCoupledFlow P 0 t z = WithLp.toLp 2 (P.flow t z.fst, z.snd) :=
  coupledFlow_zero_eq_reference P P.leftTime t z

/-- At terminal test time a the actual moving core is exactly inverse-full
flow after the pure flow, not just another solution of a transport equation. -/
theorem physicalMovingCore_leftTime_eq
    (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (φ : CoupledPhase E → ℝ) (t : Icc a b) (x : CoupledPhase E) :
    physicalMovingCore P ell P.leftTime φ (t,x) =
      φ ((referenceCoupledFlow P ell t).symm (referenceCoupledFlow P 0 t x)) := by
  unfold physicalMovingCore movingFrameCore
  rw [backwardTest_eq]
  simp only [spaceTimeForward, projIcc_of_mem P.ordered t.property]
  rfl

/-- The same identity with the proved physical position frame substituted. -/
theorem physicalMovingCore_leftTime_eq_reference
    (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (φ : CoupledPhase E → ℝ) (t : Icc a b) (x : CoupledPhase E) :
    physicalMovingCore P ell P.leftTime φ (t,x) =
      φ ((referenceCoupledFlow P ell t).symm
        (WithLp.toLp 2 (P.flow t x.fst, x.snd))) := by
  rw [physicalMovingCore_leftTime_eq, referenceCoupledFlow_zero_apply]

/-- The scalar moving-test derivative has the negative transport coefficient.
Together with the already proved negative weak IBP this yields the positive
Hessian contribution, once the change-of-variables join is implemented. -/
theorem physicalMovingCore_derivative_eq (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (T : Icc a b) {φ : CoupledPhase E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (t : ℝ) (ht : t ∈ Ioo a b)
    (x : CoupledPhase E) :
    fderiv ℝ (physicalMovingCore P ell T φ) (t,x) (1,0) =
      (-ell) * fderiv ℝ
        (fun y => backwardTest P.ordered (driftContinuous P ell)
          (driftLipschitz P ell) T φ (t,y))
        (spaceTimeForward P.ordered (driftContinuous P 0)
          (driftLipschitz P 0) (t,x)).2
        (WithLp.toLp 2
          ((spaceTimeForward P.ordered (driftContinuous P 0)
            (driftLipschitz P 0) (t,x)).2.snd,
          -gradient (P.potential t)
            (spaceTimeForward P.ordered (driftContinuous P 0)
              (driftLipschitz P 0) (t,x)).2.fst)) := by
  rw [show physicalMovingCore P ell T φ =
    movingFrameCore P.ordered (driftContinuous P ell) (driftContinuous P 0)
      (driftLipschitz P ell) (driftLipschitz P 0) T φ from rfl]
  rw [movingFrameCore_derivative_eq P.ordered
    (driftContinuous P ell) (driftContinuous P 0)
    (driftLipschitz P ell) (driftLipschitz P 0)
    (driftDerivativeContinuous P ell) (driftDerivativeContinuous P 0)
    (driftHasFDerivAt P ell) (driftHasFDerivAt P 0) T hφ t ht x,
    physical_drift_difference, map_smul, smul_eq_mul]

end AcceleratedLogConcave.Kinetic.DirectW12
