import AcceleratedLogConcave.Analysis.Poisson.ReferenceGraph
import AcceleratedLogConcave.Analysis.Poisson.GradientInverse

/-!
# Physical weak solutions on the common centered reference graph

The reference graph is built from the actual closed weighted gradient. The
pullback of a centered physical weak Poisson solution satisfies the constructed
common-domain form equation, by the proven closed-graph chain rule and unitarity.
-/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (U V : E → ℝ) (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
  (hIU : Integrable (fun x => Real.exp (-U x))) (hIV : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -U x)) (hν : ν = volume.tilted (fun x => -V x))
  (e : E ≃ₜ E) (he : MeasurePreserving e μ ν)
  (heC : ContDiff ℝ 1 e) (heInv : ContDiff ℝ 1 e.symm)
  (M N : ℝ) (hM : ∀ x, ‖fderiv ℝ e x‖ ≤ M) (hN : ∀ x, ‖fderiv ℝ e.symm x‖ ≤ N)

local instance : CompleteSpace (centeredGraph (closedGradient μ U hU hIU hμ) (mean μ)) :=
  (centeredGraph_closed _ (closedGradient_isClosed μ U hU hIU hμ) (mean μ)).completeSpace_coe

/-- Unitary composition preserves the actual Sobolev domain. -/
def pulledSobolev (u : Sobolev ν V hV hIV hν) : Sobolev μ U hU hIU hμ :=
  ⟨pullback e.toMeasurableEquiv he (u : Lp ℝ 2 ν),
    LinearPMap.mem_domain_of_mem_graph
      (closed_graph_pullback μ ν U V hU hV hIU hIV hμ hν e he heC M hM
        (u : Lp ℝ 2 ν) (closedGradient ν V hV hIV hν u)
        ((closedGradient ν V hV hIV hν).mem_graph u))⟩

/-- A centered physical domain element becomes a member of the fixed genuine graph. -/
def pulledCenteredGraph (u : Sobolev ν V hV hIV hν) (hu : mean ν u = 0) :
    centeredGraph (closedGradient μ U hU hIU hμ) (mean μ) :=
  referenceGraphLift _ _ (pulledSobolev μ ν U V hU hV hIU hIV hμ hν e he heC M hM u)
    (by
      change mean μ (pullback e.toMeasurableEquiv he (u : Lp ℝ 2 ν)) = 0
      rw [mean_apply]
      exact (integral_pullback e.toMeasurableEquiv he (u : Lp ℝ 2 ν)).trans
        ((mean_apply ν u).symm.trans hu))

/-- Pullback tests cover the complete centered graph; no test core is assumed. -/
def targetSobolevOfGraph
    (q : centeredGraph (closedGradient μ U hU hIU hμ) (mean μ)) : Sobolev ν V hV hIV hν :=
  ⟨(pullback e.toMeasurableEquiv he).symm (referenceGraphValue _ _ q),
    (sobolev_pullback_iff μ ν U V hU hV hIU hIV hμ hν e he heC M hM heInv N hN _).mpr
      (by
        rw [LinearIsometryEquiv.apply_symm_apply]
        exact (referenceGraphSobolev _ _ q).property)⟩

omit [IsProbabilityMeasure ν] in
theorem targetSobolevOfGraph_pullback
    (q : centeredGraph (closedGradient μ U hU hIU hμ) (mean μ)) :
    pullback e.toMeasurableEquiv he
      (targetSobolevOfGraph μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN q : Lp ℝ 2 ν) =
      referenceGraphValue _ _ q := LinearIsometryEquiv.apply_symm_apply _ _

omit [IsProbabilityMeasure ν] in
theorem targetSobolevOfGraph_gradient
    (q : centeredGraph (closedGradient μ U hU hIU hμ) (mean μ)) :
    pullback e.toMeasurableEquiv he
      (closedGradient ν V hV hIV hν
        (targetSobolevOfGraph μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN q)) =
      inverseJacobianMultiplier μ e heInv N hN (referenceGraphGradient _ _ q) := by
  rw [referenceGraphGradient_eq]
  apply closed_gradient_pullback_eq μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN
  exact (targetSobolevOfGraph_pullback μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN q).symm

theorem pulledCenteredGraph_gradient
    (u : Sobolev ν V hV hIV hν) (hu : mean ν u = 0) :
    inverseJacobianMultiplier μ e heInv N hN
      (referenceGraphGradient _ _ (pulledCenteredGraph μ ν U V hU hV hIU hIV hμ hν e he heC M hM u hu)) =
      pullback e.toMeasurableEquiv he (closedGradient ν V hV hIV hν u) := by
  change inverseJacobianMultiplier μ e heInv N hN
    (closedGradient μ U hU hIU hμ (pulledSobolev μ ν U V hU hV hIU hIV hμ hν e he heC M hM u)) = _
  exact (closed_gradient_pullback_eq μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN
    u (pulledSobolev μ ν U V hU hV hIU hIV hμ hν e he heC M hM u) rfl).symm

/-- The true physical weak equation becomes the common-domain equation after
unitary scalar/vector pullback. -/
theorem pulledCenteredGraph_weak
    (u : Sobolev ν V hV hIV hν) (hu : mean ν u = 0) (g : Lp ℝ 2 ν)
    (hweak : ∀ v : Sobolev ν V hV hIV hν,
      inner ℝ (closedGradient ν V hV hIV hν u) (closedGradient ν V hV hIV hν v) =
        inner ℝ g (v : Lp ℝ 2 ν))
    (q : centeredGraph (closedGradient μ U hU hIU hμ) (mean μ)) :
    inner ℝ
      (inverseJacobianMultiplier μ e heInv N hN
        (referenceGraphGradient _ _ (pulledCenteredGraph μ ν U V hU hV hIU hIV hμ hν e he heC M hM u hu)))
      (inverseJacobianMultiplier μ e heInv N hN (referenceGraphGradient _ _ q)) =
        inner ℝ (pullback e.toMeasurableEquiv he g) (referenceGraphValue _ _ q) := by
  rw [pulledCenteredGraph_gradient, ← targetSobolevOfGraph_gradient μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN,
    LinearIsometryEquiv.inner_map_map, hweak,
    ← targetSobolevOfGraph_pullback μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN,
    LinearIsometryEquiv.inner_map_map]

/-- The actual transported gradient as a bounded map on the fixed graph. -/
def transportedGraphGradient :
    centeredGraph (closedGradient μ U hU hIU hμ) (mean μ) →L[ℝ] Lp E 2 μ :=
  (inverseJacobianMultiplier μ e heInv N hN).comp
    (referenceGraphGradient (closedGradient μ U hU hIU hμ) (mean μ))

include heC hM in
/-- Coercivity on the common graph is derived from actual curvature and the
proved Jacobian inverse identity, rather than supplied as an analytic premise. -/
theorem transportedGraph_coercive
    (hU2 : ContDiff ℝ 2 U) (m L : ℝ) (hm : 0 < m) (hMpos : 0 < M)
    (hlower : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v)
    (hupper : ∀ x v, fderiv ℝ (fderiv ℝ U) x v v ≤ L * ‖v‖ ^ 2)
    (q : centeredGraph (closedGradient μ U hU hIU hμ) (mean μ)) :
    (m / (m + 1) / M ^ 2) * ‖q‖ ^ 2 ≤
      ‖transportedGraphGradient μ U hU hIU hμ e heInv N hN q‖ ^ 2 := by
  exact referenceGraph_multiplier_coercive _ _ hm hMpos
    (fun v hv => Gibbs.closedGradient_poincare μ U hU2 hIU hμ m L hm hlower hupper v
      ((mean_apply μ v).symm.trans hv))
    (inverseJacobianMultiplier μ e heInv N hN) (jacobianAdjointMultiplier μ e heC M hM)
    (jacobian_inverseJacobianMultiplier μ e heC heInv M N hM hN)
    (jacobianAdjointMultiplier_norm_le μ e heC M hM) q

/-- A physical centered weak solution equals the Lax--Milgram solution on the
actual transported reference graph. All coercivity is derived from curvature. -/
theorem pulledCenteredGraph_eq_commonDomainSolution
    (hU2 : ContDiff ℝ 2 U) (m L : ℝ) (hm : 0 < m) (hMpos : 0 < M)
    (hlower : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v)
    (hupper : ∀ x v, fderiv ℝ (fderiv ℝ U) x v v ≤ L * ‖v‖ ^ 2)
    (u : Sobolev ν V hV hIV hν) (hu : mean ν u = 0) (g : Lp ℝ 2 ν)
    (hweak : ∀ v : Sobolev ν V hV hIV hν,
      inner ℝ (closedGradient ν V hV hIV hν u) (closedGradient ν V hV hIV hν v) =
        inner ℝ g (v : Lp ℝ 2 ν)) :
    pulledCenteredGraph μ ν U V hU hV hIU hIV hμ hν e he heC M hM u hu =
      MovingForms.commonDomainSolution
        (transportedGraphGradient μ U hU hIU hμ e heInv N hN)
        (referenceGraphValue (closedGradient μ U hU hIU hμ) (mean μ))
        (by positivity : 0 < m / (m + 1) / M ^ 2)
        (transportedGraph_coercive μ U hU hIU hμ e heC heInv M N hM hN hU2 m L hm hMpos hlower hupper)
        (pullback e.toMeasurableEquiv he g) := by
  apply MovingForms.commonDomainSolution_unique
  exact pulledCenteredGraph_weak μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN u hu g hweak

include hV in
/-- Identification with the actual physical gradient inverse, for arbitrary
reference L2 forcing. The constant component is removed by the true centered
Poisson inverse and vanishes against the reference graph tests. -/
theorem commonDomainSolution_gradient_eq_pullback_gradientInverse
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (m L n K : ℝ) (hm : 0 < m) (hn : 0 < n) (hMpos : 0 < M)
    (hloU : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v)
    (hupU : ∀ x v, fderiv ℝ (fderiv ℝ U) x v v ≤ L * ‖v‖ ^ 2)
    (hloV : ∀ x v, n * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hupV : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ K * ‖v‖ ^ 2)
    (g : Lp ℝ 2 μ) :
    transportedGraphGradient μ U hU hIU hμ e heInv N hN
      (MovingForms.commonDomainSolution
        (transportedGraphGradient μ U hU hIU hμ e heInv N hN)
        (referenceGraphValue (closedGradient μ U hU hIU hμ) (mean μ))
        (by positivity : 0 < m / (m + 1) / M ^ 2)
        (transportedGraph_coercive μ U hU hIU hμ e heC heInv M N hM hN hU2 m L hm hMpos hloU hupU) g) =
      pullback e.toMeasurableEquiv he
        (gradientPoissonInverse ν V hV2 hIV hν n K hn hloV hupV
          ((pullback e.toMeasurableEquiv he).symm g)) := by
  let f := (pullback e.toMeasurableEquiv he).symm g
  let u := poissonSolution ν V hV2 hIV hν n K hn hloV hupV f
  have hus := poissonSolution_spec (μ := ν) (V := V) (hV := hV2) (hI := hIV)
    (hμ := hν) (m := n) (L := K) (hm := hn) (hlower := hloV) (hupper := hupV) f
  have hu : mean ν u = 0 := (mean_apply ν u).trans hus.1
  let p := pulledCenteredGraph μ ν U V hU hV hIU hIV hμ hν e he heC M hM u hu
  have hp : p = MovingForms.commonDomainSolution
      (transportedGraphGradient μ U hU hIU hμ e heInv N hN)
      (referenceGraphValue (closedGradient μ U hU hIU hμ) (mean μ))
      (by positivity : 0 < m / (m + 1) / M ^ 2)
      (transportedGraph_coercive μ U hU hIU hμ e heC heInv M N hM hN hU2 m L hm hMpos hloU hupU) g := by
    apply MovingForms.commonDomainSolution_unique
    intro q
    have hh := pulledCenteredGraph_weak μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN
      u hu (centerForcing ν f) hus.2 q
    change inner ℝ (transportedGraphGradient μ U hU hIU hμ e heInv N hN p)
      (transportedGraphGradient μ U hU hIU hμ e heInv N hN q) = _ at hh
    rw [hh]
    let v := targetSobolevOfGraph μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN q
    have hvg : pullback e.toMeasurableEquiv he (v : Lp ℝ 2 ν) = referenceGraphValue _ _ q :=
      targetSobolevOfGraph_pullback μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN q
    have hv : mean ν v = 0 := by
      rw [mean_apply, ← integral_pullback e.toMeasurableEquiv he (v : Lp ℝ 2 ν), hvg, ← mean_apply]
      exact referenceGraphValue_centered _ _ q
    rw [← hvg, LinearIsometryEquiv.inner_map_map]
    have hfg : pullback e.toMeasurableEquiv he f = g := LinearIsometryEquiv.apply_symm_apply _ _
    rw [← hfg, LinearIsometryEquiv.inner_map_map, centerForcing_apply,
      inner_sub_left, inner_smul_left]
    change inner ℝ f (v : Lp ℝ 2 ν) - mean ν f * mean ν v = _
    rw [hv, mul_zero, sub_zero]
  rw [← hp]
  exact pulledCenteredGraph_gradient μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN u hu
end AcceleratedLogConcave.Analysis.Poisson
