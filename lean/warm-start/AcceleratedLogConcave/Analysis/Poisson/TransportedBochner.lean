import AcceleratedLogConcave.Analysis.Poisson.TransportedSolution

/-!
# The sharp Bochner bound on the transported reference graph

Unitary pullback of the genuine physical Hessian multiplier preserves the sharp
curvature-composed Poisson bound. The common-domain solution is identified with
the actual physical weak solution, so no Bochner estimate is supplied as data.
-/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The physical Hessian multiplier conjugated by the actual unitary composition. -/
def transportedHessianMultiplier (μ ν : Measure E) (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (e : E ≃ₜ E) (he : MeasurePreserving e μ ν)
    (n K : ℝ)
    (hlo : ∀ x v, n * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ K * ‖v‖ ^ 2) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  (pullback (F := E) e.toMeasurableEquiv he).toLinearIsometry.toContinuousLinearMap.comp
    ((hessianMultiplier ν V hV n K hlo hup).comp
      (pullback (F := E) e.toMeasurableEquiv he).symm.toLinearIsometry.toContinuousLinearMap)

@[simp]
theorem transportedHessianMultiplier_pullback (μ ν : Measure E) (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (e : E ≃ₜ E) (he : MeasurePreserving e μ ν)
    (n K : ℝ)
    (hlo : ∀ x v, n * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ K * ‖v‖ ^ 2)
    (G : Lp E 2 ν) :
    transportedHessianMultiplier μ ν V hV e he n K hlo hup
      (pullback e.toMeasurableEquiv he G) =
      pullback e.toMeasurableEquiv he (hessianMultiplier ν V hV n K hlo hup G) := by
  simp [transportedHessianMultiplier]

/-- The conjugated operator is the actual Hessian field evaluated along the
flow; vector pullback is composition without an extra Jacobian. -/
theorem transportedHessianMultiplier_coe (μ ν : Measure E) (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (e : E ≃ₜ E) (he : MeasurePreserving e μ ν)
    (n K : ℝ)
    (hlo : ∀ x v, n * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ K * ‖v‖ ^ 2)
    (G : Lp E 2 μ) :
    transportedHessianMultiplier μ ν V hV e he n K hlo hup G =ᵐ[μ]
      fun x => hessianOperator V (e x) (G x) := by
  let F := (pullback e.toMeasurableEquiv he).symm G
  have hF : G =ᵐ[μ] fun x => F (e x) := by
    simpa only [F, LinearIsometryEquiv.apply_symm_apply, Homeomorph.toMeasurableEquiv_coe] using
      pullback_coeFn e.toMeasurableEquiv he F
  filter_upwards [pullback_coeFn e.toMeasurableEquiv he (hessianMultiplier ν V hV n K hlo hup F),
    he.quasiMeasurePreserving.ae (hessianMultiplier_coe ν V hV n K hlo hup F), hF] with x hx hy hz
  change (pullback e.toMeasurableEquiv he (hessianMultiplier ν V hV n K hlo hup F)) x = _
  change (pullback e.toMeasurableEquiv he (hessianMultiplier ν V hV n K hlo hup F)) x =
    (hessianMultiplier ν V hV n K hlo hup F) (e x) at hx
  rw [hx, hy, ← hz]

/-- Identification with the continuous matrix-field implementation, for any
proved bound chosen to construct that multiplier. -/
theorem transportedHessianMultiplier_eq_fieldMultiplier (μ ν : Measure E) (V : E → ℝ)
    (hV : ContDiff ℝ 2 V) (e : E ≃ₜ E) (he : MeasurePreserving e μ ν)
    (n K : ℝ)
    (hlo : ∀ x v, n * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ K * ‖v‖ ^ 2)
    (B : ℝ) (hB : ∀ x, ‖hessianOperator V (e x)‖ ≤ B) :
    transportedHessianMultiplier μ ν V hV e he n K hlo hup =
      fieldMultiplier μ (fun x => hessianOperator V (e x))
        ((continuous_hessianOperator hV).comp e.continuous) B hB := by
  apply ContinuousLinearMap.ext
  intro G
  apply Lp.ext
  exact (transportedHessianMultiplier_coe μ ν V hV e he n K hlo hup G).trans
    (fieldMultiplier_coe μ _ _ B hB G).symm

variable (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (U V : E → ℝ) (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
  (hIU : Integrable (fun x => Real.exp (-U x))) (hIV : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -U x)) (hν : ν = volume.tilted (fun x => -V x))
  (e : E ≃ₜ E) (he : MeasurePreserving e μ ν)
  (heC : ContDiff ℝ 1 e) (heInv : ContDiff ℝ 1 e.symm)
  (M N : ℝ) (hM : ∀ x, ‖fderiv ℝ e x‖ ≤ M) (hN : ∀ x, ‖fderiv ℝ e.symm x‖ ≤ N)

local instance : CompleteSpace (centeredGraph (closedGradient μ U hU hIU hμ) (mean μ)) :=
  (centeredGraph_closed _ (closedGradient_isClosed μ U hU hIU hμ) (mean μ)).completeSpace_coe

include hV hIV hν in
/-- The sharp source estimate on the actual common domain. Curvature and the
physical Poisson equation discharge the estimate, with no inverse-gap factor. -/
theorem transportedHessian_commonDomainSolution_norm_le
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (m L n : ℝ) (hm : 0 < m) (hn : 0 < n) (hMpos : 0 < M)
    (hloU : ∀ x v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v)
    (hupU : ∀ x v, fderiv ℝ (fderiv ℝ U) x v v ≤ L * ‖v‖ ^ 2)
    (hloV : ∀ x v, n * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hupV : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ 1 * ‖v‖ ^ 2)
    (g : Lp ℝ 2 μ) :
    ‖transportedHessianMultiplier μ ν V hV2 e he n 1 hloV hupV
      (transportedGraphGradient μ U hU hIU hμ e heInv N hN
        (MovingForms.commonDomainSolution
          (transportedGraphGradient μ U hU hIU hμ e heInv N hN)
          (referenceGraphValue (closedGradient μ U hU hIU hμ) (mean μ))
          (by positivity : 0 < m / (m + 1) / M ^ 2)
          (transportedGraph_coercive μ U hU hIU hμ e heC heInv M N hM hN
            hU2 m L hm hMpos hloU hupU) g))‖ ≤ ‖g‖ := by
  rw [commonDomainSolution_gradient_eq_pullback_gradientInverse
    μ ν U V hU hV hIU hIV hμ hν e he heC heInv M N hM hN
    hU2 hV2 m L n 1 hm hn hMpos hloU hupU hloV hupV g,
    transportedHessianMultiplier_pullback, LinearIsometryEquiv.norm_map]
  have hb := ContinuousLinearMap.le_opNorm
    ((hessianMultiplier ν V hV2 n 1 hloV hupV).comp
      (gradientPoissonInverse ν V hV2 hIV hν n 1 hn hloV hupV))
    ((pullback e.toMeasurableEquiv he).symm g)
  exact hb.trans (by
    simpa only [LinearIsometryEquiv.norm_map, one_mul] using
      mul_le_mul_of_nonneg_right
        (hessianMultiplier_comp_gradientPoissonInverse_norm_le ν V hV2 hIV hν n hn hloV hupV)
        (norm_nonneg ((pullback e.toMeasurableEquiv he).symm g)))

end AcceleratedLogConcave.Analysis.Poisson
