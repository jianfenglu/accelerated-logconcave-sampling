import AcceleratedLogConcave.Analysis.Poisson.WeightedPullback
import AcceleratedLogConcave.Analysis.Poisson.CoerciveSolve
import AcceleratedLogConcave.Analysis.Poisson.Centered

/-!
# The genuine weighted graph on a common reference space

The scalar reference graph is a closed Hilbert subspace. Under a C1
measure-preserving diffeomorphism, the target gradient conjugates to the
inverse-transpose Jacobian multiplier on this graph. These statements concern
the actual closed weighted gradients, not an assumed form domain.
-/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem fderiv_homeomorph_comp_symm (e : E ≃ₜ E)
    (he : Differentiable ℝ e) (hi : Differentiable ℝ e.symm) (x : E) :
    (fderiv ℝ e x).comp (fderiv ℝ e.symm (e x)) = ContinuousLinearMap.id ℝ E := by
  have hh := (he (e.symm (e x))).hasFDerivAt.comp (e x) (hi (e x)).hasFDerivAt
  simpa only [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply, Homeomorph.self_comp_symm, fderiv_id] using hh.fderiv.symm

section Transport
variable (μ ν : Measure E) (U V : E → ℝ)
  (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
  (hIU : Integrable (fun x => Real.exp (-U x))) (hIV : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -U x)) (hν : ν = volume.tilted (fun x => -V x))
  (e : E ≃ₜ E) (he : MeasurePreserving e μ ν)
  (heC : ContDiff ℝ 1 e) (heInv : ContDiff ℝ 1 e.symm)
  (M N : ℝ) (hM : ∀ x, ‖fderiv ℝ e x‖ ≤ M) (hN : ∀ x, ‖fderiv ℝ e.symm x‖ ≤ N)

/-- The inverse-transpose spatial derivative as an actual reference multiplier. -/
def inverseJacobianMultiplier : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  fieldMultiplier μ (fun x => (fderiv ℝ e.symm (e x)).adjoint)
    (ContinuousLinearMap.adjoint.continuous.comp
      ((heInv.continuous_fderiv one_ne_zero).comp e.continuous)) N
    (fun x => by simpa using hN (e x))

theorem inverseJacobianMultiplier_jacobian (G : Lp E 2 μ) :
    inverseJacobianMultiplier μ e heInv N hN
      (jacobianAdjointMultiplier μ e heC M hM G) = G := by
  apply Lp.ext
  filter_upwards [fieldMultiplier_coe μ (fun x => (fderiv ℝ e.symm (e x)).adjoint)
    (ContinuousLinearMap.adjoint.continuous.comp
      ((heInv.continuous_fderiv one_ne_zero).comp e.continuous)) N
    (fun x => by simpa using hN (e x)) (jacobianAdjointMultiplier μ e heC M hM G),
    fieldMultiplier_coe μ (fun x => (fderiv ℝ e x).adjoint)
      (ContinuousLinearMap.adjoint.continuous.comp (heC.continuous_fderiv one_ne_zero)) M
      (fun x => by simpa using hM x) G] with x hx hy
  change (inverseJacobianMultiplier μ e heInv N hN
    (jacobianAdjointMultiplier μ e heC M hM G)) x = (fderiv ℝ e.symm (e x)).adjoint
    ((jacobianAdjointMultiplier μ e heC M hM G) x) at hx
  change (jacobianAdjointMultiplier μ e heC M hM G) x = (fderiv ℝ e x).adjoint (G x) at hy
  rw [hx, hy, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
    fderiv_homeomorph_comp_symm e (heC.differentiable one_ne_zero) (heInv.differentiable one_ne_zero),
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]

theorem jacobian_inverseJacobianMultiplier (G : Lp E 2 μ) :
    jacobianAdjointMultiplier μ e heC M hM (inverseJacobianMultiplier μ e heInv N hN G) = G := by
  apply Lp.ext
  filter_upwards [fieldMultiplier_coe μ (fun x => (fderiv ℝ e x).adjoint)
      (ContinuousLinearMap.adjoint.continuous.comp (heC.continuous_fderiv one_ne_zero)) M
      (fun x => by simpa using hM x) (inverseJacobianMultiplier μ e heInv N hN G),
    fieldMultiplier_coe μ (fun x => (fderiv ℝ e.symm (e x)).adjoint)
      (ContinuousLinearMap.adjoint.continuous.comp
        ((heInv.continuous_fderiv one_ne_zero).comp e.continuous)) N
      (fun x => by simpa using hN (e x)) G] with x hx hy
  change (jacobianAdjointMultiplier μ e heC M hM
    (inverseJacobianMultiplier μ e heInv N hN G)) x =
      (fderiv ℝ e x).adjoint ((inverseJacobianMultiplier μ e heInv N hN G) x) at hx
  change (inverseJacobianMultiplier μ e heInv N hN G) x =
    (fderiv ℝ e.symm (e x)).adjoint (G x) at hy
  have hid : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ E := by
    simpa only [Homeomorph.symm_symm, Homeomorph.symm_apply_apply] using
      fderiv_homeomorph_comp_symm e.symm (heInv.differentiable one_ne_zero)
        (heC.differentiable one_ne_zero) (e x)
  rw [hx, hy, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
    hid, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]

theorem jacobianAdjointMultiplier_norm_le : ‖jacobianAdjointMultiplier μ e heC M hM‖ ≤ M :=
  fieldMultiplier_norm_le _ _ _ _ _

theorem inverseJacobianMultiplier_norm_le : ‖inverseJacobianMultiplier μ e heInv N hN‖ ≤ N :=
  fieldMultiplier_norm_le _ _ _ _ _

include heC hM in
/-- The transformed target derivative equals the inverse-transpose multiplier
of the actual reference derivative, on the whole closed domain. -/
theorem closed_gradient_pullback_eq (u : Sobolev ν V hV hIV hν)
    (w : Sobolev μ U hU hIU hμ)
    (hw : (w : Lp ℝ 2 μ) = pullback e.toMeasurableEquiv he (u : Lp ℝ 2 ν)) :
    pullback e.toMeasurableEquiv he (closedGradient ν V hV hIV hν u) =
      inverseJacobianMultiplier μ e heInv N hN (closedGradient μ U hU hIU hμ w) := by
  have hg := closed_graph_pullback μ ν U V hU hV hIU hIV hμ hν e he heC M hM
    (u : Lp ℝ 2 ν) (closedGradient ν V hV hIV hν u)
    ((closedGradient ν V hV hIV hν).mem_graph u)
  rw [← hw] at hg
  have heq : closedGradient μ U hU hIU hμ w = jacobianAdjointMultiplier μ e heC M hM
      (pullback e.toMeasurableEquiv he (closedGradient ν V hV hIV hν u)) :=
    (closedGradient μ U hU hIU hμ).mem_graph_snd_inj
      ((closedGradient μ U hU hIU hμ).mem_graph w) hg rfl
  rw [heq, inverseJacobianMultiplier_jacobian]
end Transport
end AcceleratedLogConcave.Analysis.Poisson
