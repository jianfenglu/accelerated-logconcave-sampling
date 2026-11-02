import AcceleratedLogConcave.Conditional.Centering.Field
import AcceleratedLogConcave.Kinetic.ReferenceFlow.Continuity
import AcceleratedLogConcave.Kinetic.ReferenceFlow.GaussianDensity

/-! The weighted Stein sign gives cancellation of the centering phase flux. -/
noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional.Centering
open Kinetic Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private def fstL : Phase E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap
private def sndL : Phase E →L[ℝ] E := (ContinuousLinearMap.snd ℝ E E).comp
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap

/-- The phase divergence is the divergence of the position-current column;
the momentum drift has no momentum dependence. -/
theorem velocity_divergence {Kt : E → E →L[ℝ] E} {M : E → E}
    (hK : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M) (u : E) (s : ℝ) (z : Phase E) :
    fluxDivergence (velocity Kt M u s) z =
      -s⁻¹ * fluxDivergence (fun y => Kt y z.snd) z.fst := by
  let F := fstL (E := E)
  let S := sndL (E := E)
  have hk := (hK.differentiable_one z.fst).hasFDerivAt.comp z F.hasFDerivAt
  have hm := (hM.differentiable_one z.fst).hasFDerivAt.comp z F.hasFDerivAt
  have hd := (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.hasFDerivAt.comp z
    ((((hk.clm_apply S.hasFDerivAt).const_smul s⁻¹).neg).prodMk
      ((hm.sub_const u).const_smul s⁻¹))
  have hcol := (hK.differentiable_one z.fst).hasFDerivAt.clm_apply
    (hasFDerivAt_const z.snd z.fst)
  let b := stdOrthonormalBasis ℝ E
  rw [fluxDivergence_eq_sum_basis (b.prod b) ((contDiff_velocity hK hM u s).differentiable_one z),
    fluxDivergence_eq_sum_basis b hcol.differentiableAt]
  have he : fderiv ℝ (velocity Kt M u s) z = _ := hd.fderiv
  rw [he, hcol.fderiv, Fintype.sum_sum_type]
  simp [F, S, fstL, sndL, OrthonormalBasis.prod_apply, WithLp.prod_inner_apply,
    inner_smul_right, ← Finset.mul_sum]
/-- The weighted-adjoint sign in the Stein equation cancels the Gaussian
momentum score. This is a generic implication; the actual Stein equation is
supplied by the transported-kernel construction. -/
theorem density_divergence_zero_of_stein {Kt : E → E →L[ℝ] E} {M : E → E}
    (hK : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M) (u : E) (s : ℝ)
    (p : E → ℝ) (hp : ContDiff ℝ 1 p)
    (hstein : ∀ y g, fderiv ℝ p y (Kt y g) +
      p y * fluxDivergence (fun w => Kt w g) y = -p y * inner ℝ (M y - u) g)
    (z : Phase E) :
    fderiv ℝ (coupledDensity p standardGaussianDensity) z (velocity Kt M u s z) +
      coupledDensity p standardGaussianDensity z *
        LinearMap.trace ℝ (Phase E) (fderiv ℝ (velocity Kt M u s) z).toLinearMap = 0 := by
  let F := fstL (E := E)
  let S := sndL (E := E)
  have hd := ((hp.differentiable_one z.fst).hasFDerivAt.comp z F.hasFDerivAt).mul
    ((standardGaussianDensity_hasFDerivAt z.snd).comp z S.hasFDerivAt)
  have he : fderiv ℝ (coupledDensity p standardGaussianDensity) z = _ := hd.fderiv
  rw [← fluxDivergence_eq_trace ((contDiff_velocity hK hM u s).differentiable_one z),
    velocity_divergence hK hM u s z, he]
  change p z.fst * (-standardGaussianDensity z.snd *
      inner ℝ z.snd (s⁻¹ • (M z.fst - u))) +
    standardGaussianDensity z.snd * fderiv ℝ p z.fst (-(s⁻¹ • Kt z.fst z.snd)) +
    (p z.fst * standardGaussianDensity z.snd) *
      (-s⁻¹ * fluxDivergence (fun w => Kt w z.snd) z.fst) = 0
  simp only [inner_smul_right, map_neg, map_smul, smul_eq_mul]
  rw [← real_inner_comm z.snd (M z.fst - u)]
  linear_combination -s⁻¹ * standardGaussianDensity z.snd * hstein z.fst z.snd

end AcceleratedLogConcave.Conditional.Centering
