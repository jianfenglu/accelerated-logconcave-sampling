import AcceleratedLogConcave.Root.OuterRootPhysicalPath
import DirectW12.OriginalFamilyAdapter
import AcceleratedLogConcave.Kinetic.ReferenceFlow

/-! ODE uniqueness identifies the conditional Gaussian-start
trajectory with the actual original-data coupled physical reference flow.
This identifies paths, not merely marginals. -/
noncomputable section
set_option autoImplicit false
open Set
namespace AcceleratedLogConcave.Root.OuterRootFlowIdentification
open Kinetic OuterRootPhysicalPath
open OAI.LogConcaveSampling.GlobalODE
variable {ι : Type*} [Fintype ι]
variable {V : (EuclideanSpace ℝ ι) → ℝ} (hV : ContDiff ℝ 2 V) {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
  (hlo : ∀ z v, m*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)

/-- Reuse the integrated original-data physical reference, with curvature m
represented by the existing inverse-curvature parameter. -/
def family : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2) :=
  RecursiveInnovation.originalPhysicalReference hV (inv_pos.mpr hm) hh
    (by simpa only [inv_inv] using hlo) hup

include hm hlo in
theorem lower_nonneg : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ V) z v v :=
  fun z v => (mul_nonneg hm.le (sq_nonneg ‖v‖)).trans (hlo z v)

/-- The exact input is (sqrt(h)*xF,zeta); no replacement of the initial law. -/
theorem conditional_eq_reference_trajectory (xF zeta : (EuclideanSpace ℝ ι)) {u : ℝ}
    (hu : u ∈ Icc (0:ℝ) (1/2)) :
    (position hV hh (lower_nonneg hm hlo) hup xF zeta u,
      rawY hV hh (lower_nonneg hm hlo) hup xF zeta u) =
      referenceCoupledTrajectory (family hV hm hh hlo hup)
        (Real.sqrt (2*h^2)) (Real.sqrt h • xF,zeta) u := by
  let F := family hV hm hh hlo hup
  let ell := Real.sqrt (2*h^2)
  let Y := rawY hV hh (lower_nonneg hm hlo) hup xF zeta
  let A := position hV hh (lower_nonneg hm hlo) hup xF zeta
  let C := (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι)).symm.toContinuousLinearMap
  let X : ℝ → CoupledPhase (EuclideanSpace ℝ ι) := fun t => C (A t,Y t)
  let Z : ℝ → CoupledPhase (EuclideanSpace ℝ ι) := coupledFlow F.potential ell F.scale
    (fun t _ => F.potential_C2 t) F.gradient_continuous F.scale_continuous
    F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime
    (WithLp.toLp 2 (Real.sqrt h • xF,zeta))
  have hY : Continuous Y := Numerics.AffineFlowIdentities.convexProbabilityFlow_continuous
    (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hF
    (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hell
    (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hlo
    (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hup xF
    (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hr
    (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hb (by norm_num) (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hb1 ⟨0, le_rfl, (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hb⟩ zeta
  have hA : Continuous A := continuous_const.add
    ((continuous_const.mul continuous_id).smul hY)
  have hX : Continuous X := C.continuous.comp (hA.prodMk hY)
  have hdX (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/2)) :
      HasDerivWithinAt X (coupledDrift F.potential ell F.scale t (X t))
        (Icc (0:ℝ) (1/2)) t := by
    have hd := C.hasFDerivAt.comp_hasDerivWithinAt t
      ((position_deriv hV hh (lower_nonneg hm hlo) hup xF zeta ht).prodMk
        (rawY_deriv hV hh (lower_nonneg hm hlo) hup xF zeta ht))
    have hp := RecursiveInnovation.originalPhysicalReference_potential hV
      (inv_pos.mpr hm) hh (by simpa only [inv_inv] using hlo) hup t ht
    have hs := RecursiveInnovation.originalPhysicalReference_scale hV
      (inv_pos.mpr hm) hh (by simpa only [inv_inv] using hlo) hup t ht
    change F.potential t = Gibbs.heatPotential V (variance h t) at hp
    change F.scale t = scale h t at hs
    simpa only [X, C, ell, A, Y, coupledDrift, hp, hs,
      ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, Function.comp_def] using hd

  have hZ : Continuous Z := flow_continuous _ _ _ _
  have hdZ (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/2)) :
      HasDerivWithinAt Z (coupledDrift F.potential ell F.scale t (Z t))
        (Icc (0:ℝ) (1/2)) t :=
    coupledFlow_deriv F.potential ell F.scale (fun s _ => F.potential_C2 s)
      F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
      F.hessian_nonneg F.hessian_upper F.leftTime _ t ht
  have hi : X 0 = Z 0 := by
    have hz := coupledFlow_initial F.potential ell F.scale (fun s _ => F.potential_C2 s)
      F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
      F.hessian_nonneg F.hessian_upper F.leftTime (WithLp.toLp 2 (Real.sqrt h • xF,zeta))
    have hy := Conditional.convexProbabilityFlow_initial
      (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hF
      (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hell
      (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hlo
      (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hup xF
      (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hr
      (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hb (by norm_num) (OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hb1 ⟨0,le_rfl,(OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup).hb⟩ zeta
    change Y 0 = zeta at hy
    change Z 0 = WithLp.toLp 2 (Real.sqrt h • xF,zeta) at hz
    rw [hz]
    change WithLp.toLp 2 (Real.sqrt h • xF + (ell*0) • Y 0,Y 0) = _
    simp only [mul_zero, zero_smul, add_zero, hy]
  have he := trajectory_unique_right
    (fun t ht => coupledDrift_lipschitz F.potential ell F.scale t (F.potential_C2 t)
      (F.hessian_nonneg t ht) (F.hessian_upper t ht) F.scaleBound (F.scale_bounded t ht))
    hX.continuousOn hdX hZ.continuousOn hdZ hi hu
  exact congrArg WithLp.ofLp he

end AcceleratedLogConcave.Root.OuterRootFlowIdentification
