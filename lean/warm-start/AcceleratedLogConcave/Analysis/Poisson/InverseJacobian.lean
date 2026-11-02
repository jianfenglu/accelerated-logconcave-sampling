import AcceleratedLogConcave.Analysis.Poisson.ReferenceFlow
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Inverse-transpose Jacobian of the reference flow

The matrix coefficient in the transported gradient is the inverse transpose
of the actual spatial derivative. Its derivative follows from the variational
ODE and the symmetry of the Hessian, with no time derivative of the Hessian.
-/
noncomputable section
open InnerProductSpace Set
open scoped Topology NNReal
namespace AcceleratedLogConcave.Analysis.Poisson

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Differentiate an inverse transpose along the genuine variational ODE. -/
theorem hasDerivAt_inverse_adjoint (J : ℝ → E →L[ℝ] E) (t c : ℝ)
    (H : E →L[ℝ] E) (hH : H.IsSymmetric) (e : E ≃L[ℝ] E)
    (he : J t = e.toContinuousLinearMap)
    (hJ : HasDerivAt J (((-c) • H).comp (J t)) t) :
    HasDerivAt (fun s => (Ring.inverse (J s)).adjoint)
      (c • H.comp e.symm.toContinuousLinearMap.adjoint) t := by
  have hi0 : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
        e.symm.toContinuousLinearMap e.symm.toContinuousLinearMap) (J t) := by
    rw [he]
    exact hasFDerivAt_ringInverse (𝕜 := ℝ) e.toUnit
  have hi := hi0.comp_hasDerivAt t hJ
  have ha := ContinuousLinearMap.adjoint.hasFDerivAt.comp_hasDerivAt t hi
  convert ha using 1
  · rfl
  · change c • H.comp e.symm.toContinuousLinearMap.adjoint =
      (-(e.symm.toContinuousLinearMap * (((-c) • H).comp (J t)) *
        e.symm.toContinuousLinearMap)).adjoint
    have halg : -(e.symm.toContinuousLinearMap * (((-c) • H).comp (J t)) *
        e.symm.toContinuousLinearMap) = c • e.symm.toContinuousLinearMap.comp H := by
      ext v
      simp only [he, mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
        neg_apply, smul_apply, ContinuousLinearEquiv.coe_coe, map_smul,
        ContinuousLinearEquiv.apply_symm_apply]
      module
    rw [halg, map_smul, ContinuousLinearMap.adjoint_comp, hH.clm_adjoint_eq]
end Algebra
section Reference
open OAI.LogConcaveSampling.GlobalODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (U : ℝ → E → ℝ) (c : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
  (hU : ∀ t, ContDiff ℝ 2 (U t))
  (hG : Continuous (Function.uncurry (fun t => gradient (U t))))
  (hH : Continuous (Function.uncurry (fun t => hessianOperator (U t))))
  (hc : Continuous c) (C : ℝ≥0)
  (hC : ∀ t ∈ Icc a b, |c t| ≤ C)
  (hlo : ∀ t ∈ Icc a b, ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ (U t)) x v v)
  (hup : ∀ t ∈ Icc a b, ∀ x v, fderiv ℝ (fderiv ℝ (U t)) x v v ≤ ‖v‖ ^ 2)

/-- The actual Jacobian is invertible by uniqueness for its linear ODE. -/
def referenceJacobianEquiv (x : E) (t : Icc a b) : E ≃L[ℝ] E :=
  fundamentalEquiv
    (flowSpatialCoefficient_continuous (D := fun t x => (-c t) • hessianOperator (U t) x) hab (referenceDrift_continuous U c hG hc)
      (fun t ht => referenceDrift_lipschitz U c t (hU t) (hlo t ht) (hup t ht) C (hC t ht))
      ((hc.comp continuous_fst).neg.smul hH) x)
    (flowSpatialCoefficient_bound hab (referenceDrift_continuous U c hG hc)
      (fun t ht => referenceDrift_lipschitz U c t (hU t) (hlo t ht) (hup t ht) C (hC t ht))
      (fun t z => referenceDrift_hasFDerivAt U c t z (hU t)) x)
    ⟨a, le_rfl, hab⟩ t

theorem referenceJacobianEquiv_coe (x : E) (t : Icc a b) :
    (referenceJacobianEquiv U c hab hU hG hH hc C hC hlo hup x t).toContinuousLinearMap =
      referenceJacobian U c hab hU hG hH hc C hC hlo hup x t := rfl

/-- The transported gradient matrix is the inverse transpose of the actual
reference-flow Jacobian. It is defined for all times, with conclusions on the
chosen source interval. -/
def referenceGradientMatrix (t : ℝ) (x : E) : E →L[ℝ] E :=
  (Ring.inverse (referenceJacobian U c hab hU hG hH hc C hC hlo hup x t)).adjoint

theorem referenceGradientMatrix_eq (x : E) (t : Icc a b) :
    referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x =
      (referenceJacobianEquiv U c hab hU hG hH hc C hC hlo hup x t).symm.toContinuousLinearMap.adjoint := by
  rw [referenceGradientMatrix, ← referenceJacobianEquiv_coe,
    ContinuousLinearMap.ringInverse_equiv, ContinuousLinearMap.inverse_equiv]

theorem referenceGradientMatrix_norm_le (x : E) (t : Icc a b) :
    ‖referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x‖ ≤
      Real.exp ((C : ℝ) * |(t : ℝ) - a|) := by
  rw [referenceGradientMatrix_eq, ContinuousLinearMap.adjoint.norm_map]
  let hD := (hc.comp continuous_fst).neg.smul hH
  let hL := fun t ht => referenceDrift_lipschitz U c t (hU t)
    (hlo t ht) (hup t ht) C (hC t ht)
  let hf := fun t z => referenceDrift_hasFDerivAt U c t z (hU t)
  let hA := flowSpatialCoefficient_continuous
    (D := fun t x => (-c t) • hessianOperator (U t) x)
    hab (referenceDrift_continuous U c hG hc) hL hD x
  let hK := flowSpatialCoefficient_bound hab (referenceDrift_continuous U c hG hc) hL hf x
  have heq : (referenceJacobianEquiv U c hab hU hG hH hc C hC hlo hup x t).symm.toContinuousLinearMap =
      fundamental t hA hK a := by ext v; rfl
  rw [heq]
  simpa only [abs_sub_comm] using fundamental_norm_bound t hA hK ⟨a, le_rfl, hab⟩

/-- Pointwise material differentiation of the actual inverse transpose.
The Hessian is evaluated along the flow, not taken after composition. -/
theorem referenceGradientMatrix_hasDerivAt (x : E) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup s x)
      ((c t) • (hessianOperator (U t)
        (referenceFlow U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ x t)).comp
          (referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x)) t := by
  have hj := (referenceJacobian_deriv U c hab hU hG hH hc C hC hlo hup x t
    ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hi := hasDerivAt_inverse_adjoint
    (referenceJacobian U c hab hU hG hH hc C hC hlo hup x) t (c t) _
    (hessianOperator_symmetric (hU t) _)
    (referenceJacobianEquiv U c hab hU hG hH hc C hC hlo hup x ⟨t, ht.1.le, ht.2.le⟩)
    rfl hj
  rw [← referenceGradientMatrix_eq] at hi
  exact hi

/-- Spatial continuity of the genuine inverse-transpose field. -/
theorem referenceGradientMatrix_continuous (t : Icc a b) :
    Continuous (referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t) := by
  have hJ : Continuous (fun x => referenceJacobian U c hab hU hG hH hc C hC hlo hup x t) :=
    flowLinearization_continuous_initial (D := fun t x => (-c t) • hessianOperator (U t) x)
      hab (referenceDrift_continuous U c hG hc)
      (fun t ht => referenceDrift_lipschitz U c t (hU t) (hlo t ht) (hup t ht) C (hC t ht))
      ((hc.comp continuous_fst).neg.smul hH)
      (fun t z => referenceDrift_hasFDerivAt U c t z (hU t)) t
  apply continuous_iff_continuousAt.mpr
  intro x
  have hi := NormedRing.inverse_continuousAt
    (referenceJacobianEquiv U c hab hU hG hH hc C hC hlo hup x t).toUnit
  change ContinuousAt Ring.inverse (referenceJacobian U c hab hU hG hH hc C hC hlo hup x t) at hi
  have hInv : ContinuousAt (fun y => Ring.inverse
      (referenceJacobian U c hab hU hG hH hc C hC hlo hup y t)) x := hi.comp (f := fun y => referenceJacobian U c hab hU hG hH hc C hC hlo hup y t) hJ.continuousAt
  exact ContinuousLinearMap.adjoint.continuousAt.comp hInv

/-- A single spatially uniform bound holds throughout the compact interval. -/
theorem referenceGradientMatrix_uniform_norm_le (x : E) (t : Icc a b) :
    ‖referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x‖ ≤
      Real.exp ((C : ℝ) * (b - a)) := by
  apply (referenceGradientMatrix_norm_le U c hab hU hG hH hc C hC hlo hup x t).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  rw [abs_of_nonneg (sub_nonneg.mpr t.property.1)]
  exact sub_le_sub_right t.property.2 a

/-- Uniform control of the time derivative follows from the actual Hessian
bound and the variational equation; no derivative of the Hessian is needed. -/
theorem referenceGradientMatrix_deriv_norm_le (x : E) (t : ℝ) (ht : t ∈ Ioo a b) :
    ‖deriv (fun s => referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup s x) t‖ ≤
      (C : ℝ) * Real.exp ((C : ℝ) * (b - a)) := by
  rw [(referenceGradientMatrix_hasDerivAt U c hab hU hG hH hc C hC hlo hup x t ht).deriv,
    norm_smul, Real.norm_eq_abs]
  apply mul_le_mul (hC t ⟨ht.1.le, ht.2.le⟩) _ (norm_nonneg _) C.coe_nonneg
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hh : ‖hessianOperator (U t)
      (referenceFlow U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ x t)‖ ≤ 1 := by
    simpa using hessianOperator_norm_le (hU t) (m := 0) (L := 1)
      (by simpa using hlo t ⟨ht.1.le, ht.2.le⟩)
      (by simpa using hup t ⟨ht.1.le, ht.2.le⟩) _
  simpa only [one_mul] using mul_le_mul hh
    (referenceGradientMatrix_uniform_norm_le U c hab hU hG hH hc C hC hlo hup x
      ⟨t, ht.1.le, ht.2.le⟩) (norm_nonneg _) zero_le_one

/-- The pointwise difference quotient bound used for strong L2 differentiation. -/
theorem referenceGradientMatrix_slope_norm_le (x : E) (s t : ℝ)
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    ‖slope (fun r => referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup r x) s t‖ ≤
      (C : ℝ) * Real.exp ((C : ℝ) * (b - a)) := by
  by_cases hst : t = s
  · subst t
    simp only [slope_same, norm_zero]
    positivity
  have hdiff := (convex_Ioo a b).norm_image_sub_le_of_norm_deriv_le
    (fun r hr => (referenceGradientMatrix_hasDerivAt U c hab hU hG hH hc C hC hlo hup x r hr).differentiableAt)
    (fun r hr => referenceGradientMatrix_deriv_norm_le U c hab hU hG hH hc C hC hlo hup x r hr) hs ht
  rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (abs_nonneg _))).trans
  rw [Real.norm_eq_abs]
  have hn : |t - s| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hst)
  exact le_of_eq (by field_simp)
end Reference
end AcceleratedLogConcave.Analysis.Poisson
