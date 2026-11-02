import AcceleratedLogConcave.Analysis.Poisson.ReferenceFamily
import AcceleratedLogConcave.Analysis.Poisson.InverseJacobian
import AcceleratedLogConcave.Analysis.Poisson.TransportedGraph

/-!
# Identifying the reference gradient matrix

The coefficient obtained by differentiating the variational ODE is exactly the
inverse-transpose derivative of the actual reference-flow homeomorphism. This
identifies its multiplier with the coefficient in the transported closed graph.
-/
noncomputable section
open MeasureTheory InnerProductSpace Set Function
open scoped Topology NNReal
namespace AcceleratedLogConcave.Analysis.Poisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (U : ℝ → E → ℝ) (c : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
  (hU : ∀ t, ContDiff ℝ 2 (U t))
  (hG : Continuous (uncurry (fun t => gradient (U t))))
  (hH : Continuous (uncurry (fun t => hessianOperator (U t))))
  (hc : Continuous c) (C : ℝ≥0)
  (hC : ∀ t ∈ Icc a b, |c t| ≤ C)
  (hlo : ∀ t ∈ Icc a b, ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ (U t)) x v v)
  (hup : ∀ t ∈ Icc a b, ∀ x v, fderiv ℝ (fderiv ℝ (U t)) x v v ≤ ‖v‖ ^ 2)

/-- The variational Jacobian is the spatial derivative of the actual flow. -/
theorem referenceFlowHomeomorph_fderiv_eq_referenceJacobian (t : Icc a b) (x : E) :
    fderiv ℝ (referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup
      ⟨a, le_rfl, hab⟩ t) x =
      referenceJacobian U c hab hU hG hH hc C hC hlo hup x t :=
  (referenceFlow_hasFDerivAt U c hab hU hG hH hc C hC hlo hup x t).fderiv

/-- The derivative of the actual inverse flow is the inverse variational Jacobian. -/
theorem referenceFlowHomeomorph_symm_fderiv_eq (t : Icc a b) (x : E) :
    let e := referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup
      ⟨a, le_rfl, hab⟩ t
    fderiv ℝ e.symm (e x) =
      (referenceJacobianEquiv U c hab hU hG hH hc C hC hlo hup x t).symm.toContinuousLinearMap := by
  let e := referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup
    ⟨a, le_rfl, hab⟩ t
  have hf : HasFDerivAt e
      (referenceJacobianEquiv U c hab hU hG hH hc C hC hlo hup x t).toContinuousLinearMap
      (e.symm (e x)) := by
    rw [e.symm_apply_apply]
    exact referenceFlow_hasFDerivAt U c hab hU hG hH hc C hC hlo hup x t
  exact (HasFDerivAt.of_local_left_inverse e.symm.continuous.continuousAt hf
    (Filter.Eventually.of_forall e.apply_symm_apply)).fderiv

/-- The ODE coefficient is the actual inverse-transpose derivative appearing in
transport of the closed weighted gradient. -/
theorem referenceGradientMatrix_eq_inverseFlowDerivative (t : Icc a b) (x : E) :
    let e := referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup
      ⟨a, le_rfl, hab⟩ t
    referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t x =
      (fderiv ℝ e.symm (e x)).adjoint := by
  dsimp only
  rw [referenceFlowHomeomorph_symm_fderiv_eq U c hab hU hG hH hc C hC hlo hup]
  exact referenceGradientMatrix_eq U c hab hU hG hH hc C hC hlo hup x t

variable [MeasurableSpace E] [BorelSpace E]

/-- Equality of the bounded multipliers, with the actual flow and its proved
uniform inverse derivative bound. -/
theorem referenceFlow_inverseJacobianMultiplier_eq (μ : Measure E) (t : Icc a b) :
    inverseJacobianMultiplier μ
      (referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ t)
      (referenceFlowHomeomorph_symm_contDiff U c hab hU hG hH hc C hC hlo hup ⟨a, le_rfl, hab⟩ t)
      (Real.exp ((C : ℝ) * (b - a)))
      (referenceFlowHomeomorph_symm_fderiv_bound U c hU hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ t) =
    fieldMultiplier μ (referenceGradientMatrix U c hab hU hG hH hc C hC hlo hup t)
      (referenceGradientMatrix_continuous U c hab hU hG hH hc C hC hlo hup t)
      (Real.exp ((C : ℝ) * (b - a)))
      (fun x => referenceGradientMatrix_uniform_norm_le U c hab hU hG hH hc C hC hlo hup x t) := by
  unfold inverseJacobianMultiplier
  congr 1
  funext x
  exact (referenceGradientMatrix_eq_inverseFlowDerivative U c hab hU hG hH hc C hC hlo hup t x).symm

end AcceleratedLogConcave.Analysis.Poisson
