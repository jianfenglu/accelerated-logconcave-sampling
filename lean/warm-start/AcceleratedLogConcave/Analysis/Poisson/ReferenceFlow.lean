import AcceleratedLogConcave.External.OAI.GlobalODE
import AcceleratedLogConcave.Analysis.Poisson.HessianMultiplier

/-!
# The actual gradient reference flow

The drift is `-c(t) ∇U_t`, not an arbitrary supplied flow. The Hessian bounds
prove its spatial Lipschitz estimate, from which global existence on each
compact time interval, uniqueness, and an invertible flow are constructed.
Transport of the reference measure is a further theorem, not assumed by this
construction and not asserted here.
-/

noncomputable section
open InnerProductSpace Set
open scoped Topology NNReal

namespace AcceleratedLogConcave.Analysis.Poisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem gradient_lipschitz_of_unit_hessian {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ V) x v v ≤ ‖v‖ ^ 2) :
    LipschitzWith 1 (gradient V) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  obtain ⟨_, heq, _, _, hn⟩ :=
    AutoSamplingTheory.TechnicalLemmas.Analysis.HessianSecantOperator.hessian_secant_operator
      (α := 0) (β := 1) hV (by simpa using hlo) (by simpa using hup) x y
  rw [heq]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg (x - y))

/-- The reference velocity in the manuscript. -/
def referenceDrift (U : ℝ → E → ℝ) (c : ℝ → ℝ) (t : ℝ) (x : E) : E :=
  (-c t) • gradient (U t) x

theorem referenceDrift_continuous (U : ℝ → E → ℝ) (c : ℝ → ℝ)
    (hG : Continuous (Function.uncurry (fun t => gradient (U t))))
    (hc : Continuous c) : Continuous (Function.uncurry (referenceDrift U c)) :=
  (hc.comp continuous_fst).neg.smul hG

theorem referenceDrift_lipschitz (U : ℝ → E → ℝ) (c : ℝ → ℝ) (t : ℝ)
    (hU : ContDiff ℝ 2 (U t))
    (hlo : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ (U t)) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ (U t)) x v v ≤ ‖v‖ ^ 2)
    (C : ℝ≥0) (hC : |c t| ≤ C) : LipschitzWith C (referenceDrift U c t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hg := (gradient_lipschitz_of_unit_hessian hU hlo hup).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hg
  simp only [dist_eq_norm, referenceDrift, ← smul_sub, norm_smul,
    norm_neg, Real.norm_eq_abs]
  exact mul_le_mul hC hg (norm_nonneg _) C.coe_nonneg

section Flow
variable (U : ℝ → E → ℝ) (c : ℝ → ℝ) {a b : ℝ}
  (hU : ∀ t ∈ Icc a b, ContDiff ℝ 2 (U t))
  (hG : Continuous (Function.uncurry (fun t => gradient (U t))))
  (hc : Continuous c) (C : ℝ≥0)
  (hC : ∀ t ∈ Icc a b, |c t| ≤ C)
  (hlo : ∀ t ∈ Icc a b, ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ (U t)) x v v)
  (hup : ∀ t ∈ Icc a b, ∀ x v, fderiv ℝ (fderiv ℝ (U t)) x v v ≤ ‖v‖ ^ 2)

/-- The actual globally defined trajectory on the chosen compact time interval. -/
def referenceFlow (s : Icc a b) (x : E) : ℝ → E :=
  OAI.LogConcaveSampling.GlobalODE.flow
    (fun t ht => referenceDrift_lipschitz U c t (hU t ht) (hlo t ht) (hup t ht) C (hC t ht))
    (referenceDrift_continuous U c hG hc) s x

theorem referenceFlow_initial (s : Icc a b) (x : E) :
    referenceFlow U c hU hG hc C hC hlo hup s x s = x :=
  OAI.LogConcaveSampling.GlobalODE.flow_initial _ _ _ _

theorem referenceFlow_continuous (s : Icc a b) (x : E) :
    Continuous (referenceFlow U c hU hG hc C hC hlo hup s x) :=
  OAI.LogConcaveSampling.GlobalODE.flow_continuous _ _ _ _

theorem referenceFlow_deriv (s : Icc a b) (x : E) (t : ℝ) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (referenceFlow U c hU hG hc C hC hlo hup s x)
      (referenceDrift U c t (referenceFlow U c hU hG hc C hC hlo hup s x t))
      (Icc a b) t :=
  OAI.LogConcaveSampling.GlobalODE.flow_deriv _ _ _ _ t ht

/-- Invertibility comes from uniqueness of the actual ODE in both directions. -/
def referenceFlowHomeomorph (s t : Icc a b) : E ≃ₜ E :=
  OAI.LogConcaveSampling.GlobalODE.flowHomeomorph
    (fun t ht => referenceDrift_lipschitz U c t (hU t ht) (hlo t ht) (hup t ht) C (hC t ht))
    (referenceDrift_continuous U c hG hc) s t

theorem referenceFlowHomeomorph_apply (s t : Icc a b) (x : E) :
    referenceFlowHomeomorph U c hU hG hc C hC hlo hup s t x =
      referenceFlow U c hU hG hc C hC hlo hup s x t := rfl

end Flow

/-- The derivative of the genuine gradient is the Riesz Hessian. -/
theorem gradient_hasFDerivAt_hessian {V : E → ℝ} (hV : ContDiff ℝ 2 V) (x : E) :
    HasFDerivAt (gradient V) (hessianOperator V x) x := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  exact ((toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).comp
    x (hfd.differentiable_one x).hasFDerivAt

/-- The true spatial derivative of the reference drift. -/
theorem referenceDrift_hasFDerivAt (U : ℝ → E → ℝ) (c : ℝ → ℝ) (t x)
    (hU : ContDiff ℝ 2 (U t)) :
    HasFDerivAt (referenceDrift U c t) ((-c t) • hessianOperator (U t) x) x :=
  (gradient_hasFDerivAt_hessian hU x).const_smul (-c t)

variable (U : ℝ → E → ℝ) (c : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
  (hU : ∀ t, ContDiff ℝ 2 (U t))
  (hG : Continuous (Function.uncurry (fun t => gradient (U t))))
  (hH : Continuous (Function.uncurry (fun t => hessianOperator (U t))))
  (hc : Continuous c) (C : ℝ≥0)
  (hC : ∀ t ∈ Icc a b, |c t| ≤ C)
  (hlo : ∀ t ∈ Icc a b, ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ (U t)) x v v)
  (hup : ∀ t ∈ Icc a b, ∀ x v, fderiv ℝ (fderiv ℝ (U t)) x v v ≤ ‖v‖ ^ 2)

/-- Spatial linearization of the actual reference flow from the left endpoint.
This globally defined family API can be applied to a time-clamped potential. -/
def referenceJacobian (x : E) : ℝ → E →L[ℝ] E :=
  OAI.LogConcaveSampling.GlobalODE.flowLinearization
    (D := fun t x => (-c t) • hessianOperator (U t) x) hab
    (referenceDrift_continuous U c hG hc)
    (fun t ht => referenceDrift_lipschitz U c t (hU t) (hlo t ht) (hup t ht) C (hC t ht))
    ((hc.comp continuous_fst).neg.smul hH)
    (fun t x => referenceDrift_hasFDerivAt U c t x (hU t)) x

theorem referenceFlow_hasFDerivAt (x : E) (t : Icc a b) :
    HasFDerivAt
      (fun z => referenceFlow U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ z t)
      (referenceJacobian U c hab hU hG hH hc C hC hlo hup x t) x :=
  OAI.LogConcaveSampling.GlobalODE.flow_hasFDerivAt_left
    (D := fun t x => (-c t) • hessianOperator (U t) x) hab
    (referenceDrift_continuous U c hG hc)
    (fun t ht => referenceDrift_lipschitz U c t (hU t) (hlo t ht) (hup t ht) C (hC t ht))
    ((hc.comp continuous_fst).neg.smul hH)
    (fun t x => referenceDrift_hasFDerivAt U c t x (hU t)) x t

/-- The variational equation uses the actual Hessian evaluated on the trajectory. -/
theorem referenceJacobian_deriv (x : E) (t : ℝ) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (referenceJacobian U c hab hU hG hH hc C hC hlo hup x)
      (((-c t) • hessianOperator (U t)
          (referenceFlow U c (fun t _ => hU t) hG hc C hC hlo hup ⟨a, le_rfl, hab⟩ x t)).comp
        (referenceJacobian U c hab hU hG hH hc C hC hlo hup x t))
      (Icc a b) t := by
  let hL := fun t ht => referenceDrift_lipschitz U c t (hU t)
    (hlo t ht) (hup t ht) C (hC t ht)
  have hD : Continuous (Function.uncurry (fun t x => (-c t) • hessianOperator (U t) x)) :=
    (hc.comp continuous_fst).neg.smul hH
  exact OAI.LogConcaveSampling.GlobalODE.fundamental_deriv ⟨a, le_rfl, hab⟩
    (OAI.LogConcaveSampling.GlobalODE.flowSpatialCoefficient_continuous hab
      (referenceDrift_continuous U c hG hc) hL hD x)
    (OAI.LogConcaveSampling.GlobalODE.flowSpatialCoefficient_bound hab
      (referenceDrift_continuous U c hG hc) hL
      (fun t z => referenceDrift_hasFDerivAt U c t z (hU t)) x) t ht

end AcceleratedLogConcave.Analysis.Poisson
