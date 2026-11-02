import AcceleratedLogConcave.Conditional.Stein.JacobianODE

/-! Actual inverse-flow Jacobian for an arbitrary reference time in the slab.
This generalizes the pinned JacobianODE supplier from terminal endpoint b to
an arbitrary fixed w. The construction interval and the reference time are
separate, as required by the enlarged positive-variance warm extension. -/

noncomputable section
set_option maxHeartbeats 1600000
open Set Function
open scoped Topology NNReal

namespace OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E] {a b : ℝ} (hab : a ≤ b)
  {f : ℝ → E → E} (hc : Continuous (uncurry f))
  {K : ℝ≥0} (hL : ∀ t ∈ Icc a b, LipschitzWith K (f t))
  {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
  (hf : ∀ t z, HasFDerivAt (f t) (D t z) z)

/-- Actual spatial derivative of transport to a fixed reference time, evaluated
along the actual reference-started trajectory. -/
def flowReferenceJacobian (w : Icc a b) (t : ℝ) (y : E) : E →L[ℝ] E :=
  fderiv ℝ (fun z => flow hL hc (projIcc a b hab t) z w)
    (flow hL hc w y (projIcc a b hab t))

omit [ProperSpace E] in
/-- The reference time need not be an endpoint for the Jacobian to be the identity. -/
@[simp] theorem flowReferenceJacobian_reference (w : Icc a b) (y : E) :
    flowReferenceJacobian hab hc hL w w y = ContinuousLinearMap.id ℝ E := by
  have he : (fun z => flow hL hc w z w) = id := by
    funext z
    exact flow_initial hL hc w z
  simp only [flowReferenceJacobian, projIcc_of_mem hab w.2, he, fderiv_id]

omit [ProperSpace E] in
/-- Stability of the actual transport bounds its actual spatial derivative,
uniformly in the initial spatial input. -/
theorem norm_flowReferenceJacobian_le (w : Icc a b) (t : ℝ) (y : E) :
    ‖flowReferenceJacobian hab hc hL w t y‖ ≤
      Real.exp ((K : ℝ) * |(w : ℝ) - (projIcc a b hab t : ℝ)|) :=
  norm_fderiv_le_of_lipschitz ℝ (flow_lipschitz hL hc (projIcc a b hab t) w)

omit [ProperSpace E] in
/-- One zeroth-order bound holds across the whole slab in either time orientation. -/
theorem norm_flowReferenceJacobian_uniform_le (w : Icc a b) (t : ℝ) (y : E) :
    ‖flowReferenceJacobian hab hc hL w t y‖ ≤ Real.exp ((K : ℝ) * (b - a)) := by
  apply (norm_flowReferenceJacobian_le hab hc hL w t y).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  rw [abs_le]
  constructor <;> linarith [w.2.1, w.2.2, (projIcc a b hab t).2.1,
    (projIcc a b hab t).2.2]

include hD hf in
theorem flowReferenceJacobian_eq_fundamental (w t : Icc a b) (y : E) :
    flowReferenceJacobian hab hc hL w t y =
      (flowLinearization hab hc hL hD hf (flow hL hc w y a) w).comp
        (inverseFundamental
          (flowSpatialCoefficient_continuous hab hc hL hD
            (flow hL hc w y a))
          (flowSpatialCoefficient_bound hab hc hL hf
            (flow hL hc w y a)) ⟨a, le_rfl, hab⟩ t) := by
  let s : Icc a b := ⟨a, le_rfl, hab⟩
  let z := flow hL hc w y a
  let J := flowLinearization hab hc hL hD hf z
  have hz : flow hL hc s z t = flow hL hc w y t :=
    flow_cocycle hL hc w s t y
  have ht := ((flow_contDiff_one hab hc hL hD hf t w).differentiable_one
    (flow hL hc s z t)).hasFDerivAt
  have hd := ht.comp z (flow_hasFDerivAt_left hab hc hL hD hf z t)
  have hfun : (fun q => flow hL hc t (flow hL hc s q t) w) =
      (fun q => flow hL hc s q w) := by
    funext q
    exact flow_cocycle hL hc s t w q
  change HasFDerivAt (fun q => flow hL hc t (flow hL hc s q t) w) _ z at hd
  rw [hfun] at hd
  have heq := hd.unique (flow_hasFDerivAt_left hab hc hL hD hf z w)
  have he : (flowReferenceJacobian hab hc hL w t y).comp (J t) = J w := by
    simpa only [flowReferenceJacobian, projIcc_of_mem hab t.2, hz, J] using heq
  change flowReferenceJacobian hab hc hL w t y = (J w).comp _
  rw [inverseFundamental_eq]
  ext v
  have hh := congrArg (fun T : E →L[ℝ] E => T
    (fundamental t
      (flowSpatialCoefficient_continuous hab hc hL hD z)
      (flowSpatialCoefficient_bound hab hc hL hf z) s v)) he
  dsimp only [ContinuousLinearMap.comp_apply] at hh ⊢
  change _ = J w _
  rw [show J t = fundamental s
    (flowSpatialCoefficient_continuous hab hc hL hD z)
    (flowSpatialCoefficient_bound hab hc hL hf z) t from rfl,
    fundamental_cocycle, fundamental_apply_initial] at hh
  exact hh

include hD hf in
/-- The actual inverse-flow Jacobian obeys the backward variational equation.
The order is `B Df`, rather than the forward equation's `Df B`. -/
theorem flowReferenceJacobian_deriv (w : Icc a b) {t : ℝ} (ht : t ∈ Icc a b) (y : E) :
    HasDerivWithinAt (fun u => flowReferenceJacobian hab hc hL w u y)
      (-(flowReferenceJacobian hab hc hL w t y).comp
        (D t (flow hL hc w y t))) (Icc a b) t := by
  let s : Icc a b := ⟨a, le_rfl, hab⟩
  let z := flow hL hc w y a
  let hA := flowSpatialCoefficient_continuous hab hc hL hD z
  let hK := flowSpatialCoefficient_bound hab hc hL hf z
  let J := flowLinearization hab hc hL hD hf z
  let C := inverseFundamental hA hK s
  have heq (u : ℝ) (hu : u ∈ Icc a b) :
      flowReferenceJacobian hab hc hL w u y = (J w).comp (C u) :=
    flowReferenceJacobian_eq_fundamental hab hc hL hD hf w ⟨u, hu⟩ y
  have hd := (hasDerivWithinAt_const t (Icc a b) (J w)).clm_comp
    (inverseFundamental_deriv hA hK s ht)
  have hh := hd.congr_of_mem heq ht
  have hAeq : flowSpatialCoefficient hab hc hL (D := D) z t =
      D t (flow hL hc w y t) := by
    dsimp only [flowSpatialCoefficient, z]
    rw [flow_cocycle hL hc w s ⟨t, ht⟩ y]
  convert hh using 1
  rw [ContinuousLinearMap.zero_comp, zero_add, ContinuousLinearMap.comp_neg,
    ← ContinuousLinearMap.comp_assoc, ← heq t ht, hAeq]

include hD hf in
/-- Joint continuity of the actual backward Jacobian follows from the joint
fundamental matrix and continuous inversion of its proved linear equivalence. -/
theorem flowReferenceJacobian_joint_continuous (w : Icc a b) :
    Continuous (fun p : E × Icc a b => flowReferenceJacobian hab hc hL w p.2 p.1) := by
  let Z (y : E) := flow hL hc w y a
  have hZ : Continuous Z := (flow_lipschitz hL hc w ⟨a, le_rfl, hab⟩).continuous
  have hJ : Continuous (fun p : E × Icc a b => flowLinearization hab hc hL hD hf (Z p.1) p.2) :=
    (flowLinearization_joint_continuous hab hc hL hD hf).comp
      ((hZ.comp continuous_fst).prodMk continuous_snd)
  have hJb : Continuous (fun p : E × Icc a b => flowLinearization hab hc hL hD hf (Z p.1) w) :=
    (flowLinearization_continuous_initial hab hc hL hD hf w).comp
      (hZ.comp continuous_fst)
  have hi : Continuous (fun p : E × Icc a b =>
      Ring.inverse (flowLinearization hab hc hL hD hf (Z p.1) p.2)) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hinv : ContinuousAt (Ring.inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
        (flowLinearization hab hc hL hD hf (Z p.1) p.2) :=
      NormedRing.inverse_continuousAt (fundamentalEquiv
        (flowSpatialCoefficient_continuous hab hc hL hD (Z p.1))
        (flowSpatialCoefficient_bound hab hc hL hf (Z p.1))
        ⟨a, le_rfl, hab⟩ p.2).toUnit
    exact ContinuousAt.comp (f := fun q : E × Icc a b =>
      flowLinearization hab hc hL hD hf (Z q.1) q.2) (g := Ring.inverse) (x := p)
      hinv hJ.continuousAt
  exact (hJb.clm_comp hi).congr fun p =>
    (flowReferenceJacobian_eq_fundamental hab hc hL hD hf w p.2 p.1).symm

end OAI.LogConcaveSampling.GlobalODE
