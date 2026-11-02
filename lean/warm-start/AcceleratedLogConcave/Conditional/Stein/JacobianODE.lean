import AcceleratedLogConcave.Conditional.Stein.InverseFundamental
import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransportFlow

/-! # The backward Jacobian of a constructed complete flow

The time equation is obtained from the actual spatial derivative by the
cocycle identity and inverse differentiation of its fundamental matrix.
-/

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

/-- Actual spatial derivative of transport to the terminal time, evaluated
along the actual backward trajectory. -/
def flowBackwardJacobian (t : ℝ) (y : E) : E →L[ℝ] E :=
  fderiv ℝ (fun z => flow hL hc (projIcc a b hab t) z b)
    (flow hL hc ⟨b, hab, le_rfl⟩ y (projIcc a b hab t))

include hD hf in
theorem flowBackwardJacobian_eq_fundamental (t : Icc a b) (y : E) :
    flowBackwardJacobian hab hc hL t y =
      (flowLinearization hab hc hL hD hf (flow hL hc ⟨b, hab, le_rfl⟩ y a) b).comp
        (inverseFundamental
          (flowSpatialCoefficient_continuous hab hc hL hD
            (flow hL hc ⟨b, hab, le_rfl⟩ y a))
          (flowSpatialCoefficient_bound hab hc hL hf
            (flow hL hc ⟨b, hab, le_rfl⟩ y a)) ⟨a, le_rfl, hab⟩ t) := by
  let s : Icc a b := ⟨a, le_rfl, hab⟩
  let w : Icc a b := ⟨b, hab, le_rfl⟩
  let z := flow hL hc w y a
  let J := flowLinearization hab hc hL hD hf z
  have hz : flow hL hc s z t = flow hL hc w y t :=
    flow_cocycle hL hc w s t y
  have ht := ((flow_contDiff_one hab hc hL hD hf t w).differentiable_one
    (flow hL hc s z t)).hasFDerivAt
  have hd := ht.comp z (flow_hasFDerivAt_left hab hc hL hD hf z t)
  have hfun : (fun q => flow hL hc t (flow hL hc s q t) b) =
      (fun q => flow hL hc s q b) := by
    funext q
    exact flow_cocycle hL hc s t w q
  change HasFDerivAt (fun q => flow hL hc t (flow hL hc s q t) b) _ z at hd
  rw [hfun] at hd
  have heq := hd.unique (flow_hasFDerivAt_left hab hc hL hD hf z w)
  have he : (flowBackwardJacobian hab hc hL t y).comp (J t) = J b := by
    simpa only [flowBackwardJacobian, projIcc_of_mem hab t.2, hz, J] using heq
  change flowBackwardJacobian hab hc hL t y = (J b).comp _
  rw [inverseFundamental_eq]
  ext v
  have hh := congrArg (fun T : E →L[ℝ] E => T
    (fundamental t
      (flowSpatialCoefficient_continuous hab hc hL hD z)
      (flowSpatialCoefficient_bound hab hc hL hf z) s v)) he
  dsimp only [ContinuousLinearMap.comp_apply] at hh ⊢
  change _ = J b _
  rw [show J t = fundamental s
    (flowSpatialCoefficient_continuous hab hc hL hD z)
    (flowSpatialCoefficient_bound hab hc hL hf z) t from rfl,
    fundamental_cocycle, fundamental_apply_initial] at hh
  exact hh

include hD hf in
/-- The actual inverse-flow Jacobian obeys the backward variational equation.
The order is `B Df`, rather than the forward equation's `Df B`. -/
theorem flowBackwardJacobian_deriv {t : ℝ} (ht : t ∈ Icc a b) (y : E) :
    HasDerivWithinAt (fun u => flowBackwardJacobian hab hc hL u y)
      (-(flowBackwardJacobian hab hc hL t y).comp
        (D t (flow hL hc ⟨b, hab, le_rfl⟩ y t))) (Icc a b) t := by
  let s : Icc a b := ⟨a, le_rfl, hab⟩
  let w : Icc a b := ⟨b, hab, le_rfl⟩
  let z := flow hL hc w y a
  let hA := flowSpatialCoefficient_continuous hab hc hL hD z
  let hK := flowSpatialCoefficient_bound hab hc hL hf z
  let J := flowLinearization hab hc hL hD hf z
  let C := inverseFundamental hA hK s
  have heq (u : ℝ) (hu : u ∈ Icc a b) :
      flowBackwardJacobian hab hc hL u y = (J b).comp (C u) :=
    flowBackwardJacobian_eq_fundamental hab hc hL hD hf ⟨u, hu⟩ y
  have hd := (hasDerivWithinAt_const t (Icc a b) (J b)).clm_comp
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
theorem flowBackwardJacobian_joint_continuous :
    Continuous (fun p : E × Icc a b => flowBackwardJacobian hab hc hL p.2 p.1) := by
  let Z (y : E) := flow hL hc ⟨b, hab, le_rfl⟩ y a
  have hZ : Continuous Z := (flow_lipschitz hL hc ⟨b, hab, le_rfl⟩ ⟨a, le_rfl, hab⟩).continuous
  have hJ : Continuous (fun p : E × Icc a b => flowLinearization hab hc hL hD hf (Z p.1) p.2) :=
    (flowLinearization_joint_continuous hab hc hL hD hf).comp
      ((hZ.comp continuous_fst).prodMk continuous_snd)
  have hJb : Continuous (fun p : E × Icc a b => flowLinearization hab hc hL hD hf (Z p.1) b) :=
    (flowLinearization_continuous_initial hab hc hL hD hf ⟨b, hab, le_rfl⟩).comp
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
    (flowBackwardJacobian_eq_fundamental hab hc hL hD hf p.2 p.1).symm

end OAI.LogConcaveSampling.GlobalODE
