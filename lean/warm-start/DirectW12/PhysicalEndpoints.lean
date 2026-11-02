import DirectW12.PhysicalInterior
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Locally checked against existing cached dependencies; independent replay pending.
Genuine closed-clock coefficients and weak inverses.
No auxiliary identity extension is used at either endpoint. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory InnerProductSpace Set Function Filter
open scoped Topology NNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
open WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (P : ReferencePoissonFamily E a b)

/-- The actual inverse-transpose coefficient, with only a clamped time extension. -/
def closedMatrix (t : ℝ) (x : E) : E →L[ℝ] E :=
  referenceGradientMatrix P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper (projIcc a b P.ordered t) x

theorem closedMatrix_continuous (t : ℝ) : Continuous (P.closedMatrix t) :=
  referenceGradientMatrix_continuous P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper (projIcc a b P.ordered t)

theorem closedMatrix_norm_le (t : ℝ) (x : E) :
    ‖P.closedMatrix t x‖ ≤ P.jacobianBound :=
  referenceGradientMatrix_uniform_norm_le P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper x (projIcc a b P.ordered t)

/-- Continuity in time at the actual physical endpoints follows from the
variational Jacobian and inversion at its proved unit, not from interior limits
of the artificial identity-extended coefficient. -/
theorem physicalMatrix_continuousOn (x : E) :
    ContinuousOn (fun t => referenceGradientMatrix P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper t x) (Icc a b) := by
  intro t ht
  have hJ := (referenceJacobian_deriv P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper x t ht).continuousWithinAt
  have hi := NormedRing.inverse_continuousAt
    (referenceJacobianEquiv P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper x ⟨t,ht⟩).toUnit
  change ContinuousAt Ring.inverse (referenceJacobian P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper x t) at hi
  exact ContinuousLinearMap.adjoint.continuousAt.comp_continuousWithinAt
    (hi.comp_continuousWithinAt hJ)

/-- The derivative bound extends to the closed interval by actual continuity.
The degenerate interval is treated separately. -/
theorem physicalMatrix_lipschitz (x : E) :
    LipschitzOnWith ⟨(P.scaleBound : ℝ) * P.jacobianBound,
      mul_nonneg P.scaleBound.coe_nonneg P.jacobianBound_pos.le⟩
      (fun t => referenceGradientMatrix P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper t x) (Icc a b) := by
  by_cases hab : a < b
  · have hi : LipschitzOnWith
        ⟨(P.scaleBound : ℝ) * P.jacobianBound,
          mul_nonneg P.scaleBound.coe_nonneg P.jacobianBound_pos.le⟩
        (fun t => referenceGradientMatrix P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper t x) (Ioo a b) :=
      (convex_Ioo a b).lipschitzOnWith_of_nnnorm_deriv_le
        (fun t ht => (referenceGradientMatrix_hasDerivAt P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper x t ht).differentiableAt)
        (fun t ht => referenceGradientMatrix_deriv_norm_le P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper x t ht)
    have hc : ContinuousOn (fun t => referenceGradientMatrix P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper t x)
        (closure (Ioo a b)) := by
      simpa only [closure_Ioo hab.ne] using P.physicalMatrix_continuousOn x
    simpa only [closure_Ioo hab.ne] using LipschitzOnWith.closure hc hi
  · have he : a = b := le_antisymm P.ordered (not_lt.mp hab)
    subst b
    intro s hs t ht
    have hs' : s = a := le_antisymm hs.2 hs.1
    have ht' : t = a := le_antisymm ht.2 ht.1
    subst s; subst t
    simp

theorem closedMatrix_sub_norm_le (s t : ℝ) (x : E) :
    ‖P.closedMatrix t x - P.closedMatrix s x‖ ≤
      ((P.scaleBound : ℝ) * P.jacobianBound) * ‖t - s‖ := by
  have hi := (P.physicalMatrix_lipschitz x).dist_le_mul
    _ (projIcc a b P.ordered t).property _ (projIcc a b P.ordered s).property
  have hp := (LipschitzWith.projIcc P.ordered).dist_le_mul t s
  simp only [NNReal.coe_one, one_mul] at hp
  calc
    _ ≤ ((P.scaleBound : ℝ) * P.jacobianBound) *
        dist (projIcc a b P.ordered t) (projIcc a b P.ordered s) := by
      change dist (P.closedMatrix t x) (P.closedMatrix s x) ≤
        ((P.scaleBound : ℝ) * P.jacobianBound) *
          dist (projIcc a b P.ordered t : ℝ) (projIcc a b P.ordered s : ℝ) at hi
      rw [dist_eq_norm] at hi
      exact hi
    _ ≤ _ := mul_le_mul_of_nonneg_left hp
      (mul_nonneg P.scaleBound.coe_nonneg P.jacobianBound_pos.le)

theorem closedMatrix_slope_norm_le (s t : ℝ) (x : E) :
    ‖slope (fun r => P.closedMatrix r x) s t‖ ≤
      (P.scaleBound : ℝ) * P.jacobianBound := by
  by_cases h : t = s
  · subst t
    simpa only [slope_same, norm_zero] using
      mul_nonneg P.scaleBound.coe_nonneg P.jacobianBound_pos.le
  rw [slope_def_module, norm_smul, norm_inv]
  apply (mul_le_mul_of_nonneg_left (P.closedMatrix_sub_norm_le s t x)
    (inv_nonneg.mpr (norm_nonneg _))).trans
  exact le_of_eq (by
    rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)), mul_one])

/-- Bounded multiplication by the genuine A = DΦ⁻ᵀ at all closed times. -/
def closedCoefficient (t : ℝ) : Lp E 2 (P.law a) →L[ℝ] Lp E 2 (P.law a) :=
  fieldMultiplier (P.law a) (P.closedMatrix t) (P.closedMatrix_continuous t)
    P.jacobianBound (P.closedMatrix_norm_le t)

theorem closedCoefficient_eq_transport (t : Icc a b) :
    P.closedCoefficient t = inverseJacobianMultiplier (P.law a)
      (P.flow t) (P.flow_symm_C1 t) P.jacobianBound (P.flow_symm_fderiv_bound t) := by
  have h := referenceFlow_inverseJacobianMultiplier_eq P.potential P.scale P.ordered P.potential_C2
    P.gradient_continuous P.hessian_continuous P.scale_continuous P.scaleBound
    P.scale_bounded P.hessian_nonneg P.hessian_upper (P.law a) t
  change inverseJacobianMultiplier (P.law a) (P.flow t) (P.flow_symm_C1 t)
    P.jacobianBound (P.flow_symm_fderiv_bound t) = _ at h
  rw [h]
  unfold closedCoefficient
  congr 1
  funext x
  unfold closedMatrix
  rw [projIcc_of_mem P.ordered t.property]

def closedMovingGradient (t : ℝ) : P.Graph →L[ℝ] Lp E 2 (P.law a) :=
  (P.closedCoefficient t).comp P.baseGradient

theorem closedMovingGradient_coercive (t : ℝ) (u : P.Graph) :
    P.coercivity * ‖u‖ ^ 2 ≤ ‖P.closedMovingGradient t u‖ ^ 2 := by
  let r := projIcc a b P.ordered t
  have hp (v : P.referenceClosedGradient.domain) (hv : mean (P.law a) v = 0) :
      P.lower a * ‖(v : Lp ℝ 2 (P.law a))‖ ^ 2 ≤ ‖P.referenceClosedGradient v‖ ^ 2 :=
    Gibbs.closedGradient_poincare (P.law a) (P.potential a) (P.potential_C2 a)
      (P.integrable a P.leftTime.property) (P.gibbs_law a P.leftTime.property)
      (P.lower a) 1 (P.lower_pos a P.leftTime.property)
      (P.hessian_lower a P.leftTime.property)
      (by simpa only [one_mul] using P.hessian_upper a P.leftTime.property) v
      ((mean_apply (P.law a) v).symm.trans hv)
  have hcoef : P.closedCoefficient t = P.closedCoefficient r := by
    unfold closedCoefficient
    congr 1
    funext x
    simp only [closedMatrix, r,
      projIcc_of_mem P.ordered (projIcc a b P.ordered t).property]
  unfold closedMovingGradient
  rw [hcoef, P.closedCoefficient_eq_transport r]
  exact referenceGraph_multiplier_coercive _ _ (P.lower_pos a P.leftTime.property)
    P.jacobianBound_pos hp _
    (jacobianAdjointMultiplier (P.law a) (P.flow r) (P.flow_C1 r)
      P.jacobianBound (P.flow_fderiv_bound r))
    (jacobian_inverseJacobianMultiplier _ _ _ _ _ _ _ _)
    (jacobianAdjointMultiplier_norm_le _ _ _ _ _) u

theorem closedMovingGradient_continuousAt (t : ℝ) :
    ContinuousAt P.closedMovingGradient t := by
  have hc : ContinuousAt P.closedCoefficient t :=
    continuousAt_fieldMultiplier_of_quotient_bound (P.law a) P.closedMatrix
      P.closedMatrix_continuous (fun _ => P.jacobianBound) P.closedMatrix_norm_le
      t ((P.scaleBound : ℝ) * P.jacobianBound)
      (Eventually.of_forall fun s x => P.closedMatrix_slope_norm_le t s x)
  exact hc.clm_comp continuousAt_const

theorem closedEnergy_continuousAt (t : ℝ) :
    ContinuousAt (fun s => MovingForms.energyCoefficient (P.closedMovingGradient s)) t := by
  have he (s : ℝ) := energyCoefficient_fieldMultiplier (P.law a)
    (P.closedMatrix s) (P.closedMatrix_continuous s) P.jacobianBound
    (P.closedMatrix_norm_le s) P.baseGradient
  simp_rw [closedMovingGradient, closedCoefficient, he]
  exact continuousAt_const.clm_comp
    ((continuousAt_energyFieldMultiplier (P.law a) P.closedMatrix
      P.closedMatrix_continuous P.jacobianBound P.closedMatrix_norm_le t
      ((P.scaleBound : ℝ) * P.jacobianBound)
      (Eventually.of_forall fun s x => P.closedMatrix_slope_norm_le t s x)).clm_comp
        continuousAt_const)

/-- Constructed from the fixed closed graph and its genuine transported form. -/
def closedGradientInverse (t : ℝ) : Lp ℝ 2 (P.law a) →L[ℝ] Lp E 2 (P.law a) :=
  (P.closedMovingGradient t).comp ((MovingForms.coerciveInverse
    (MovingForms.energyCoefficient (P.closedMovingGradient t)) P.coercivity_pos
    (MovingForms.energyCoefficient_coercive _ (P.closedMovingGradient_coercive t))).comp
      P.inclusion.adjoint)

theorem closedGradientInverse_continuous : Continuous P.closedGradientInverse := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (P.closedMovingGradient_continuousAt t).clm_comp
    ((MovingForms.continuousAt_coerciveInverse
      (fun s => MovingForms.energyCoefficient (P.closedMovingGradient s))
      P.coercivity_pos
      (fun s => MovingForms.energyCoefficient_coercive _ (P.closedMovingGradient_coercive s))
      (P.closedEnergy_continuousAt t)).clm_comp continuousAt_const)

/-- The physical inverse identification has no interior restriction. It uses
closed-domain change of variables and weak-form uniqueness at this exact time. -/
theorem closedGradientInverse_eq_physical (t : Icc a b) (g : Lp ℝ 2 (P.law a)) :
    P.closedGradientInverse t g = P.physicalGradientPullback t g := by
  have heq := commonDomainSolution_gradient_eq_pullback_gradientInverse
    (P.law a) (P.law t) (P.potential a) (P.potential t)
    ((P.potential_C2 a).of_le (by norm_num)) ((P.potential_C2 t).of_le (by norm_num))
    (P.integrable a P.leftTime.property) (P.integrable t t.property)
    (P.gibbs_law a P.leftTime.property) (P.gibbs_law t t.property)
    (P.flow t) (P.flow_measurePreserving t)
    (P.flow_C1 t) (P.flow_symm_C1 t) P.jacobianBound P.jacobianBound
    (P.flow_fderiv_bound t) (P.flow_symm_fderiv_bound t) (P.potential_C2 a) (P.potential_C2 t)
    (P.lower a) 1 (P.lower t) 1 (P.lower_pos a P.leftTime.property)
    (P.lower_pos t t.property) P.jacobianBound_pos
    (P.hessian_lower a P.leftTime.property)
    (by simpa only [one_mul] using P.hessian_upper a P.leftTime.property)
    (P.hessian_lower t t.property)
    (by simpa only [one_mul] using P.hessian_upper t t.property) g
  have hi : P.inclusion.adjoint g = MovingForms.variationalRHS P.inclusion g := by
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left, MovingForms.variationalRHS_inner]
  unfold closedGradientInverse
  simp only [ContinuousLinearMap.comp_apply, hi]
  change P.closedMovingGradient t
    (MovingForms.commonDomainSolution (P.closedMovingGradient t) P.inclusion
      P.coercivity_pos (P.closedMovingGradient_coercive t) g) = _
  unfold closedMovingGradient
  simpa only [transportedGraphGradient, ← P.closedCoefficient_eq_transport t,
    baseGradient, inclusion, unitary, coercivity,
    physicalGradientPullback] using heq

theorem physicalGradientPullback_continuous (g : Lp ℝ 2 (P.law a)) :
    Continuous (fun t : Icc a b => P.physicalGradientPullback t g) := by
  have he : (fun t : Icc a b => P.physicalGradientPullback t g) =
      fun t : Icc a b => P.closedGradientInverse (t : ℝ) g :=
    funext fun t => (P.closedGradientInverse_eq_physical t g).symm
  rw [he]
  exact (P.closedGradientInverse_continuous.comp continuous_subtype_val).clm_apply
    continuous_const

end AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
