import AcceleratedLogConcave.Kinetic.ReferenceCorrector
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Initial-time continuity of the genuine reference-gradient coefficient.
Its identity value at the left endpoint agrees with the actual initial Jacobian. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory InnerProductSpace Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b)

private abbrev initialMatrix (t : ℝ) (x : E) :=
  referenceGradientMatrix F.potential F.scale F.ordered F.potential_C2 F.gradient_continuous
    F.hessian_continuous F.scale_continuous F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper t x

private theorem initialMatrix_initial (x : E) : initialMatrix F a x = ContinuousLinearMap.id ℝ E := by
  unfold initialMatrix referenceGradientMatrix referenceJacobian OAI.LogConcaveSampling.GlobalODE.flowLinearization
  rw [OAI.LogConcaveSampling.GlobalODE.fundamental_initial]
  change (Ring.inverse (1 : E →L[ℝ] E)).adjoint = ContinuousLinearMap.id ℝ E
  rw [Ring.inverse_one]
  exact ContinuousLinearMap.adjoint_id

private theorem initialMatrix_continuousOn (x : E) :
    ContinuousOn (fun t => initialMatrix F t x) (Icc a b) := by
  have hJ : Continuous (referenceJacobian F.potential F.scale F.ordered F.potential_C2
      F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound F.scale_bounded
      F.hessian_nonneg F.hessian_upper x) := by
    unfold referenceJacobian OAI.LogConcaveSampling.GlobalODE.flowLinearization
    exact OAI.LogConcaveSampling.GlobalODE.fundamental_continuous _ _ _
  intro t ht
  have hi := NormedRing.inverse_continuousAt
    (referenceJacobianEquiv F.potential F.scale F.ordered F.potential_C2 F.gradient_continuous
      F.hessian_continuous F.scale_continuous F.scaleBound F.scale_bounded F.hessian_nonneg
      F.hessian_upper x ⟨t,ht⟩).toUnit
  change ContinuousAt Ring.inverse (referenceJacobian F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound F.scale_bounded
    F.hessian_nonneg F.hessian_upper x t) at hi
  exact (ContinuousLinearMap.adjoint.continuousAt.comp (hi.comp hJ.continuousAt)).continuousWithinAt

private theorem initialMatrix_sub_initial_bound (x : E) (t : ℝ) (ht : t ∈ Ioo a b) :
    ‖initialMatrix F t x - ContinuousLinearMap.id ℝ E‖ ≤
      (F.scaleBound : ℝ)*F.jacobianBound*‖t-a‖ := by
  let K : ℝ≥0 := ⟨(F.scaleBound : ℝ)*F.jacobianBound,
    mul_nonneg F.scaleBound.coe_nonneg F.jacobianBound_pos.le⟩
  have hd (s : ℝ) (hs : s ∈ Ioo a b) := referenceGradientMatrix_hasDerivAt
    F.potential F.scale F.ordered F.potential_C2 F.gradient_continuous F.hessian_continuous
    F.scale_continuous F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper x s hs
  have hb (s : ℝ) (hs : s ∈ Ioo a b) := referenceGradientMatrix_deriv_norm_le
    F.potential F.scale F.ordered F.potential_C2 F.gradient_continuous F.hessian_continuous
    F.scale_continuous F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper x s hs
  have hb' (s : ℝ) (hs : s ∈ Ioo a b) :
      ‖deriv (fun r => initialMatrix F r x) s‖ ≤ (F.scaleBound : ℝ)*F.jacobianBound := by
    exact hb s hs
  have hL : LipschitzOnWith K (fun s => initialMatrix F s x) (Ioo a b) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro s hs u hu
    simp only [dist_eq_norm]
    change ‖initialMatrix F s x - initialMatrix F u x‖ ≤
      (F.scaleBound : ℝ)*F.jacobianBound*‖s-u‖
    exact (convex_Ioo a b).norm_image_sub_le_of_norm_deriv_le
      (f := fun r => initialMatrix F r x)
      (fun r hr => (hd r hr).differentiableAt) (fun r hr => hb' r hr) hu hs
  have hab : a < b := ht.1.trans ht.2
  have hLc : LipschitzOnWith K (fun s => initialMatrix F s x) (Icc a b) := by
    have hc : ContinuousOn (fun s => initialMatrix F s x) (closure (Ioo a b)) := by
      simpa only [closure_Ioo hab.ne] using initialMatrix_continuousOn F x
    simpa only [closure_Ioo hab.ne] using LipschitzOnWith.closure hc hL
  have he := hLc.dist_le_mul t (Ioo_subset_Icc_self ht) a (show a ∈ Icc a b from ⟨le_rfl,F.ordered⟩)
  simp only [dist_eq_norm] at he
  change ‖initialMatrix F t x - initialMatrix F a x‖ ≤
    (F.scaleBound : ℝ)*F.jacobianBound*‖t-a‖ at he
  simpa only [initialMatrix_initial] using he

/-- The actual coefficient is operator-norm continuous at its identity initial value. -/
theorem gradientCoefficient_continuousAt_initial : ContinuousAt F.gradientCoefficient a := by
  unfold ReferencePoissonFamily.gradientCoefficient referenceGradientMultiplier
  apply continuousAt_fieldMultiplier_of_quotient_bound
    (C := (F.scaleBound : ℝ)*F.jacobianBound)
  apply Eventually.of_forall
  intro t x
  have ha : a ∉ Ioo a b := by simp
  by_cases ht : t ∈ Ioo a b
  · have hn := initialMatrix_sub_initial_bound F x t ht
    simp only [slope_def_module, extendedReferenceGradientMatrix, ite_eq_left ht, ite_eq_right ha,
      norm_smul, norm_inv]
    have hne : ‖t-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ne_of_gt ht.1))
    apply (mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (norm_nonneg _))).trans
    exact le_of_eq (by field_simp)
  · simp only [slope_def_module, extendedReferenceGradientMatrix, ite_eq_right ht, ite_eq_right ha,
      sub_self, smul_zero, norm_zero]
    exact mul_nonneg F.scaleBound.coe_nonneg F.jacobianBound_pos.le

theorem gradientInverse_continuousAt_initial : ContinuousAt F.gradientInverse a := by
  have hD : ContinuousAt F.movingGradient a :=
    (gradientCoefficient_continuousAt_initial F).clm_comp continuousAt_const
  have hB : ContinuousAt (fun s => MovingForms.energyCoefficient (F.movingGradient s)) a :=
    (ContinuousLinearMap.adjoint.continuousAt.comp hD).clm_comp hD
  exact hD.clm_comp ((MovingForms.continuousAt_coerciveInverse
    (fun s => MovingForms.energyCoefficient (F.movingGradient s)) F.coercivity_pos
    (fun s => MovingForms.energyCoefficient_coercive _ (F.movingGradient_coercive s)) hB).clm_comp
    continuousAt_const)

theorem gradientCoefficient_eq_transport_initial :
    F.gradientCoefficient a = inverseJacobianMultiplier (F.law a)
      (F.flow F.leftTime) (F.flow_symm_C1 F.leftTime)
      F.jacobianBound (F.flow_symm_fderiv_bound F.leftTime) := by
  have heq := referenceFlow_inverseJacobianMultiplier_eq F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper (F.law a) F.leftTime
  change inverseJacobianMultiplier (F.law a) (F.flow F.leftTime)
    (F.flow_symm_C1 F.leftTime) F.jacobianBound
    (F.flow_symm_fderiv_bound F.leftTime) = _ at heq
  rw [heq]
  unfold ReferencePoissonFamily.gradientCoefficient referenceGradientMultiplier
  congr 1
  funext x
  have ha : a ∉ Ioo a b := by simp
  simp only [extendedReferenceGradientMatrix, ite_eq_right ha]
  exact (initialMatrix_initial F x).symm

end AcceleratedLogConcave.Kinetic.Reheating
