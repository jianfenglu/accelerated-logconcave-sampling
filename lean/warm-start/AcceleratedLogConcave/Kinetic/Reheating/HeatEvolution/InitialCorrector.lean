import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.InitialCoefficient

/-! The initial weighted inverse and corrector are the genuine physical operators. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory InnerProductSpace Set Filter
open scoped Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b)

theorem gradientInverse_initial_eq_transport (g : Lp ℝ 2 (F.law a)) :
    F.gradientInverse a g = F.unitary F.leftTime
      (gradientPoissonInverse (F.law a) (F.potential a) (F.potential_C2 a)
        (F.integrable a F.leftTime.property) (F.gibbs_law a F.leftTime.property)
        (F.lower a) 1 (F.lower_pos a F.leftTime.property)
        (F.hessian_lower a F.leftTime.property)
        (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)
        ((F.unitary F.leftTime).symm g)) := by
  have heq := commonDomainSolution_gradient_eq_pullback_gradientInverse
    (F.law a) (F.law a) (F.potential a) (F.potential a)
    ((F.potential_C2 a).of_le (by norm_num)) ((F.potential_C2 a).of_le (by norm_num))
    (F.integrable a F.leftTime.property) (F.integrable a F.leftTime.property)
    (F.gibbs_law a F.leftTime.property) (F.gibbs_law a F.leftTime.property)
    (F.flow F.leftTime) (F.flow_measurePreserving F.leftTime)
    (F.flow_C1 _) (F.flow_symm_C1 _) F.jacobianBound F.jacobianBound
    (F.flow_fderiv_bound _) (F.flow_symm_fderiv_bound _) (F.potential_C2 a) (F.potential_C2 a)
    (F.lower a) 1 (F.lower a) 1 (F.lower_pos a F.leftTime.property)
    (F.lower_pos a F.leftTime.property) F.jacobianBound_pos
    (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)
    (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property) g
  rw [F.gradientInverse_apply]
  unfold ReferencePoissonFamily.solution ReferencePoissonFamily.movingGradient
  have hc := gradientCoefficient_eq_transport_initial F
  simp only [ReferencePoissonFamily.leftTime] at hc heq ⊢
  simp only [transportedGraphGradient, ← hc,
    ReferencePoissonFamily.baseGradient, ReferencePoissonFamily.inclusion,
    ReferencePoissonFamily.unitary, ReferencePoissonFamily.coercivity,
    ReferencePoissonFamily.referenceClosedGradient] at heq ⊢
  convert heq using 1
  rfl




theorem unitary_initial {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (g : Lp K 2 (F.law a)) : F.unitary F.leftTime g = g := by
  apply Lp.ext
  filter_upwards [pullback_coeFn (F.flow F.leftTime).toMeasurableEquiv
    (F.flow_measurePreserving F.leftTime) g] with x hx
  change (F.unitary F.leftTime g) x = g (F.flow F.leftTime x) at hx
  rw [hx]
  congr 1
  exact referenceFlow_initial F.potential F.scale (fun s _ => F.potential_C2 s)
    F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
    F.hessian_nonneg F.hessian_upper F.leftTime x

theorem unitary_symm_initial {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (g : Lp K 2 (F.law a)) : (F.unitary F.leftTime).symm g = g := by
  apply (F.unitary F.leftTime).injective
  rw [LinearIsometryEquiv.apply_symm_apply, unitary_initial]

theorem gradientInverse_initial_eq_physical :
    F.gradientInverse a = gradientPoissonInverse (F.law a) (F.potential a) (F.potential_C2 a)
      (F.integrable a F.leftTime.property) (F.gibbs_law a F.leftTime.property)
      (F.lower a) 1 (F.lower_pos a F.leftTime.property)
      (F.hessian_lower a F.leftTime.property)
      (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property) := by
  ext g
  rw [gradientInverse_initial_eq_transport, unitary_initial, unitary_symm_initial]

theorem corrector_initial_eq_physical : F.corrector a = F.physicalCorrector F.leftTime := by
  unfold ReferencePoissonFamily.corrector ReferencePoissonFamily.physicalCorrector
  rw [gaussianCorrector_eq_referenceCorrector, gradientInverse_initial_eq_physical]
  rfl

theorem corrector_continuousAt_initial : ContinuousAt F.corrector a := by
  exact continuousAt_const.clm_comp
    ((ContinuousLinearMap.adjoint.continuousAt.comp (gradientInverse_continuousAt_initial F)).clm_comp
      continuousAt_const)

theorem corrector_continuousOn_Ico : ContinuousOn F.corrector (Ico a b) := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | hat
  · exact (corrector_continuousAt_initial F).continuousWithinAt
  · exact (continuousAt_const.clm_comp
      ((ContinuousLinearMap.adjoint.continuousAt.comp
        (F.gradientInverse_continuousAt t ⟨hat,ht.2⟩)).clm_comp continuousAt_const)).continuousWithinAt

end AcceleratedLogConcave.Kinetic.Reheating
