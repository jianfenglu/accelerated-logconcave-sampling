import AcceleratedLogConcave.Root.BackwardParentLaw

/-! Joint clock dependence of the actual reference flow, including its inverse.
No measurable-center or inverse-flow regularity premise is supplied. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Root.FlowClock

/-- Joint forward continuity plus a uniform inverse Lipschitz bound gives joint
inverse continuity. This is applied below to the actual complete ODE flow. -/
theorem continuous_inverse_family {T X : Type*} [TopologicalSpace T] [PseudoMetricSpace X]
    (e : T → X ≃ₜ X) (hf : Continuous (fun z : T × X => e z.1 z.2))
    (C : ℝ≥0) (hi : ∀ t, LipschitzWith C (e t).symm) :
    Continuous (fun z : T × X => (e z.1).symm z.2) := by
  rw [continuous_iff_continuousAt]
  intro z
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hc : Continuous (fun w : T × X => (C : ℝ) *
      dist w.2 (e w.1 ((e z.1).symm z.2))) :=
    continuous_const.mul (continuous_snd.dist (hf.comp (continuous_fst.prodMk continuous_const)))
  have ht : Tendsto (fun w : T × X => (C : ℝ) *
      dist w.2 (e w.1 ((e z.1).symm z.2))) (𝓝 z) (𝓝 0) := by
    simpa only [ContinuousAt, Homeomorph.apply_symm_apply, dist_self, mul_zero] using (hc.continuousAt (x := z))
  apply squeeze_zero (fun _ => dist_nonneg) _ ht
  intro w
  have h := (hi w.1).dist_le_mul w.2 (e w.1 ((e z.1).symm z.2))
  simpa only [Homeomorph.symm_apply_apply] using h

open OAI.LogConcaveSampling.GlobalODE
section ODE
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {a b : ℝ} {f : ℝ → X → X} {K : ℝ≥0}
  (hL : ∀ t ∈ Icc a b, LipschitzWith K (f t)) (hc : Continuous (Function.uncurry f))

/-- Unlike a fixed-clock spatial homeomorphism theorem, this varies clock and state together. -/
theorem flowHomeomorph_symm_joint_continuous (s : Icc a b) :
    Continuous (fun z : Icc a b × X => (flowHomeomorph hL hc s z.1).symm z.2) := by
  apply continuous_inverse_family (fun t => flowHomeomorph hL hc s t)
    ((flow_joint_continuous hL hc s).comp continuous_swap)
    ⟨Real.exp ((K : ℝ) * (b-a)), (Real.exp_pos _).le⟩
  intro t
  apply (flow_lipschitz hL hc t s).weaken
  change Real.exp _ ≤ Real.exp _
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  rw [abs_le]
  constructor <;> linarith [s.2.1,s.2.2,t.2.1,t.2.2]
end ODE

open AcceleratedLogConcave.Kinetic AcceleratedLogConcave.Analysis.Poisson
section ActualFlow
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell : ℝ)

/-- Actual coupled pair flow, jointly continuous in clock and spatial pair. -/
theorem referencePair_joint_continuous :
    Continuous (fun z : Icc a b × (E × E) => referenceCoupledPairFlow F ell z.1 z.2) := by
  have h := flow_joint_continuous
    (fun t ht => coupledDrift_lipschitz F.potential ell F.scale t (F.potential_C2 t)
      (F.hessian_nonneg t ht) (F.hessian_upper t ht) F.scaleBound (F.scale_bounded t ht))
    (coupledDrift_continuous F.potential ell F.scale F.gradient_continuous F.scale_continuous)
    F.leftTime
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ E E).continuous.comp
    (h.comp (((WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.continuous.comp continuous_snd).prodMk
      continuous_fst))

/-- The actual inverse parent flow is jointly continuous, not only separately measurable. -/
theorem referencePair_symm_joint_continuous :
    Continuous (fun z : Icc a b × (E × E) => (referenceCoupledPairFlow F ell z.1).symm z.2) := by
  have h := flowHomeomorph_symm_joint_continuous
    (fun t ht => coupledDrift_lipschitz F.potential ell F.scale t (F.potential_C2 t)
      (F.hessian_nonneg t ht) (F.hessian_upper t ht) F.scaleBound (F.scale_bounded t ht))
    (coupledDrift_continuous F.potential ell F.scale F.gradient_continuous F.scale_continuous)
    F.leftTime
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ E E).continuous.comp
    (h.comp (continuous_fst.prodMk
      ((WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.continuous.comp continuous_snd)))
end ActualFlow
end AcceleratedLogConcave.Root.FlowClock
