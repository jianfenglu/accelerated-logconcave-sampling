import AcceleratedLogConcave.Analysis.Poisson.ReferencePoisson
import AcceleratedLogConcave.Analysis.Poisson.ReferenceTimeExtension

/-! Growth and calculus of the actual reference trajectory used by heat core
transport. The flow is the existing constructed ODE solution. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ}

def heatReferenceTrajectory (F : ReferencePoissonFamily E a b) (x : E) : ℝ → E :=
  referenceFlow F.potential F.scale (fun s _ => F.potential_C2 s) F.gradient_continuous
    F.scale_continuous F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime x

@[simp] theorem heatReferenceTrajectory_eq_flow (F : ReferencePoissonFamily E a b)
    (t : Icc a b) (x : E) : heatReferenceTrajectory F x t = F.flow t x := rfl

theorem heatReferenceTrajectory_continuous (F : ReferencePoissonFamily E a b) (x : E) :
    Continuous (heatReferenceTrajectory F x) :=
  referenceFlow_continuous F.potential F.scale (fun s _ => F.potential_C2 s) F.gradient_continuous
    F.scale_continuous F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime x

theorem heatReferenceTrajectory_hasDerivAt (F : ReferencePoissonFamily E a b)
    (x : E) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (heatReferenceTrajectory F x)
      ((-F.scale t) • gradient (F.potential t) (heatReferenceTrajectory F x t)) t :=
  (referenceFlow_deriv F.potential F.scale (fun s _ => F.potential_C2 s) F.gradient_continuous
    F.scale_continuous F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper
    F.leftTime x t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- A common affine growth bound follows from ODE stability and the compact
trajectory of the origin. -/
theorem heatReferenceTrajectory_uniform_bound (F : ReferencePoissonFamily E a b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x,
      ‖heatReferenceTrajectory F x t‖ ≤ B*(1+‖x‖) := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (heatReferenceTrajectory_continuous F (0:E)).continuousOn
  let B := max M 0 + F.jacobianBound
  have hJ : 0 ≤ F.jacobianBound := (Real.exp_pos _).le
  have hB : 0 ≤ B := add_nonneg (le_max_right _ _) hJ
  refine ⟨B,hB,fun t ht x => ?_⟩
  have hL := OAI.LogConcaveSampling.GlobalODE.flow_lipschitz
    (fun s hs => referenceDrift_lipschitz F.potential F.scale s (F.potential_C2 s)
      (F.hessian_nonneg s hs) (F.hessian_upper s hs) F.scaleBound (F.scale_bounded s hs))
    (referenceDrift_continuous F.potential F.scale F.gradient_continuous F.scale_continuous)
    F.leftTime ⟨t,ht⟩
  have hd := hL.dist_le_mul x 0
  change dist (heatReferenceTrajectory F x t) (heatReferenceTrajectory F 0 t) ≤
    Real.exp (F.scaleBound*|t-a|)*dist x 0 at hd
  have hExp : Real.exp (F.scaleBound*|t-a|) ≤ F.jacobianBound := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) F.scaleBound.coe_nonneg
  simp only [dist_eq_norm, sub_zero] at hd
  have hb0 := hM t ht
  have he := norm_le_insert' (heatReferenceTrajectory F x t) (heatReferenceTrajectory F 0 t)
  have hh := mul_le_mul_of_nonneg_right hExp (norm_nonneg x)
  dsimp only [B]
  nlinarith [le_max_left M 0, mul_nonneg (le_max_right M 0) (norm_nonneg x)]

end AcceleratedLogConcave.Kinetic.Reheating
