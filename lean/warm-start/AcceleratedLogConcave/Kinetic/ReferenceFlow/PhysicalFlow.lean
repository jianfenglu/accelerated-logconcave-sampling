import AcceleratedLogConcave.Kinetic.ReferenceFlow.PhysicalCore

/-! Identification of the physical ODE flow with the actual rotated coupled flow. -/
noncomputable section
set_option maxHeartbeats 1600000
open Set Function MeasureTheory InnerProductSpace
open scoped NNReal
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)

/-- Coordinate conjugacy of the full physical flow is proved by ODE uniqueness. -/
theorem physicalFlow_eq (t : Icc a b) (z : GaussianPhase E) :
    flow (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_continuous F ell s n hsn)
      F.leftTime z t =
      physicalPhaseCoordinates s n hsn
        (referenceCoupledFlow F ell t ((physicalPhaseCoordinates s n hsn).symm z).1,
          ((physicalPhaseCoordinates s n hsn).symm z).2) := by
  rw [show flow (physicalDrift_lipschitz F ell s n hsn)
      (physicalDrift_continuous F ell s n hsn) F.leftTime z t =
      physicalPhaseCoordinates s n hsn
        (flow (fun u hu => extendDrift_lipschitz (Y := E)
          (coupledDrift_lipschitz F.potential ell F.scale u (F.potential_C2 u)
            (F.hessian_nonneg u hu) (F.hessian_upper u hu) F.scaleBound (F.scale_bounded u hu)))
          (extendDrift_continuous (coupledDrift_continuous F.potential ell F.scale
            F.gradient_continuous F.scale_continuous)) F.leftTime
          ((physicalPhaseCoordinates s n hsn).symm z) t) from
        flow_conjugateDrift (physicalPhaseCoordinates s n hsn) _ _ F.leftTime t z]
  rw [flow_extendDrift
    (coupledDrift_continuous F.potential ell F.scale F.gradient_continuous F.scale_continuous)
    (fun u hu => coupledDrift_lipschitz F.potential ell F.scale u (F.potential_C2 u)
      (F.hessian_nonneg u hu) (F.hessian_upper u hu) F.scaleBound (F.scale_bounded u hu))]
  rfl

/-- At zero Hamiltonian speed the physical flow is exactly W04's spatial
reference flow, with both Gaussian coordinates fixed. -/
theorem physicalFlow_zero_eq (t : Icc a b) (z : GaussianPhase E) :
    flow (physicalDrift_lipschitz F 0 s n hsn) (physicalDrift_continuous F 0 s n hsn)
      F.leftTime z t = ((F.flow t z.1.1,z.1.2),z.2) := by
  let x := referenceFlow F.potential F.scale (fun u _ => F.potential_C2 u)
    F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
    F.hessian_nonneg F.hessian_upper F.leftTime z.1.1
  have hx := referenceFlow_continuous F.potential F.scale (fun u _ => F.potential_C2 u)
    F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
    F.hessian_nonneg F.hessian_upper F.leftTime z.1.1
  have hd (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivWithinAt (fun v => ((x v,z.1.2),z.2))
        (physicalPhaseDrift F.potential 0 F.scale s n hsn u ((x u,z.1.2),z.2)) (Icc a b) u := by
    rw [physicalPhaseDrift_apply]
    simp only [zero_smul, zero_sub, neg_zero, zero_mul]
    simpa only [referenceDrift, neg_smul] using ((referenceFlow_deriv F.potential F.scale (fun v _ => F.potential_C2 v)
      F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
      F.hessian_nonneg F.hessian_upper F.leftTime z.1.1 u hu).prodMk
        (hasDerivWithinAt_const u (Icc a b) z.1.2)).prodMk
        (hasDerivWithinAt_const u (Icc a b) z.2)
  have hh := trajectory_dist (physicalDrift_lipschitz F 0 s n hsn)
    (flow_continuous (physicalDrift_lipschitz F 0 s n hsn)
      (physicalDrift_continuous F 0 s n hsn) F.leftTime z).continuousOn
    (flow_deriv (physicalDrift_lipschitz F 0 s n hsn)
      (physicalDrift_continuous F 0 s n hsn) F.leftTime z)
    ((hx.prodMk continuous_const).prodMk continuous_const).continuousOn hd F.leftTime t
  have hi := referenceFlow_initial F.potential F.scale
    (fun u _ => F.potential_C2 u) F.gradient_continuous F.scale_continuous
    F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime z.1.1
  have hfi := flow_initial (physicalDrift_lipschitz F 0 s n hsn)
    (physicalDrift_continuous F 0 s n hsn) F.leftTime z
  rw [hfi, hi] at hh
  have he := (dist_le_zero.mp (by simpa only [Prod.mk.eta, dist_self, zero_mul] using hh))
  change flow (physicalDrift_lipschitz F 0 s n hsn) (physicalDrift_continuous F 0 s n hsn)
    F.leftTime z t = ((referenceFlow F.potential F.scale (fun u _ => F.potential_C2 u)
      F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
      F.hessian_nonneg F.hessian_upper F.leftTime z.1.1 t,z.1.2),z.2)
  exact he

end AcceleratedLogConcave.Kinetic
