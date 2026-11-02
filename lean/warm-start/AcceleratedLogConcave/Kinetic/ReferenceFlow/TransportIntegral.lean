import AcceleratedLogConcave.Kinetic.ReferenceFlow.TransportEnergy
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.InitialCorrector
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Integrating the actual transport-energy derivative on source subintervals. -/
noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b)

theorem physicalMovingCoreLp_continuous (ell s n : ℝ) (hsn : s^2+n^2=1)
    (T : Icc a b) {φ : GaussianPhase E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    Continuous (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hφ.continuous
  have hb (u : ℝ) (z : GaussianPhase E) :
      ‖physicalMovingCore F ell s n hsn T φ (u,z)‖ ≤ C := hC _
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_L2_of_dominated_core_representatives
    (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc)
    (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc t)
    (fun u z => physicalMovingCore F ell s n hsn T φ (u,z))
    (fun z => physicalMovingCore F ell s n hsn T φ (t,z))
    (fun u => (movingFrameCore_memLp F.ordered
      (physicalDrift_continuous F ell s n hsn) (physicalDrift_continuous F 0 s n hsn)
      (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_lipschitz F 0 s n hsn)
      (gaussianPhaseMeasure (F.law a)) T hφ.continuous hc u).coeFn_toLp)
    (movingFrameCore_memLp F.ordered
      (physicalDrift_continuous F ell s n hsn) (physicalDrift_continuous F 0 s n hsn)
      (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_lipschitz F 0 s n hsn)
      (gaussianPhaseMeasure (F.law a)) T hφ.continuous hc t).coeFn_toLp
    (fun _ => 2*C) (integrable_const _)
  · exact Eventually.of_forall fun u => Eventually.of_forall fun z =>
      (norm_sub_le _ _).trans (by linarith [hb u z,hb t z])
  · exact Eventually.of_forall fun z =>
      ((movingFrameCore_continuous F.ordered
        (physicalDrift_continuous F ell s n hsn) (physicalDrift_continuous F 0 s n hsn)
        (physicalDrift_lipschitz F ell s n hsn) (physicalDrift_lipschitz F 0 s n hsn)
        T hφ.continuous).comp (continuous_id.prodMk continuous_const)).continuousAt

theorem physicalMovingCoreLp_continuousOn (ell s n : ℝ) (hsn : s^2+n^2=1)
    (T : Icc a b) {φ : GaussianPhase E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    ContinuousOn (physicalMovingCoreLp F ell s n hsn T hφ.continuous hc) (Ioo a b) := by
  intro t ht
  exact (physicalMovingCoreLp_hasDerivAt F ell s n hsn T hφ hc t ht).choose_spec.1.continuousAt.continuousWithinAt

 theorem physicalTransportEnergy_integrated (ell ε : ℝ) (hell : 0 ≤ ell) (hε : 0 ≤ ε)
    (T : Icc a b) {φ : GaussianPhase E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hmean : (∫ z, φ z ∂gaussianPhaseMeasure (F.law T)) = 0)
    {s u : ℝ} (hs : a ≤ s) (hu : u < b) (hsu : s ≤ u)
    (hscale : ∀ t ∈ Icc s u, |F.scale t| ≤ ell/4) :
    let g := physicalMovingCoreLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ.continuous hc;
    let R := fun t => ‖g t-gaussianPositionProjection (F.law a) (g t)‖^2;
    quadraticEnergy (F.corrector u) ε (g u) ≤ quadraticEnergy (F.corrector s) ε (g s) -
      ε*ell*(u-s)/8*(∫ z, (φ z)^2 ∂gaussianPhaseMeasure (F.law T)) +
      3*ε*ell*(∫ t in s..u, R t) := by
  let g := physicalMovingCoreLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ.continuous hc
  let Q := fun t => quadraticEnergy (F.corrector t) ε (g t)
  let R := fun t => ‖g t-gaussianPositionProjection (F.law a) (g t)‖^2
  let N := ∫ z, (φ z)^2 ∂gaussianPhaseMeasure (F.law T)
  have hsub : Ioo s u ⊆ Ioo a b := fun t ht => ⟨hs.trans_lt ht.1, ht.2.trans hu⟩
  have hg : ContinuousOn g (Icc s u) :=
    (physicalMovingCoreLp_continuous F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc).continuousOn
  have hR : ContinuousOn R (Icc s u) :=
    (hg.sub ((gaussianPositionProjection (F.law a)).continuous.comp_continuousOn hg)).norm.pow 2
  have hderiv (t : ℝ) (ht : t ∈ Ioo s u) : ∃ d : ℝ, HasDerivAt Q d t ∧
      d ≤ -ε*ell*N/8+3*ε*ell*R t := by
    obtain ⟨d,hd,hbound⟩ := physicalTransportEnergy_derivative_le F ell ε hell hε T hφ hc hmean t
      (hsub ht) (hscale t ⟨ht.1.le,ht.2.le⟩)
    refine ⟨d,hd,?_⟩
    have he := physicalMovingCoreLp_eq_phaseUnitary F ell (1/2) (Real.sqrt 3/2)
      source_split_coefficients T hφ hc t (hsub ht)
    have hr : R t = ‖physicalTransportLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients
        T hφ hc t (hsub ht)-gaussianPositionProjection (F.law t)
          (physicalTransportLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t (hsub ht))‖^2 := by
      dsimp only [R,g]
      rw [he,phaseUnitary_micro_norm]
    rw [physicalTransportLp_norm_sq F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t (hsub ht),← hr] at hbound
    exact hbound
  have hA : ContinuousOn F.corrector (Icc s u) :=
    (Reheating.corrector_continuousOn_Ico F).mono (fun t ht => ⟨hs.trans ht.1,ht.2.trans_lt hu⟩)
  have hQ : ContinuousOn Q (Icc s u) := by
    unfold Q quadraticEnergy
    exact ((hg.norm.pow 2).const_mul (1/2 : ℝ)).add (((hA.clm_apply hg).inner hg).const_mul ε)
  have hbudget : ContinuousOn (fun t => -ε*ell*N/8+3*ε*ell*R t) (Icc s u) :=
    continuousOn_const.add (hR.const_mul _)
  have hi := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (g' := deriv Q) hsu hQ
    (fun t ht => ((hderiv t ht).choose_spec.1.differentiableAt.hasDerivAt.hasDerivWithinAt))
    (hbudget.integrableOn_Icc)
    (fun t ht => by
      rw [(hderiv t ht).choose_spec.1.deriv]
      exact (hderiv t ht).choose_spec.2)
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((hR.intervalIntegrable_of_Icc hsu).const_mul _), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,smul_eq_mul] at hi
  change Q u ≤ Q s - ε*ell*(u-s)/8*N+3*ε*ell*(∫ t in s..u,R t)
  nlinarith

end AcceleratedLogConcave.Kinetic
