import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseStrong
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseIdentification

/-! Endpoint identification with the actual ordinary heat channel. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem phaseHeatMovingCoreLp_norm_sq {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖phaseHeatMovingCoreLp F hf hc hheat t‖^2 =
      ∫ z, (compactPhaseHeatQuotient F f t z)^2 ∂(F.law t).prod (stdGaussian E) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have he : (∫ z, inner ℝ ((phaseHeatMovingCoreLp F hf hc hheat t) z)
      ((phaseHeatMovingCoreLp F hf hc hheat t) z) ∂(F.law a).prod (stdGaussian E)) =
      ∫ z, (compactPhaseHeatQuotient F f t (F.flow ⟨t,ht⟩ z.1,z.2))^2
        ∂(F.law a).prod (stdGaussian E) := by
    apply integral_congr_ae
    filter_upwards [(phaseHeatMovingCore_memLp F hf hc hheat t).coeFn_toLp] with z hz
    change (phaseHeatMovingCoreLp F hf hc hheat t) z = _ at hz
    rw [hz]
    simp only [phaseHeatMovingCore, projIcc_of_mem _ ht, real_inner_self_eq_norm_sq,
      Real.norm_eq_abs, sq_abs]
  rw [he]
  let e := (F.flow ⟨t,ht⟩).toMeasurableEquiv.prodCongr (MeasurableEquiv.refl E)
  exact (phaseHeatFlow_measurePreserving F ⟨t,ht⟩).integral_comp e.measurableEmbedding
    (fun z => (compactPhaseHeatQuotient F f t z)^2)

/-- The transported norm is the norm of the actual signed heat output. -/
theorem phaseHeatMovingCoreLp_norm_eq_ordinaryHeatDensity {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E×E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖phaseHeatMovingCoreLp F hf hc hheat t‖ =
      ‖ordinaryHeatDensity (F.law a) (t-a)
        (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc)‖ := by
  have h1 := phaseHeatMovingCoreLp_norm_sq F hf hc hheat t ht
  have h2 : ‖ordinaryHeatDensity (F.law a) (t-a)
      (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc)‖^2 =
      ∫ z, (compactPhaseHeatQuotient F f t z)^2 ∂(F.law t).prod (stdGaussian E) := by
    rw [hheat t ht, ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [compactPhaseHeatQuotient_eq_ordinaryHeatDensity F hf hc t ht (hheat t ht)] with z hz
    rw [hz]
    simp
  nlinarith [norm_nonneg (phaseHeatMovingCoreLp F hf hc hheat t),
    norm_nonneg (ordinaryHeatDensity (F.law a) (t-a)
      (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc))]

/-- At zero elapsed time the actual transported core is the original input. -/
theorem phaseHeatMovingCoreLp_initial {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    phaseHeatMovingCoreLp F hf hc hheat a =
      compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc := by
  apply Lp.ext
  filter_upwards [(phaseHeatMovingCore_memLp F hf hc hheat a).coeFn_toLp,
    (compactTest_memLp ((F.law a).prod (stdGaussian E)) f hf.continuous hc).coeFn_toLp] with z hz hfz
  change (phaseHeatMovingCoreLp F hf hc hheat a) z = _ at hz
  change (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc) z = _ at hfz
  rw [hz,hfz]
  have hi : F.flow ⟨a,le_rfl,F.ordered⟩ z.1 = z.1 :=
    referenceFlow_initial F.potential F.scale (fun s _ => F.potential_C2 s) F.gradient_continuous
      F.scale_continuous F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime z.1
  simp only [phaseHeatMovingCore, projIcc_of_mem _ (show a ∈ Icc a b from ⟨le_rfl,F.ordered⟩),
    compactPhaseHeatQuotient, compactHeatQuotient_initial, hi]

end AcceleratedLogConcave.Kinetic.Reheating
