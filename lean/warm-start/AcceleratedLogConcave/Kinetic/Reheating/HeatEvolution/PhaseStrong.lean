import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseGrowth
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.MaterialPointwise
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.FlowBounds
import AcceleratedLogConcave.Kinetic.ReferenceFlow.DerivativeEnvelope

/-! Genuine strong time calculus for the compact visible-phase heat core,
retaining momentum and transporting position by the actual reference flow. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The actual position flow with retained momentum preserves the product law. -/
theorem phaseHeatFlow_measurePreserving {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : Icc a b) : MeasurePreserving (fun z : E×E => (F.flow t z.1,z.2))
      ((F.law a).prod (stdGaussian E)) ((F.law t).prod (stdGaussian E)) :=
  (F.flow_measurePreserving t).prod (MeasurePreserving.id (stdGaussian E))

def phaseHeatMovingCore {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (f : E×E → ℝ) (t : ℝ) (z : E×E) : ℝ :=
  let τ := projIcc a b F.ordered t;
  compactPhaseHeatQuotient F f τ (F.flow τ z.1,z.2)

def phaseHeatMovingGenerator {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (f : E×E → ℝ) (t : ℝ) (z : E×E) : ℝ :=
  let τ := projIcc a b F.ordered t;
  -(1/2:ℝ)*compactPhaseHeatGenerator F f τ (F.flow τ z.1,z.2)

theorem phaseHeatMovingCore_memLp {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) (t : ℝ) :
    MemLp (phaseHeatMovingCore F f t) 2 ((F.law a).prod (stdGaussian E)) :=
  (compactPhaseHeatQuotient_memLp F hf hc hheat _ (projIcc a b F.ordered t).property).1.comp_measurePreserving
    (phaseHeatFlow_measurePreserving F (projIcc a b F.ordered t))

theorem phaseHeatMovingGenerator_memLp {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) (t : ℝ) :
    MemLp (phaseHeatMovingGenerator F f t) 2 ((F.law a).prod (stdGaussian E)) :=
  ((compactPhaseHeatQuotient_memLp F hf hc hheat _ (projIcc a b F.ordered t).property).2.2.comp_measurePreserving
    (phaseHeatFlow_measurePreserving F (projIcc a b F.ordered t))).const_mul (-(1/2:ℝ))

def phaseHeatMovingCoreLp {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) (t : ℝ) :
    Lp ℝ 2 ((F.law a).prod (stdGaussian E)) := (phaseHeatMovingCore_memLp F hf hc hheat t).toLp _

def phaseHeatMovingGeneratorLp {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) (t : ℝ) :
    Lp ℝ 2 ((F.law a).prod (stdGaussian E)) := (phaseHeatMovingGenerator_memLp F hf hc hheat t).toLp _

theorem phaseHeatMovingCore_hasDerivAt {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (t : ℝ) (ht : t ∈ Ioo a b) (z : E×E) :
    HasDerivAt (fun s => phaseHeatMovingCore F f s z) (phaseHeatMovingGenerator F f t z) t := by
  have hz := heatReferenceTrajectory_hasDerivAt F z.1 t ht
  rw [hscale t ht, neg_neg] at hz
  have hd := compactHeatQuotient_material_hasDerivAt F (phase_position_slice_C2 hf z.2)
    (phase_position_slice_compact hc z.2) ht (hscale t ht) hz
  have he : (fun s => phaseHeatMovingCore F f s z) =ᶠ[𝓝 t]
      fun s => compactHeatQuotient F (fun x => f (x,z.2)) s (heatReferenceTrajectory F z.1 s) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    simp only [phaseHeatMovingCore, projIcc_of_mem _ hs]
    rfl
  have hh := hd.congr_of_eventuallyEq he
  have heq := heatReferenceTrajectory_eq_flow F ⟨t,Ioo_subset_Icc_self ht⟩ z.1
  change heatReferenceTrajectory F z.1 t = _ at heq
  rw [heq] at hh
  simpa only [phaseHeatMovingGenerator, compactPhaseHeatGenerator, compactPhaseHeatQuotient,
    projIcc_of_mem _ (Ioo_subset_Icc_self ht)] using hh

theorem phaseHeatMovingGenerator_uniform_bound {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t z, ‖phaseHeatMovingGenerator F f t z‖ ≤ D*(1+‖z.1‖^2) := by
  obtain ⟨C,hC,hq⟩ := compactPhaseHeatQuotient_growth F hf hc hheat
  obtain ⟨B,hB,hflow⟩ := heatReferenceTrajectory_uniform_bound F
  refine ⟨C*(1+2*B^2),by positivity,fun t z => ?_⟩
  let τ := projIcc a b F.ordered t
  have h1 := (hq τ τ.property (F.flow τ z.1,z.2)).2.2
  have h2 := hflow τ τ.property z.1
  change ‖F.flow τ z.1‖ ≤ B*(1+‖z.1‖) at h2
  have hs : ‖F.flow τ z.1‖^2 ≤ 2*B^2*(1+‖z.1‖^2) := by
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ B*(1+‖z.1‖))).mpr h2
    nlinarith [mul_nonneg (sq_nonneg B) (sq_nonneg (‖z.1‖-1))]
  change ‖-(1/2:ℝ)*compactPhaseHeatGenerator F f τ (F.flow τ z.1,z.2)‖ ≤ _
  rw [norm_mul]
  norm_num only [norm_neg, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  nlinarith [mul_le_mul_of_nonneg_left hs hC, mul_nonneg hC (sq_nonneg ‖z.1‖)]

theorem phaseHeatMovingCoreLp_hasDerivAt {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (phaseHeatMovingCoreLp F hf hc hheat) (phaseHeatMovingGeneratorLp F hf hc hheat t) t := by
  obtain ⟨D,hD,hbound⟩ := phaseHeatMovingGenerator_uniform_bound F hf hc hheat
  apply hasDerivAt_L2_of_derivative_envelope ((F.law a).prod (stdGaussian E))
    (phaseHeatMovingCoreLp F hf hc hheat) (phaseHeatMovingGeneratorLp F hf hc hheat t)
    (phaseHeatMovingCore F f) (phaseHeatMovingGenerator F f) ht
    (fun s => (phaseHeatMovingCore_memLp F hf hc hheat s).coeFn_toLp)
    (phaseHeatMovingGenerator_memLp F hf hc hheat t).coeFn_toLp
    (phaseHeatMovingCore_hasDerivAt F hf hc hscale) (fun z => D*(1+‖z.1‖^2))
  · exact ((((memLp_const (1:ℝ) (μ := F.law a) (p := 2)).add
      (reference_memLp_norm_pow F a ⟨le_rfl,F.ordered⟩ 2)).const_mul D).comp_fst
        (stdGaussian E)).integrable_sq
  · exact fun s _ z => hbound s z

theorem phaseHeatMovingCore_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (z : E×E) :
    Continuous (fun t => phaseHeatMovingCore F f t z) := by
  let τ : ℝ → ℝ := fun t => projIcc a b F.ordered t
  have hτ : Continuous τ := continuous_subtype_val.comp continuous_projIcc
  have hz : Continuous (fun t => (F.flow (projIcc a b F.ordered t) z.1,z.2)) :=
    ((heatReferenceTrajectory_continuous F z.1).comp hτ).prodMk continuous_const
  exact (compactPhaseHeatQuotient_continuousOn F hf.continuous hc).comp_continuous
    (hτ.prodMk hz) (fun t => ⟨(projIcc a b F.ordered t).property,mem_univ _⟩)

theorem phaseHeatMovingGenerator_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (z : E×E) :
    Continuous (fun t => phaseHeatMovingGenerator F f t z) := by
  let τ : ℝ → ℝ := fun t => projIcc a b F.ordered t
  have hτ : Continuous τ := continuous_subtype_val.comp continuous_projIcc
  have hz : Continuous (fun t => (F.flow (projIcc a b F.ordered t) z.1,z.2)) :=
    ((heatReferenceTrajectory_continuous F z.1).comp hτ).prodMk continuous_const
  exact ((compactPhaseHeatGenerator_continuousOn F hf hc).comp_continuous
    (hτ.prodMk hz) (fun t => ⟨(projIcc a b F.ordered t).property,mem_univ _⟩)).const_mul (-(1/2:ℝ))

/-- Strong continuity of the actual transported phase core includes both endpoints. -/
theorem phaseHeatMovingCoreLp_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    Continuous (phaseHeatMovingCoreLp F hf hc hheat) := by
  obtain ⟨C,hC,hbound⟩ := compactPhaseHeatQuotient_growth F hf hc hheat
  have hb (t : ℝ) (z : E×E) : ‖phaseHeatMovingCore F f t z‖ ≤ C :=
    (hbound _ (projIcc a b F.ordered t).property _).1
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_L2_of_dominated_core_representatives
    (phaseHeatMovingCoreLp F hf hc hheat) (phaseHeatMovingCoreLp F hf hc hheat t)
    (phaseHeatMovingCore F f) (phaseHeatMovingCore F f t)
    (fun s => (phaseHeatMovingCore_memLp F hf hc hheat s).coeFn_toLp)
    (phaseHeatMovingCore_memLp F hf hc hheat t).coeFn_toLp
    (fun _ => 2*C) (integrable_const _)
  · exact Filter.Eventually.of_forall fun s => Filter.Eventually.of_forall fun z =>
      (norm_sub_le _ _).trans (by linarith [hb s z,hb t z])
  · exact Filter.Eventually.of_forall fun z => (phaseHeatMovingCore_continuous F hf hc z).continuousAt

theorem phaseHeatMovingGeneratorLp_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    Continuous (phaseHeatMovingGeneratorLp F hf hc hheat) := by
  obtain ⟨D,hD,hbound⟩ := phaseHeatMovingGenerator_uniform_bound F hf hc hheat
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_L2_of_dominated_core_representatives
    (phaseHeatMovingGeneratorLp F hf hc hheat) (phaseHeatMovingGeneratorLp F hf hc hheat t)
    (phaseHeatMovingGenerator F f) (phaseHeatMovingGenerator F f t)
    (fun s => (phaseHeatMovingGenerator_memLp F hf hc hheat s).coeFn_toLp)
    (phaseHeatMovingGenerator_memLp F hf hc hheat t).coeFn_toLp
    (fun z => 2*D*(1+‖z.1‖^2))
  · exact ((((memLp_const (1:ℝ) (μ := F.law a) (p := 2)).add
      (reference_memLp_norm_pow F a ⟨le_rfl,F.ordered⟩ 2)).const_mul (2*D)).comp_fst
        (stdGaussian E)).integrable_sq
  · exact Filter.Eventually.of_forall fun s => Filter.Eventually.of_forall fun z =>
      (norm_sub_le _ _).trans (by nlinarith [hbound s z,hbound t z])
  · exact Filter.Eventually.of_forall fun z => (phaseHeatMovingGenerator_continuous F hf hc z).continuousAt

end AcceleratedLogConcave.Kinetic.Reheating
