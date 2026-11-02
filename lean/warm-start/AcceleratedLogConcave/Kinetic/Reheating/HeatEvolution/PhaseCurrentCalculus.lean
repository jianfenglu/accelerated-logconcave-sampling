import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseCorrectorPairing
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseEnergy

/-! Actual moving-frame current differentiation and physical pairing transport. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The physical heat current in the fixed reference phase Hilbert space. -/
def phaseHeatCurrent {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) (t : ℝ) : ℝ :=
  let q := Kinetic.hiddenEmbedding (F.law a) (phaseHeatMovingCoreLp F hf hc hheat t)
  inner ℝ q (F.corrector t q)

/-- A continuous representative of the true gradient dissipation. -/
def phaseHeatDissipation {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) (t : ℝ) : ℝ :=
  -2 * inner ℝ (phaseHeatMovingGeneratorLp F hf hc hheat t) (phaseHeatMovingCoreLp F hf hc hheat t)

theorem phaseHeatDissipation_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    Continuous (phaseHeatDissipation F hf hc hheat) :=
  ((phaseHeatMovingGeneratorLp_continuous F hf hc hheat).inner
    (phaseHeatMovingCoreLp_continuous F hf hc hheat)).const_mul (-2)

theorem phaseHeatDissipation_eq_gradient_energy {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    phaseHeatDissipation F hf hc hheat t = phaseHeatCoreGradientEnergy F hf hc hheat t ht := by
  unfold phaseHeatDissipation
  rw [phaseHeatMovingCore_inner_generator F hf hc hheat t ht]
  ring

theorem phaseHeatDissipation_eq_norm_sq {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    phaseHeatDissipation F hf hc hheat t = ‖phaseHeatGradientLp F hf hc hheat t ht‖^2 := by
  rw [phaseHeatDissipation_eq_gradient_energy F hf hc hheat t ht,
    ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(compactPhaseHeatQuotient_memLp F hf hc hheat t ht).2.1.coeFn_toLp] with z hz
  change phaseHeatGradientLp F hf hc hheat t ht z = _ at hz
  rw [hz, real_inner_self_eq_norm_sq]

theorem phaseHeatCurrent_hasDerivAt {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (t : ℝ) (ht : t ∈ Ioo a b) :
    let q := Kinetic.hiddenEmbedding (F.law a) (phaseHeatMovingCoreLp F hf hc hheat t)
    let d := Kinetic.hiddenEmbedding (F.law a) (phaseHeatMovingGeneratorLp F hf hc hheat t)
    HasDerivAt (phaseHeatCurrent F hf hc hheat)
      (inner ℝ d (F.corrector t q) + inner ℝ q (F.corrector t d) +
        inner ℝ q (F.materialCorrector t ht q)) t := by
  exact F.corrector_quadratic_hasDerivAt t ht _ _
    ((Kinetic.hiddenEmbedding (F.law a)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (phaseHeatMovingCoreLp_hasDerivAt F hf hc hheat hscale t ht))

/-- Physical corrector pairings are unchanged by actual phase transport. -/
theorem phaseHeat_corrector_pullback_pairing {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Ioo a b)
    (k q : Lp ℝ 2 ((F.law t).prod (stdGaussian E))) :
    let τ : Icc a b := ⟨t,ht.1.le,ht.2.le⟩
    inner ℝ (F.phaseUnitary τ (Kinetic.hiddenEmbedding (F.law t) k))
      (F.corrector t (F.phaseUnitary τ (Kinetic.hiddenEmbedding (F.law t) q))) =
      inner ℝ k (phaseVisibleCorrector F t τ.property q) := by
  dsimp only
  rw [F.corrector_eq_physical t ht]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply]
  rw [(F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩).inner_map_map]
  change inner ℝ (Kinetic.hiddenEmbedding (F.law t) k)
    (gaussianCorrector (F.law t) (F.potential t) (F.potential_C2 t) (F.integrable t (Ioo_subset_Icc_self ht))
      (F.gibbs_law t (Ioo_subset_Icc_self ht)) (F.lower t) 1 (F.lower_pos t (Ioo_subset_Icc_self ht)) (F.hessian_lower t (Ioo_subset_Icc_self ht))
      (by simpa only [one_mul] using F.hessian_upper t (Ioo_subset_Icc_self ht))
      (Kinetic.hiddenEmbedding (F.law t) q)) = _
  rw [← hiddenEmbedding_visibleCorrector, (Kinetic.hiddenEmbedding (F.law t)).inner_map_map]
  rfl

end AcceleratedLogConcave.Kinetic.Reheating
