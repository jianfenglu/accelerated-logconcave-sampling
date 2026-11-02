import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseStrong
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseGreen
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseNorm

/-! Weighted energy of the actual signed heat core in the fixed reference
space. The gradient energy is identified through the proved closed-domain Green identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Exact instantaneous weighted gradient energy for the true heat quotient. -/
def phaseHeatCoreGradientEnergy {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (_hf : ContDiff ℝ 2 f) (_hc : HasCompactSupport f)
    (_hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (_ht : t ∈ Icc a b) : ℝ :=
  ∫ z, ‖compactPhaseHeatGradient F f t z‖^2 ∂(F.law t).prod (stdGaussian E)

theorem phaseHeatMovingCore_inner_generator {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    inner ℝ (phaseHeatMovingGeneratorLp F hf hc hheat t) (phaseHeatMovingCoreLp F hf hc hheat t) =
      -(1/2:ℝ)*phaseHeatCoreGradientEnergy F hf hc hheat t ht := by
  let q := compactPhaseHeatQuotient F f t
  let k := compactPhaseHeatGenerator F f t
  have hi : inner ℝ (phaseHeatMovingGeneratorLp F hf hc hheat t) (phaseHeatMovingCoreLp F hf hc hheat t) =
      ∫ z, q (F.flow ⟨t,ht⟩ z.1,z.2) * (-(1/2:ℝ)*k (F.flow ⟨t,ht⟩ z.1,z.2)) ∂(F.law a).prod (stdGaussian E) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(phaseHeatMovingGenerator_memLp F hf hc hheat t).coeFn_toLp,
      (phaseHeatMovingCore_memLp F hf hc hheat t).coeFn_toLp] with x hk hq
    change (phaseHeatMovingGeneratorLp F hf hc hheat t) x = _ at hk
    change (phaseHeatMovingCoreLp F hf hc hheat t) x = _ at hq
    change (phaseHeatMovingCoreLp F hf hc hheat t) x * (phaseHeatMovingGeneratorLp F hf hc hheat t) x = _
    rw [hk,hq]
    simp only [phaseHeatMovingCore,phaseHeatMovingGenerator,projIcc_of_mem _ ht]
    rfl
  rw [hi, (phaseHeatFlow_measurePreserving F ⟨t,ht⟩).integral_comp
    ((F.flow ⟨t,ht⟩).toMeasurableEquiv.prodCongr (MeasurableEquiv.refl E)).measurableEmbedding
    (fun z => q z * (-(1/2:ℝ)*k z))]
  unfold phaseHeatCoreGradientEnergy
  rw [compactPhaseHeatQuotient_green_integral F hf hc hheat t ht, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  dsimp only [q,k]
  ring

/-- Exact weighted L2 dissipation on the actual compact smooth heat core. -/
theorem phaseHeatMovingCore_norm_sq_hasDerivAt {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => ‖phaseHeatMovingCoreLp F hf hc hheat s‖^2)
      (-phaseHeatCoreGradientEnergy F hf hc hheat t ⟨ht.1.le,ht.2.le⟩) t := by
  have hd := (phaseHeatMovingCoreLp_hasDerivAt F hf hc hheat hscale t ht).norm_sq
  have hi := phaseHeatMovingCore_inner_generator F hf hc hheat t ⟨ht.1.le,ht.2.le⟩
  rw [real_inner_comm] at hi
  convert hd using 1
  linarith

/-- Integrated dissipation for the actual smooth core, including both
endpoints. The integrand is the squared norm of the true weighted gradient. -/
theorem phaseHeatMovingCore_energy_identity {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ)) :
    ‖phaseHeatMovingCoreLp F hf hc hheat a‖^2 - ‖phaseHeatMovingCoreLp F hf hc hheat b‖^2 =
      ∫ t in a..b, let τ := projIcc a b F.ordered t
        phaseHeatCoreGradientEnergy F hf hc hheat τ τ.property := by
  let D := fun t => -2 * inner ℝ (phaseHeatMovingGeneratorLp F hf hc hheat t)
    (phaseHeatMovingCoreLp F hf hc hheat t)
  have hD : Continuous D :=
    ((phaseHeatMovingGeneratorLp_continuous F hf hc hheat).inner
      (phaseHeatMovingCoreLp_continuous F hf hc hheat)).const_mul (-2)
  have he (t : ℝ) (ht : t ∈ Icc a b) :
      D t = phaseHeatCoreGradientEnergy F hf hc hheat t ht := by
    dsimp only [D]
    rw [phaseHeatMovingCore_inner_generator F hf hc hheat t ht]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f' := fun t => -D t) F.ordered
    ((phaseHeatMovingCoreLp_continuous F hf hc hheat).norm.pow 2).continuousOn
    (fun t ht => by
      rw [he t ⟨ht.1.le,ht.2.le⟩]
      exact phaseHeatMovingCore_norm_sq_hasDerivAt F hf hc hheat hscale t ht)
    (hD.neg.intervalIntegrable a b)
  have hgrad : (∫ t in a..b, D t) =
      ∫ t in a..b, let τ := projIcc a b F.ordered t
        phaseHeatCoreGradientEnergy F hf hc hheat τ τ.property := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le F.ordered] using ht
    simpa only [projIcc_of_mem _ ht'] using he t ht'
  rw [← hgrad]
  rw [intervalIntegral.integral_neg] at hFTC
  simp only [Pi.pow_apply] at hFTC
  linarith

theorem phaseHeatMovingCore_energy_identity_to {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (τ : ℝ) (hτ : τ ∈ Icc a b) :
    ‖phaseHeatMovingCoreLp F hf hc hheat a‖^2 - ‖phaseHeatMovingCoreLp F hf hc hheat τ‖^2 =
      ∫ t in a..τ, let τ := projIcc a b F.ordered t
        phaseHeatCoreGradientEnergy F hf hc hheat τ τ.property := by
  let D := fun t => -2 * inner ℝ (phaseHeatMovingGeneratorLp F hf hc hheat t)
    (phaseHeatMovingCoreLp F hf hc hheat t)
  have hD : Continuous D :=
    ((phaseHeatMovingGeneratorLp_continuous F hf hc hheat).inner
      (phaseHeatMovingCoreLp_continuous F hf hc hheat)).const_mul (-2)
  have he (t : ℝ) (ht : t ∈ Icc a b) :
      D t = phaseHeatCoreGradientEnergy F hf hc hheat t ht := by
    dsimp only [D]
    rw [phaseHeatMovingCore_inner_generator F hf hc hheat t ht]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f' := fun t => -D t) hτ.1
    ((phaseHeatMovingCoreLp_continuous F hf hc hheat).norm.pow 2).continuousOn
    (fun t ht => by
      rw [he t ⟨ht.1.le,ht.2.le.trans hτ.2⟩]
      exact phaseHeatMovingCore_norm_sq_hasDerivAt F hf hc hheat hscale t ⟨ht.1,ht.2.trans_le hτ.2⟩)
    (hD.neg.intervalIntegrable a τ)
  have hgrad : (∫ t in a..τ, D t) =
      ∫ t in a..τ, let τ := projIcc a b F.ordered t
        phaseHeatCoreGradientEnergy F hf hc hheat τ τ.property := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hti : t ∈ Icc a τ := by simpa only [uIcc_of_le hτ.1] using ht
    have ht' : t ∈ Icc a b := ⟨hti.1,hti.2.trans hτ.2⟩
    simpa only [projIcc_of_mem _ ht'] using he t ht'
  rw [← hgrad]
  rw [intervalIntegral.integral_neg] at hFTC
  simp only [Pi.pow_apply] at hFTC
  linarith

/-- The dissipation defect is exactly that of the actual bounded signed heat
operator, with retained momentum, on the compact smooth core. -/
theorem ordinaryHeatDensity_core_energy_identity {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ)) :
    ‖compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc‖^2 -
      ‖ordinaryHeatDensity (F.law a) (b-a)
        (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc)‖^2 =
      ∫ t in a..b, let τ := projIcc a b F.ordered t
        phaseHeatCoreGradientEnergy F hf hc hheat τ τ.property := by
  rw [← phaseHeatMovingCoreLp_norm_eq_ordinaryHeatDensity F hf hc hheat b ⟨F.ordered,le_rfl⟩,
    ← phaseHeatMovingCoreLp_initial F hf hc hheat]
  exact phaseHeatMovingCore_energy_identity F hf hc hheat hscale

theorem ordinaryHeatDensity_core_energy_identity_to {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (τ : ℝ) (hτ : τ ∈ Icc a b) :
    ‖compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc‖^2 -
      ‖ordinaryHeatDensity (F.law a) (τ-a)
        (compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc)‖^2 =
      ∫ t in a..τ, let τ := projIcc a b F.ordered t
        phaseHeatCoreGradientEnergy F hf hc hheat τ τ.property := by
  rw [← phaseHeatMovingCoreLp_norm_eq_ordinaryHeatDensity F hf hc hheat τ hτ,
    ← phaseHeatMovingCoreLp_initial F hf hc hheat]
  exact phaseHeatMovingCore_energy_identity_to F hf hc hheat hscale τ hτ

end AcceleratedLogConcave.Kinetic.Reheating
