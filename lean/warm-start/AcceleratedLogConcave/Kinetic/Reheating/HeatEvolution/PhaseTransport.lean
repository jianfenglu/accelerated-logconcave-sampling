import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseNorm
import AcceleratedLogConcave.Kinetic.ReferenceCorrector

/-! Exact physical and reference-space identifications for the phase heat core. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The actual reference flow on visible phase space, with momentum retained. -/
def phaseHeatPullback {a b : ℝ} (F : ReferencePoissonFamily E a b) (t : Icc a b) :
    Lp ℝ 2 ((F.law t).prod (stdGaussian E)) ≃ₗᵢ[ℝ]
      Lp ℝ 2 ((F.law a).prod (stdGaussian E)) :=
  pullback ((F.flow t).toMeasurableEquiv.prodCongr (MeasurableEquiv.refl E))
    (phaseHeatFlow_measurePreserving F t)

theorem phaseHeatPullback_hiddenEmbedding {a b : ℝ} (F : ReferencePoissonFamily E a b) (t : Icc a b)
    (g : Lp ℝ 2 ((F.law t).prod (stdGaussian E))) :
    Kinetic.hiddenEmbedding (F.law a) (phaseHeatPullback F t g) =
      F.phaseUnitary t (Kinetic.hiddenEmbedding (F.law t) g) := by
  apply Lp.ext
  have hp := pullback_coeFn ((F.flow t).toMeasurableEquiv.prodCongr (MeasurableEquiv.refl E))
    (phaseHeatFlow_measurePreserving F t) g
  have hh := Lp.coeFn_compMeasurePreserving g (measurePreserving_fst (ν := stdGaussian E))
  filter_upwards [Lp.coeFn_compMeasurePreserving (phaseHeatPullback F t g)
      (measurePreserving_fst (ν := stdGaussian E)),
    measurePreserving_fst.quasiMeasurePreserving.ae hp,
    gaussianPhasePullback_coe (F.flow t).toMeasurableEquiv (F.flow_measurePreserving t)
      (Kinetic.hiddenEmbedding (F.law t) g),
    (gaussianPhaseEquiv_measurePreserving (F.flow t).toMeasurableEquiv
      (F.flow_measurePreserving t)).quasiMeasurePreserving.ae hh] with z h1 h2 h3 h4
  exact h1.trans (h2.trans (h4.symm.trans h3.symm))

theorem phaseHeatMovingCoreLp_eq_pullback {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    phaseHeatMovingCoreLp F hf hc hheat t = phaseHeatPullback F ⟨t,ht⟩
      ((compactPhaseHeatQuotient_memLp F hf hc hheat t ht).1.toLp _) := by
  apply Lp.ext
  filter_upwards [(phaseHeatMovingCore_memLp F hf hc hheat t).coeFn_toLp,
    pullback_coeFn ((F.flow ⟨t,ht⟩).toMeasurableEquiv.prodCongr (MeasurableEquiv.refl E))
      (phaseHeatFlow_measurePreserving F ⟨t,ht⟩)
      ((compactPhaseHeatQuotient_memLp F hf hc hheat t ht).1.toLp _),
    (phaseHeatFlow_measurePreserving F ⟨t,ht⟩).quasiMeasurePreserving.ae
      (compactPhaseHeatQuotient_memLp F hf hc hheat t ht).1.coeFn_toLp] with z hz hp hq
  change (phaseHeatMovingCoreLp F hf hc hheat t) z = _ at hz
  change (phaseHeatPullback F ⟨t,ht⟩ _) z = _ at hp
  rw [hz,hp]
  simp only [phaseHeatMovingCore, projIcc_of_mem _ ht]
  exact hq.symm

theorem phaseHeatMovingGeneratorLp_eq_pullback {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    phaseHeatMovingGeneratorLp F hf hc hheat t = -(1/2:ℝ) • phaseHeatPullback F ⟨t,ht⟩
      ((compactPhaseHeatQuotient_memLp F hf hc hheat t ht).2.2.toLp _) := by
  apply Lp.ext
  let k := (compactPhaseHeatQuotient_memLp F hf hc hheat t ht).2.2.toLp _
  filter_upwards [(phaseHeatMovingGenerator_memLp F hf hc hheat t).coeFn_toLp,
    Lp.coeFn_smul (-(1/2:ℝ)) (phaseHeatPullback F ⟨t,ht⟩ k),
    pullback_coeFn ((F.flow ⟨t,ht⟩).toMeasurableEquiv.prodCongr (MeasurableEquiv.refl E))
      (phaseHeatFlow_measurePreserving F ⟨t,ht⟩) k,
    (phaseHeatFlow_measurePreserving F ⟨t,ht⟩).quasiMeasurePreserving.ae
      (compactPhaseHeatQuotient_memLp F hf hc hheat t ht).2.2.coeFn_toLp] with z hz hs hp hk
  change (phaseHeatMovingGeneratorLp F hf hc hheat t) z = _ at hz
  change (phaseHeatPullback F ⟨t,ht⟩ k) z = _ at hp
  rw [hz,hs]
  simp only [Pi.smul_apply, smul_eq_mul, hp, phaseHeatMovingGenerator, projIcc_of_mem _ ht]
  congr 1
  exact hk.symm

end AcceleratedLogConcave.Kinetic.Reheating
