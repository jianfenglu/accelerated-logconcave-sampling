import AcceleratedLogConcave.Conditional.Centering.Construction
import AcceleratedLogConcave.Conditional.Centering.Stationary
import AcceleratedLogConcave.Conditional.Centering.WeightedDivergence
import AcceleratedLogConcave.Conditional.Centering.SteinBridge
import AcceleratedLogConcave.Kinetic.ReferenceFlow

/-! Product-law invariance of the actual complete centering field, derived
from the pointwise Stein equation. Product density normalization is taken from
the actual probability law, and its density formula is reused from W05. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional.Centering
open Kinetic Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem phaseDensity_contDiff {p : E → ℝ} (hp : ContDiff ℝ 1 p) :
    ContDiff ℝ 1 (coupledDensity p standardGaussianDensity) := by
  exact (hp.comp (contDiff_fst.comp WithLp.contDiff_ofLp)).mul
    (standardGaussianDensity_contDiff.comp (contDiff_snd.comp WithLp.contDiff_ofLp))

/-- The actual product density is integrable because its associated measure
is the normalized independent product law. -/
theorem integrable_phaseDensity {ξ : Measure E} [IsProbabilityMeasure ξ]
    {p : E → ℝ} (hp : Continuous p) (hp0 : ∀ y, 0 ≤ p y)
    (hξ : ξ = volume.withDensity (fun y => ENNReal.ofReal (p y))) :
    Integrable (coupledDensity p standardGaussianDensity) volume := by
  have hpos (z : Phase E) : 0 ≤ coupledDensity p standardGaussianDensity z :=
    mul_nonneg (hp0 z.fst) (standardGaussianDensity_pos z.snd).le
  have hc : Continuous (coupledDensity p standardGaussianDensity) :=
    (hp.comp (WithLp.prod_continuous_ofLp 2 E E).fst).mul
      (standardGaussianDensity_contDiff.continuous.comp (WithLp.prod_continuous_ofLp 2 E E).snd)
  apply (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable
    (Eventually.of_forall hpos)).mp
  have hmass : (∫⁻ z : Phase E, ENNReal.ofReal (coupledDensity p standardGaussianDensity z)) = 1 := by
    have hh := congrArg (fun μ : Measure (Phase E) => μ univ)
      (coupledPhaseMeasure_density ξ p hp hp0 hξ)
    simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hh.symm
  rw [hmass]
  exact ENNReal.one_ne_top

/-- The complete centering flow preserves the independent position/Gaussian
law. All flow, density and Jacobian claims are derived; only the analytic
Stein equation remains an explicit input to this generic implication. -/
theorem centeringFlowHomeomorph_measurePreserving_of_stein
    {Kt : E → E →L[ℝ] E} {M : E → E}
    (hKt : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y, ‖Kt y‖ ≤ A)
    {B : ℝ≥0} (hlip : LipschitzWith B M) (u : E) {s : ℝ} (hs : 0 < s)
    {ξ : Measure E} [IsProbabilityMeasure ξ]
    {p : E → ℝ} (hp : ContDiff ℝ 1 p) (hp0 : ∀ y, 0 ≤ p y)
    (hξ : ξ = volume.withDensity (fun y => ENNReal.ofReal (p y)))
    (hstein : ∀ y g, fderiv ℝ p y (Kt y g) + p y * fluxDivergence (fun w => Kt w g) y =
      -p y * inner ℝ (M y - u) g) (t : ℝ) :
    MeasurePreserving (centeringFlowHomeomorph hKt hM hA hbound hlip u hs t)
      (coupledPhaseMeasure ξ) (coupledPhaseMeasure ξ) := by
  rw [coupledPhaseMeasure_density ξ p hp.continuous hp0 hξ]
  unfold centeringFlowHomeomorph
  apply completeFlowHomeomorph_measurePreserving _ _ _ _ volume (phaseDensity_contDiff hp)
    (integrable_phaseDensity hp.continuous hp0 hξ)
    (fun z => mul_nonneg (hp0 z.fst) (standardGaussianDensity_pos z.snd).le)
    (density_divergence_zero_of_stein hKt hM u s p hp hstein)

/-- Compact-test Stein integration by parts suffices for stationarity of the
constructed complete flow; a stationary-flow premise is not required. -/
theorem centeringFlowHomeomorph_measurePreserving_of_compact_test
    {Kt : E → E →L[ℝ] E} {M : E → E}
    (hKt : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y, ‖Kt y‖ ≤ A)
    {B : ℝ≥0} (hlip : LipschitzWith B M) (u : E) {s : ℝ} (hs : 0 < s)
    {ξ : Measure E} [IsProbabilityMeasure ξ]
    {p : E → ℝ} (hp : ContDiff ℝ 1 p) (hp0 : ∀ y, 0 < p y)
    (hξ : ξ = volume.withDensity (fun y => ENNReal.ofReal (p y)))
    {score : E → E} (hscorec : Continuous score)
    (hscore : ∀ y, HasFDerivAt p ((-p y) • innerSL ℝ (score y)) y)
    (hweak : ∀ (g : E) (φ : E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y, p y * inner ℝ (M y - u) g * φ y) =
        ∫ y, p y * fderiv ℝ φ y (Kt y g)) (t : ℝ) :
    MeasurePreserving (centeringFlowHomeomorph hKt hM hA hbound hlip u hs t)
      (coupledPhaseMeasure ξ) (coupledPhaseMeasure ξ) :=
  centeringFlowHomeomorph_measurePreserving_of_stein hKt hM hA hbound hlip u hs hp
    (fun y => (hp0 y).le) hξ
    (pointwise_stein_of_compact_test u hp hp0 hscorec hM.continuous hKt hscore hweak) t

/-- The literal integrated mean plus the retained original Gaussian momentum
has the shifted Gaussian law under the independent invariant starting law. -/
theorem centeringFlow_output_law_of_stein
    {Kt : E → E →L[ℝ] E} {M : E → E}
    (hKt : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y, ‖Kt y‖ ≤ A)
    {B : ℝ≥0} (hlip : LipschitzWith B M) (u : E) {s : ℝ} (hs : 0 < s)
    {ξ : Measure E} [IsProbabilityMeasure ξ]
    {p : E → ℝ} (hp : ContDiff ℝ 1 p) (hp0 : ∀ y, 0 ≤ p y)
    (hξ : ξ = volume.withDensity (fun y => ENNReal.ofReal (p y)))
    (hstein : ∀ y g, fderiv ℝ p y (Kt y g) + p y * fluxDivergence (fun w => Kt w g) y =
      -p y * inner ℝ (M y - u) g) :
    (coupledPhaseMeasure ξ).map (fun z => s • z.snd +
      ∫ τ in (0 : ℝ)..1, M (centeringFlow hKt hM hA hbound hlip u hs z τ).fst) =
      (stdGaussian E).map (fun g => u + s • g) := by
  have hmp := centeringFlowHomeomorph_measurePreserving_of_stein hKt hM hA hbound hlip u hs hp hp0 hξ hstein 1
  have hfun : (fun z : Phase E => s • z.snd +
      ∫ τ in (0 : ℝ)..1, M (centeringFlow hKt hM hA hbound hlip u hs z τ).fst) =
      fun z => u + s • (centeringFlowHomeomorph hKt hM hA hbound hlip u hs 1 z).snd := by
    funext z
    exact centeringFlow_integrated_output hKt hM hA hbound hlip u hs z
  rw [hfun]
  exact endpoint_shiftedGaussian_law hmp u s

end AcceleratedLogConcave.Conditional.Centering
