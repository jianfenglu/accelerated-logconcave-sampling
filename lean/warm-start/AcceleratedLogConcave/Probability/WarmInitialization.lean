import AcceleratedLogConcave.Probability.WarmnessKernel
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Warm initialization by independent additive noise and momentum

The laws below are actual pushforwards of independent product measures. The
Gaussian specialization uses Mathlib's finite-dimensional `stdGaussian`, with
the manuscript's exact `√2 * h` noise scale. Identification of the smoothed
Gibbs reference with `π_{V_{2h²}}` belongs to W02 and is not assumed here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace AcceleratedLogConcave.Probability

section AdditiveNoise

variable {X P : Type*} [MeasurableSpace X] [Add X] [MeasurableAdd₂ X]
  [MeasurableSpace P]

/-- Add independent noise with law `ρ` to an input with law `ν`. -/
def additiveNoiseLaw (ν ρ : Measure X) : Measure X :=
  (ν.prod ρ).map (fun az => az.1 + az.2)

instance additiveNoiseLaw_isProbabilityMeasure (ν ρ : Measure X)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (additiveNoiseLaw ν ρ) := by
  unfold additiveNoiseLaw
  exact (Measure.isProbabilityMeasure_map_iff measurable_add.aemeasurable).mpr inferInstance

/-- After adding noise, independently initialize momentum with law `γ`. -/
def additiveNoiseMomentumLaw (ν ρ : Measure X) (γ : Measure P) : Measure (X × P) :=
  (additiveNoiseLaw ν ρ).prod γ

instance additiveNoiseMomentumLaw_isProbabilityMeasure (ν ρ : Measure X) (γ : Measure P)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure γ] :
    IsProbabilityMeasure (additiveNoiseMomentumLaw ν ρ γ) := by
  unfold additiveNoiseMomentumLaw
  infer_instance

/-- The sequential law is exactly the joint law obtained from the independent
input, noise, and momentum draws. -/
theorem additiveNoiseMomentumLaw_eq_map (ν ρ : Measure X) (γ : Measure P)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure γ] :
    additiveNoiseMomentumLaw ν ρ γ =
      ((ν.prod ρ).prod γ).map (fun azp => (azp.1.1 + azp.1.2, azp.2)) := by
  simpa only [additiveNoiseMomentumLaw, additiveNoiseLaw, Measure.map_id,
    Prod.map_def, id_eq] using
    (Measure.map_prod_map (ν.prod ρ) γ measurable_add measurable_id)

/-- Adding a common independent noise law contracts squared-L2 warmness. -/
theorem L2Warm.additiveNoise {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {B : ℝ} (h : L2Warm μ ν B)
    (ρ : Measure X) [IsProbabilityMeasure ρ] :
    L2Warm (additiveNoiseLaw μ ρ) (additiveNoiseLaw ν ρ) B :=
  (h.prod_right ρ).map measurable_add

/-- Adding noise and then independent common momentum preserves the original
warmness budget; the reference uses exactly the same initialization. -/
theorem L2Warm.additiveNoiseMomentum {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {B : ℝ} (h : L2Warm μ ν B)
    (ρ : Measure X) (γ : Measure P) [IsProbabilityMeasure ρ] [IsProbabilityMeasure γ] :
    L2Warm (additiveNoiseMomentumLaw μ ρ γ) (additiveNoiseMomentumLaw ν ρ γ) B :=
  (h.additiveNoise ρ).prod_right γ

end AdditiveNoise

section GaussianInitialization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual law of `√2 * h • Z`, with `Z` a standard finite-dimensional Gaussian. -/
def gaussianInitializationNoise (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (h : ℝ) : Measure E :=
  (stdGaussian E).map (fun z => (Real.sqrt 2 * h) • z)

instance gaussianInitializationNoise_isProbabilityMeasure (h : ℝ) :
    IsProbabilityMeasure (gaussianInitializationNoise E h) := by
  unfold gaussianInitializationNoise
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

/-- Law of the manuscript's `(A₀ + √2 h Z₀, p₀)` from three independent draws. -/
def gaussianWarmInitializationLaw (ν : Measure E) (h : ℝ) : Measure (E × E) :=
  ((ν.prod (stdGaussian E)).prod (stdGaussian E)).map
    (fun azp => (azp.1.1 + (Real.sqrt 2 * h) • azp.1.2, azp.2))

/-- The raw Gaussian draw construction equals addition by the scaled-noise law,
followed by adjoining independent standard Gaussian momentum. -/
theorem gaussianWarmInitializationLaw_eq (ν : Measure E) [IsProbabilityMeasure ν] (h : ℝ) :
    gaussianWarmInitializationLaw ν h =
      additiveNoiseMomentumLaw ν (gaussianInitializationNoise E h) (stdGaussian E) := by
  rw [additiveNoiseMomentumLaw_eq_map]
  unfold gaussianWarmInitializationLaw gaussianInitializationNoise
  have hprod := Measure.map_prod_map ν (stdGaussian E) measurable_id
    (measurable_const_smul (Real.sqrt 2 * h) :
      Measurable (fun z : E => (Real.sqrt 2 * h) • z))
  simp only [Measure.map_id] at hprod
  rw [hprod]
  have hprod' := Measure.map_prod_map (ν.prod (stdGaussian E)) (stdGaussian E)
    (measurable_id.prodMap (measurable_const_smul (Real.sqrt 2 * h))) measurable_id
  simp only [Measure.map_id] at hprod'
  rw [hprod']
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

instance gaussianWarmInitializationLaw_isProbabilityMeasure (ν : Measure E)
    [IsProbabilityMeasure ν] (h : ℝ) :
    IsProbabilityMeasure (gaussianWarmInitializationLaw ν h) := by
  rw [gaussianWarmInitializationLaw_eq]
  infer_instance

/-- The W01 probability component of `cor:original-warm`: forward Gaussian heat
and independent Gaussian momentum preserve the supplied squared-L2 budget. -/
theorem L2Warm.gaussianWarmInitialization {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ}
    (hν : L2Warm μ ν B) (h : ℝ) :
    L2Warm (gaussianWarmInitializationLaw μ h) (gaussianWarmInitializationLaw ν h) B := by
  rw [gaussianWarmInitializationLaw_eq, gaussianWarmInitializationLaw_eq]
  exact hν.additiveNoiseMomentum (gaussianInitializationNoise E h) (stdGaussian E)

end GaussianInitialization

end AcceleratedLogConcave.Probability
