import AcceleratedLogConcave.Root.SourceWarmSampler
import AcceleratedLogConcave.Probability.WarmInitialization

/-! Exact original-target warm initialization: two independent standard
Gaussian draws, no oracle calls, and the same physical smoothing variance. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.SourceWarmInitialization
open Oracle
variable {d : ℕ}

theorem noise_eq (h : ℝ) (hh : 0≤h) :
    Probability.gaussianInitializationNoise (Point d) h=
      Channels.noise (Schedule.Dyadic.sourceVariance h) := by
  rw [Probability.gaussianInitializationNoise,Channels.noise_eq_scaled_stdGaussian]
  congr 1
  funext z
  change (Real.sqrt 2*h) • z=Real.sqrt (2*h^2) • z
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.sqrt_sq hh]

/-- The initialization is the exact heat convolution and independent momentum. -/
theorem law_eq (ν : Measure (Point d)) [IsProbabilityMeasure ν] (h : ℝ) (hh : 0≤h) :
    Probability.gaussianWarmInitializationLaw ν h=
      (Channels.forward ν (Schedule.Dyadic.sourceVariance h)).prod (stdGaussian (Point d)) := by
  rw [Probability.gaussianWarmInitializationLaw_eq,Probability.additiveNoiseMomentumLaw,noise_eq h hh]
  rfl

/-- The supplied original-target warm input meets the exact smoothed joint
warmness assumption, without constructing that supplied input. -/
theorem warm {V : Point d→ℝ} (hI : Integrable (fun x => Real.exp (-V x)))
    (ν : Measure (Point d)) [IsProbabilityMeasure ν] {B h : ℝ} (hh : 0≤h)
    (hw : Probability.L2Warm (volume.tilted (fun x => -V x)) ν B) :
    Probability.L2Warm (Schedule.Dyadic.phaseReference V (Schedule.Dyadic.sourceVariance h))
      (Probability.gaussianWarmInitializationLaw ν h) B := by
  let := isProbabilityMeasure_tilted hI
  have hw' := hw.gaussianWarmInitialization h
  rw [law_eq _ h hh] at hw'
  simpa only [Schedule.Dyadic.phaseReference,Schedule.Dyadic.cooledLaw,
    Schedule.Dyadic.targetLaw,Schedule.Dyadic.variance_zero] using hw'
end AcceleratedLogConcave.Root.SourceWarmInitialization
