import AcceleratedLogConcave.Gibbs.HeatHessian
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Actual conditional laws and division-free jets

The Gaussian variance is `1 - ρ²`. The normalized posterior uses the ENNReal
partition function and ENNReal density from `Gibbs.heatPosterior`. Defining jets
by center derivatives avoids a singular division by probability time at zero;
the identification with scaled spatial derivatives is a separate theorem.
-/

noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def primitivePotential (F : E → ℝ) (x : E) (r : ℝ) (z : E) : ℝ := F (x + r • z)

def primitiveObservable (F : E → ℝ) (x : E) (r : ℝ) (z : E) : E :=
  gradient F (x + r • z)

def conditionalVariance (ρ : ℝ) : ℝ := 1 - ρ ^ 2

theorem conditionalVariance_pos {ρ : ℝ} (hlo : -1 < ρ) (hhi : ρ < 1) :
    0 < conditionalVariance ρ := by
  unfold conditionalVariance
  nlinarith [mul_pos (show 0 < 1 - ρ by linarith) (show 0 < 1 + ρ by linarith)]

@[simp] theorem conditionalVariance_zero : conditionalVariance 0 = 1 := by
  norm_num [conditionalVariance]

def conditionalLaw (F : E → ℝ) (x : E) (r ρ : ℝ) (y : E) : Measure E :=
  Gibbs.heatPosterior (primitivePotential F x r) (conditionalVariance ρ) (ρ • y)

def baseLaw (F : E → ℝ) (x : E) (r : ℝ) : Measure E :=
  Gibbs.heatPosterior (primitivePotential F x r) 1 0

@[simp] theorem conditionalLaw_zero (F : E → ℝ) (x : E) (r : ℝ) (y : E) :
    conditionalLaw F x r 0 y = baseLaw F x r := by
  simp [conditionalLaw, baseLaw]

def conditionalMean (F : E → ℝ) (x : E) (r ρ : ℝ) (y : E) : E :=
  ∫ z, primitiveObservable F x r z ∂conditionalLaw F x r ρ y

def conditionalPositionMean (F : E → ℝ) (x : E) (r ρ : ℝ) (y : E) : E :=
  ∫ z, z ∂conditionalLaw F x r ρ y

@[simp] theorem conditionalMean_zero (F : E → ℝ) (x : E) (r : ℝ) (y : E) :
    conditionalMean F x r 0 y = ∫ z, primitiveObservable F x r z ∂baseLaw F x r := by
  simp [conditionalMean]

def interpolationMap (ρ : ℝ) (p : E × E) : E :=
  ρ • p.1 + Real.sqrt (conditionalVariance ρ) • p.2

def interpolationLaw (F : E → ℝ) (x : E) (r ρ : ℝ) : Measure E :=
  (baseLaw F x r |>.prod (stdGaussian E)).map (interpolationMap ρ)

/-- The actual covariance operator, including at probability time zero. -/
def firstScaledJet (F : E → ℝ) (x : E) (r ρ : ℝ) (y : E) : E →L[ℝ] E :=
  (conditionalVariance ρ)⁻¹ • ∫ z,
    (innerSL ℝ (z - conditionalPositionMean F x r ρ y)).smulRight
      (primitiveObservable F x r z - conditionalMean F x r ρ y)
    ∂conditionalLaw F x r ρ y

/-- Center derivatives provide the nonsingular realization of all scaled jets. -/
def scaledJet (q : ℕ) (F : E → ℝ) (x : E) (r ρ : ℝ) (y : E) :=
  iteratedFDeriv ℝ q
    (fun c : E ↦ ∫ z, primitiveObservable F x r z ∂
      Gibbs.heatPosterior (primitivePotential F x r) (conditionalVariance ρ) c) (ρ • y)

def probabilityVelocity (F : E → ℝ) (x : E) (r ρ : ℝ) (y : E) : E :=
  -r • conditionalMean F x r ρ y

end AcceleratedLogConcave.Conditional
