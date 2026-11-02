import AcceleratedLogConcave.Analysis.AnglePhaseJetEnergy
import AcceleratedLogConcave.Analysis.AnglePhaseVectorJet

/-! The positive Gaussian jet ladder starts from the literal displacement,
not an unspecified antiderivative. Base MemLp is isolated for the original
source-law receiver, where it follows from the existing actual action MemLp. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.Ordered.Graph Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "X" => E × EP

def parameterDisplacement (T : E → E) (q a : ℝ) (p : X) : EP :=
  displacementVector T p.1 q a p.2

theorem hasDerivAt_parameterDisplacement (T : E → E) (hT : ContDiff ℝ ∞ T)
    (q a : ℝ) (p : X) (t : ℝ) :
    HasDerivAt (fun u => parameterDisplacement T q a (parameterRotation q u p))
      (angleSourceJet T q a 0 (parameterRotation q t p)) t := by
  have hz := hasDerivAt_rotationOrbit (D := D) q p.2 t
  rw [rotationVelocity_eq_generator] at hz
  have h := hasDerivAt_sourceVector_along (angleCoefficients T p.1 q a) gaussianPotential
    (displacementVector T p.1 q a) (smooth_angleCoefficients T hT p.1 q a)
    (fun i => by simpa only [displacementVector_apply] using
      smooth_displacementCoordinate T hT p.1 q a i)
    (angleCoefficients_skew T p.1 q a) F
    (fun i j => by simpa only [displacementVector_apply] using
      angleCoefficients_gradient T p.1 q a i j) hz
  simpa only [parameterDisplacement,parameterRotation,angleSourceJet,Nat.zero_add,pow_one,jet] using h

def displacementLp (μ : Measure E) [IsProbabilityMeasure μ] (T : E → E) (q a : ℝ)
    (hf : MemLp (parameterDisplacement T q a) 2 (μ.prod (stdGaussian EP)))
    (t : ℝ) : Lp EP 2 (μ.prod (stdGaussian EP)) :=
  parameterLpOrbit μ q (hf.toLp (parameterDisplacement T q a)) t

theorem hasDerivAt_displacementLp (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (hf : MemLp (parameterDisplacement T q a) 2 (μ.prod (stdGaussian EP))) (t : ℝ) :
    HasDerivAt (displacementLp μ T q a hf)
      (angleSourceJetLp μ T hT q a C S hC hS hS1 hb 0 t) t :=
  hasDerivAt_parameterLpOrbit_of_source μ q (parameterDisplacement T q a)
    (angleSourceJet T q a 0) hf (angleSourceJet_memLp μ T hT q a C S hC hS hS1 hb 0)
    (smooth_angleSourceJet T hT q a 0).continuous
    (fun t p => hasDerivAt_parameterDisplacement T hT q a p t) t

theorem iteratedDeriv_displacementLp (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (hf : MemLp (parameterDisplacement T q a) 2 (μ.prod (stdGaussian EP))) (k : ℕ) :
    iteratedDeriv (k+1) (displacementLp μ T q a hf) =
      angleSourceJetLp μ T hT q a C S hC hS hS1 hb k := by
  induction k with
  | zero =>
    simp only [zero_add,iteratedDeriv_one]
    funext t
    exact (hasDerivAt_displacementLp μ T hT q a C S hC hS hS1 hb hf t).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    exact (hasDerivAt_angleSourceJetLp μ T hT q a C S hC hS hS1 hb k t).deriv

theorem contDiff_displacementLp (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (hf : MemLp (parameterDisplacement T q a) 2 (μ.prod (stdGaussian EP))) :
    ContDiff ℝ ∞ (displacementLp μ T q a hf) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero]
    intro t
    exact (hasDerivAt_displacementLp μ T hT q a C S hC hS hS1 hb hf t).differentiableAt
  | succ k =>
    rw [iteratedDeriv_displacementLp μ T hT q a C S hC hS hS1 hb hf k]
    intro t
    exact (hasDerivAt_angleSourceJetLp μ T hT q a C S hC hS hS1 hb k t).differentiableAt
end AcceleratedLogConcave.Analysis.AnglePhase
