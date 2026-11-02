import AcceleratedLogConcave.Analysis.AnglePhaseProductMoments
import AcceleratedLogConcave.Analysis.AngleProductStationaryLp
import AcceleratedLogConcave.Analysis.AnglePhaseSourceJet

/-! Actual positive angle jets form a genuine common-source L² derivative
ladder. The literal primitive split supplier remains explicitly conditional. -/
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

def angleSourceJet (T : E → E) (q a : ℝ) (k : ℕ) (p : X) : EP :=
  (q⁻¹)^(k+1) • vectorSection (angleCoefficients T p.1 q a) gaussianPotential (jet F k) p.2

theorem smooth_angleSourceJet (T : E → E) (hT : ContDiff ℝ ∞ T) (q a : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (angleSourceJet T q a k) :=
  (smooth_parameter_angleVector T hT q a (jet F k)).const_smul _

theorem hasDerivAt_angleSourceJet (T : E → E) (hT : ContDiff ℝ ∞ T)
    (q a : ℝ) (k : ℕ) (p : X) (t : ℝ) :
    HasDerivAt (fun u => angleSourceJet T q a k (parameterRotation q u p))
      (angleSourceJet T q a (k+1) (parameterRotation q t p)) t := by
  have hz := hasDerivAt_rotationOrbit (D := D) q p.2 t
  rw [rotationVelocity_eq_generator] at hz
  have h := (hasDerivAt_vectorSection_along (angleCoefficients T p.1 q a) gaussianPotential
    (smooth_angleCoefficients T hT p.1 q a) gaussianPotential_smooth
    (angleCoefficients_skew T p.1 q a) (jet F k) hz).const_smul ((q⁻¹)^(k+1))
  change HasDerivAt (fun u => angleSourceJet T q a k (parameterRotation q u p))
    ((q⁻¹)^(k+1) • (q⁻¹ • vectorSection (angleCoefficients T p.1 q a)
      gaussianPotential (jet F (k+1)) (rotationOrbit q p.2 t))) t at h
  simpa only [angleSourceJet,parameterRotation,smul_smul,← pow_succ] using h

theorem angleSourceJet_memLp (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (k : ℕ) : MemLp (angleSourceJet T q a k) 2 (μ.prod (stdGaussian EP)) := by
  unfold angleSourceJet
  exact (angle_product_expression_memLp μ T hT q a C S hC hS hS1 hb (jet F k)).const_smul
    ((q⁻¹)^(k+1))

def angleSourceJetLp (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (k : ℕ) (t : ℝ) : Lp EP 2 (μ.prod (stdGaussian EP)) :=
  parameterLpOrbit μ q ((angleSourceJet_memLp μ T hT q a C S hC hS hS1 hb k).toLp
    (angleSourceJet T q a k)) t

theorem hasDerivAt_angleSourceJetLp (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (k : ℕ) (t : ℝ) :
    HasDerivAt (angleSourceJetLp μ T hT q a C S hC hS hS1 hb k)
      (angleSourceJetLp μ T hT q a C S hC hS hS1 hb (k+1) t) t :=
  hasDerivAt_parameterLpOrbit_of_source μ q (angleSourceJet T q a k)
    (angleSourceJet T q a (k+1))
    (angleSourceJet_memLp μ T hT q a C S hC hS hS1 hb k)
    (angleSourceJet_memLp μ T hT q a C S hC hS hS1 hb (k+1))
    (smooth_angleSourceJet T hT q a (k+1)).continuous
    (fun t p => hasDerivAt_angleSourceJet T hT q a k p t) t

theorem iteratedDeriv_angleSourceJetLp (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (k n : ℕ) :
    iteratedDeriv n (angleSourceJetLp μ T hT q a C S hC hS hS1 hb k) =
      angleSourceJetLp μ T hT q a C S hC hS hS1 hb (k+n) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,Nat.add_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    exact (hasDerivAt_angleSourceJetLp μ T hT q a C S hC hS hS1 hb (k+n) t).deriv

theorem contDiff_angleSourceJetLp (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (k : ℕ) : ContDiff ℝ ∞ (angleSourceJetLp μ T hT q a C S hC hS hS1 hb k) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [iteratedDeriv_angleSourceJetLp μ T hT q a C S hC hS hS1 hb k n]
  intro t
  exact (hasDerivAt_angleSourceJetLp μ T hT q a C S hC hS hS1 hb (k+n) t).differentiableAt
end AcceleratedLogConcave.Analysis.AnglePhase
