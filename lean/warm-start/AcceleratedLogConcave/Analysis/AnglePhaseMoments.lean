import AcceleratedLogConcave.Analysis.AnglePhaseCoefficients
import AcceleratedLogConcave.Analysis.PhasePrimitivePolynomial
import AcceleratedLogConcave.Tensor.PhaseVectorRms
import AcceleratedLogConcave.Tensor.PhaseVectorSource

/-! Actual Gaussian phase moments for the normalized displacement gradient.
The quantitative primitive split supplier remains explicit and unpaid here;
qualitative moments and polynomial jets are derived rather than assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.Ordered.Graph Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def angleAnalyticEnvironment (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a C S : ℝ)
    (hb : PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S) :
    PhaseAnalyticEnvironment signature (D+D) where
  toSmoothGibbsEnvironment := gaussianEnvironment (D+D)
  coefficients := angleCoefficients T M q a
  coefficient_smooth := smooth_angleCoefficients T hT M q a
  coefficient_jets := hb.coefficient_polynomialJets (smooth_angleCoefficients T hT M q a)

theorem angle_expression_integral_norm_sq_le (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a C S : ℝ) (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (e : Expr signature 1) :
    (∫ z : EP, ‖vectorSection (angleCoefficients T M q a) gaussianPotential e z‖^2
      ∂stdGaussian EP) ≤
      ((D+D : ℕ) : ℝ) * Tensor.AdjointReduction.PhaseBudget.Q C e.size * S^(-2*(e.weight : ℝ)) := by
  let P := angleAnalyticEnvironment T hT M q a C S hb
  let : IsProbabilityMeasure P.toSmoothGibbsEnvironment.law :=
    gaussianEnvironment_probability (D+D)
  have h := phase_expression_vector_integral_norm_sq_le_Q P hC hS hS1 hb e
  change (∫ z : EP, ‖Expr.evaluate (angleCoefficients T M q a) gaussianPotential e z‖^2
      ∂(gaussianEnvironment (D+D)).law) ≤ _ at h
  rw [gaussianEnvironment_law] at h
  simpa only [norm_vectorSection] using h
end AcceleratedLogConcave.Analysis.AnglePhase
