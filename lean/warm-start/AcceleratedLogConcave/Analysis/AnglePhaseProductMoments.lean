import AcceleratedLogConcave.Analysis.AnglePhaseIntegrability
import AcceleratedLogConcave.Analysis.AnglePhaseParameterSmoothness
import AcceleratedLogConcave.Analysis.UniformFiberL2

/-! The midpoint can have any probability law. No midpoint moment or
coefficient-independence assertion is substituted for the actual product law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.Ordered.Graph Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem angle_product_expression_memLp (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (e : Expr signature 1) :
    MemLp (fun p : E × EP => vectorSection (angleCoefficients T p.1 q a)
      gaussianPotential e p.2) 2 (μ.prod (stdGaussian EP)) := by
  apply UniformFiberL2.memLp_prod_of_uniform_energy μ (stdGaussian EP) _
    (smooth_parameter_angleVector T hT q a e).continuous.aestronglyMeasurable
    (fun M => angle_expression_memLp T hT M q a C S (hb M) e)
    (((D+D : ℕ) : ℝ) * Tensor.AdjointReduction.PhaseBudget.Q C e.size * S^(-2*(e.weight : ℝ)))
  intro M
  exact angle_expression_integral_norm_sq_le T hT M q a C S hC hS hS1 (hb M) e

theorem angle_product_expression_energy (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (e : Expr signature 1) :
    (∫ p : E × EP, ‖vectorSection (angleCoefficients T p.1 q a)
      gaussianPotential e p.2‖^2 ∂μ.prod (stdGaussian EP)) ≤
      ((D+D : ℕ) : ℝ) * Tensor.AdjointReduction.PhaseBudget.Q C e.size * S^(-2*(e.weight : ℝ)) := by
  apply UniformFiberL2.integral_prod_norm_sq_le μ (stdGaussian EP) _
    (smooth_parameter_angleVector T hT q a e).continuous.aestronglyMeasurable
    (fun M => angle_expression_memLp T hT M q a C S (hb M) e)
  intro M
  exact angle_expression_integral_norm_sq_le T hT M q a C S hC hS hS1 (hb M) e
end AcceleratedLogConcave.Analysis.AnglePhase
