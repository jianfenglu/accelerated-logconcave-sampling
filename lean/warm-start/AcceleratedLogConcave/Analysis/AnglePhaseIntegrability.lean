import AcceleratedLogConcave.Analysis.AnglePhaseMoments
import AcceleratedLogConcave.Tensor.PhaseVectorSourceRegularity

/-! Integrability is established before the phase energy inequality is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.Ordered.Graph Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem angle_expression_memLp (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a C S : ℝ)
    (hb : PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (e : Expr signature 1) :
    MemLp (vectorSection (angleCoefficients T M q a) gaussianPotential e) 2 (stdGaussian EP) := by
  let P := angleAnalyticEnvironment T hT M q a C S hb
  have h := memLp_vectorSection P e
  change MemLp (vectorSection (angleCoefficients T M q a) gaussianPotential e) 2
    (gaussianEnvironment (D+D)).law at h
  rwa [gaussianEnvironment_law] at h
end AcceleratedLogConcave.Analysis.AnglePhase
