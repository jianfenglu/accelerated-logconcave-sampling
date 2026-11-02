import AcceleratedLogConcave.Tensor.PhaseVectorSource
import AcceleratedLogConcave.Tensor.PhaseExpressionMemLp

/-! Qualitative vector source regularity and genuine L² membership. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PhaseSourceJetInduction
open CoordinateReduction PhaseExpression Ordered.Graph
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

theorem contDiff_vectorSection (ρ : CoefficientEnvironment signature D) (H : E → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    (e : Expr signature 1) : ContDiff ℝ ∞ (vectorSection ρ H e) := by
  have hp : ContDiff ℝ ∞ (fun x i => sectionValue ρ H e ![i] x) :=
    contDiff_pi.mpr (fun i => contDiff_section ρ H hρ hH e ![i])
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D => ℝ)).symm.contDiff.comp hp
  convert h using 1
  funext x
  ext i
  rfl

theorem memLp_vectorSection (P : PhaseAnalyticEnvironment signature D) (e : Expr signature 1) :
    MemLp (vectorSection P.coefficients P.potential e) 2 P.toSmoothGibbsEnvironment.law := by
  exact (P.expression_memLp_two e).continuousLinearMap_comp
    rankOneVectorEquiv.toContinuousLinearEquiv.toContinuousLinearMap

end AcceleratedLogConcave.Tensor.PhaseSourceJetInduction
