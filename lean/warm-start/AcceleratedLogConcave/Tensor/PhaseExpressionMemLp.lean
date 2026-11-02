import AcceleratedLogConcave.Tensor.PhaseAnalyticEnvironment
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Genuine square integrability of every evaluated expression, proved before
and independently of its quantitative integral estimate. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction PolynomialClosure
variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}

namespace PhaseAnalyticEnvironment

theorem expression_memLp_two (P : PhaseAnalyticEnvironment σ D) {r : ℕ} (e : Expr σ r) :
    MemLp (Expr.evaluate P.coefficients P.potential e) 2
      P.toSmoothGibbsEnvironment.law := by
  let : IsFiniteMeasure P.toSmoothGibbsEnvironment.law := P.finite
  apply memLp_piLp_iff.mpr
  intro a
  have hs := contDiff_section P.coefficients P.potential P.coefficient_smooth P.smooth e a
  have hj := section_hasPolynomialJets P.coefficients P.potential P.coefficient_smooth
    P.smooth P.coefficient_jets P.score_jets e a
  apply (memLp_two_iff_integrable_sq_norm hs.continuous.aestronglyMeasurable).mpr
  exact ((hj []).norm.pow 2).integrable
    (hs.continuous.norm.pow 2).aestronglyMeasurable P.moments

end PhaseAnalyticEnvironment
end AcceleratedLogConcave.Tensor.Ordered.Graph
