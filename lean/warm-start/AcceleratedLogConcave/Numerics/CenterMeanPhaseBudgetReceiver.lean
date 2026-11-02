import AcceleratedLogConcave.Numerics.CenterMeanPhaseAnalytic
import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoefficientSmooth
import AcceleratedLogConcave.Analysis.PhasePrimitivePolynomial
import AcceleratedLogConcave.Tensor.PhaseAnalyticEnvironment

/-! Original-data phase receiver from genuine primitive split bounds. Those
bounds themselves supply coefficient polynomial tails; no extra transport-tail,
finished-expression moment, or integration-by-parts premise is introduced. -/
noncomputable section
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open CenteringFlowLp Tensor.Ordered.Graph
variable {D : ℕ}

def actualPhaseAnalyticEnvironmentOfBudgets (d : Data (Fin D)) (ellScale a : ℝ)
    {C R : ℝ}
    (hprim : PhasePrimitiveBudgets (phaseCoefficients d ellScale a) (phasePotential d) C R) :
    PhaseAnalyticEnvironment Tensor.PhaseExpression.signature (D+D) where
  toSmoothGibbsEnvironment := actualPhaseGibbsEnvironment d
  coefficients := phaseCoefficients d ellScale a
  coefficient_smooth := phaseCoefficients_smooth d ellScale a
  coefficient_jets := hprim.coefficient_polynomialJets (phaseCoefficients_smooth d ellScale a)

theorem actualPhaseAnalyticEnvironmentOfBudgets_law (d : Data (Fin D)) (ellScale a : ℝ)
    {C R : ℝ}
    (hprim : PhasePrimitiveBudgets (phaseCoefficients d ellScale a) (phasePotential d) C R) :
    (actualPhaseAnalyticEnvironmentOfBudgets d ellScale a hprim).toSmoothGibbsEnvironment.law =
      phaseSeedLaw d := actualPhaseGibbsEnvironment_law d

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
