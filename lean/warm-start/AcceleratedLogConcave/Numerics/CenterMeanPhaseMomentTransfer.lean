import AcceleratedLogConcave.Numerics.CenterMeanPhaseBudgetReceiver
import AcceleratedLogConcave.Tensor.PhaseSourceJetMoment
import AcceleratedLogConcave.Tensor.PhaseVectorSource

/-! Concrete phase-law moment transfer from genuine primitive split bounds.
The spatial primitive budgets are the remaining quantitative supplier. There is
no finished-expression moment, integrability, or integration-by-parts premise. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Tensor.AdjointReduction Tensor.Ordered.Graph Tensor.PolynomialClosure
variable {D : ℕ}
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def phaseEnvironmentOfSplitBudgets (d : Data (Fin D)) (L a : ℝ) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R) :
    PhaseAnalyticEnvironment signature (D+D) :=
  actualPhaseAnalyticEnvironmentOfBudgets d L a hb

theorem phaseEnvironmentOfSplitBudgets_law (d : Data (Fin D)) (L a : ℝ) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R) :
    (phaseEnvironmentOfSplitBudgets d L a hb).toSmoothGibbsEnvironment.law = phaseSeedLaw d :=
  actualPhaseAnalyticEnvironmentOfBudgets_law d L a hb

theorem actual_phase_observable_jet_moment (d : Data (Fin D)) (L a : ℝ) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R) (k : ℕ) :
    (∫ z, ‖vectorSection (phaseCoefficients d L a) (phasePotential d) (jet F k) z‖^2
      ∂phaseSeedLaw d) ≤
      ((D+D : ℕ) : ℝ) * PhaseBudget.Q c (5*(k+1)+1) * R^(-4*((k : ℝ)+1)) := by
  let A := phaseEnvironmentOfSplitBudgets d L a hb
  have hμ : A.toSmoothGibbsEnvironment.law = phaseSeedLaw d :=
    phaseEnvironmentOfSplitBudgets_law d L a hb
  let : IsProbabilityMeasure A.toSmoothGibbsEnvironment.law := by
    rw [hμ]
    infer_instance
  have h := phase_observable_jet_moment A hc hR hR1 hb k
  rw [hμ] at h
  simpa only [A,phaseEnvironmentOfSplitBudgets,actualPhaseAnalyticEnvironmentOfBudgets,
    actualPhaseGibbsEnvironment,norm_vectorSection] using h

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
