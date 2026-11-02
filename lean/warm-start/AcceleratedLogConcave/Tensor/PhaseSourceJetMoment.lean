import AcceleratedLogConcave.Tensor.PhaseVectorRms
import AcceleratedLogConcave.Tensor.PhaseExpressionGrammar

/-! The phase recurrence moment specialization. This is an abstract expression
result only. Identifying it with the actual ODE source jet and supplying the
original-data primitive estimates are separate theorems, not hidden fields. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction PhaseExpression

/-- Positive-order generic observable recurrence, k+1 applications. -/
theorem phase_observable_jet_moment {D : ℕ}
    (A : PhaseAnalyticEnvironment PhaseExpression.signature D) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : PhasePrimitiveBudgets A.coefficients A.potential c R)
    [IsProbabilityMeasure A.toSmoothGibbsEnvironment.law] (k : ℕ) :
    (∫ y, ‖Expr.evaluate A.coefficients A.potential (jet F k) y‖^2
      ∂A.toSmoothGibbsEnvironment.law) ≤
      (D : ℝ) * PhaseBudget.Q c (5*(k+1)+1) * R^(-4*((k : ℝ)+1)) := by
  have h := phase_expression_vector_integral_norm_sq_le_Q A hc hR hR1 hb (jet F k)
  rw [(observable_jet_budgets k).1, (observable_jet_budgets k).2] at h
  convert h using 1
  push_cast
  congr 2
  ring

/-- Position saves one smoothing power before squaring. In a phase space of
physical dimension 2D, instantiate this theorem at ambient dimension 2D. -/
theorem phase_position_jet_moment {D : ℕ}
    (A : PhaseAnalyticEnvironment PhaseExpression.signature D) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : PhasePrimitiveBudgets A.coefficients A.potential c R)
    [IsProbabilityMeasure A.toSmoothGibbsEnvironment.law] (k : ℕ) :
    (∫ y, ‖Expr.evaluate A.coefficients A.potential (jet P k) y‖^2
      ∂A.toSmoothGibbsEnvironment.law) ≤
      (D : ℝ) * PhaseBudget.Q c (5*(k+1)+1) * R^(-2*(2*(k : ℝ)+1)) := by
  have h := phase_expression_vector_integral_norm_sq_le_Q A hc hR hR1 hb (jet P k)
  rw [(position_jet_budgets k).1, (position_jet_budgets k).2] at h
  convert h using 1
  push_cast
  congr 2
end AcceleratedLogConcave.Tensor.Ordered.Graph
