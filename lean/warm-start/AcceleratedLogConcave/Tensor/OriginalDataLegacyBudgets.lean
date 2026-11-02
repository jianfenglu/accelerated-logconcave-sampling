import AcceleratedLogConcave.Tensor.OriginalDataFlowBounds
import AcceleratedLogConcave.Tensor.InverseLegacySlotChart
import AcceleratedLogConcave.Tensor.LegacyOrderConstantBridge

/-!
The existing analytic induction and inverse slot chart are dependencies, not
certified by the numerical bridge. No recurrence, lower-jet budget, derivative
identity, cut supplier, or desired bound is a premise of the public consumers.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped Classical

namespace AcceleratedLogConcave.Tensor.LegacyOriginalDataBudgets
open Conditional ActualCoefficient
variable {D : ℕ}

/-- The two predicates quantify exactly the same cuts and the same split norm. -/
theorem allProper_iff {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (T : Coeff Slot D) (C : ℝ) :
    EdgeClosure.AllProper D T C ↔ QuantitativeKernel.AllProper D T C :=
  Iff.rfl

/-- Both names denote the original backward probability transport. -/
theorem actualY_eq_legacy (d : PositiveVarianceFlowData (Space D)) (t : ℝ) :
    Conditional.Transport.SpatialFlow.actualY d t =
      QuantitativeKernel.actualY d t := rfl

/-- Literal coefficient equality, not a quantitative transport hypothesis.
The flow convention already has derivative slots plus the output slot. -/
theorem actualJetCoeff_eq_legacy
    (d : PositiveVarianceFlowData (Space D)) (n : ℕ) (y : Space D) (t : ℝ) :
    ActualCoefficient.actualJetCoeff d n y t =
      QuantitativeKernel.vectorJetCoeff n (QuantitativeKernel.actualY d t) y := by
  ext a
  rfl

/-- The clock identity does not need smallness or a nonzero parameter. -/
theorem flowClock_eq_curvatureTime
    (d : PositiveVarianceFlowData (Space D)) (t : ℝ) :
    FlowInduction.flowClock d t =
      QuantitativeKernel.curvatureTime d.r d.ell d.b t := rfl

/-- The scale identity involves no cancellation or division by b. -/
theorem flowScale_eq_spatialScale (d : PositiveVarianceFlowData (Space D)) :
    FlowInduction.flowScale d = QuantitativeKernel.spatialScale d.b := rfl

/-- Positive flow orders only: the legacy and new zero entries differ. -/
theorem flowBudget_eq_legacy
    (d : PositiveVarianceFlowData (Space D)) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    FlowInduction.flowBudget d n t =
      if n = 1 then Real.exp (QuantitativeKernel.curvatureTime d.r d.ell d.b t)
      else QuantitativeKernel.curvatureTime d.r d.ell d.b t *
        QuantitativeKernel.spatialScale d.b^(n-1) * QuantitativeKernel.flowConstant n := by
  simp only [FlowInduction.flowBudget, flowClock_eq_curvatureTime, flowScale_eq_spatialScale,
    LegacyOrderConstantBridge.flowConstant_eq_orderConstant (by omega : 1 ≤ n)]

/-- All inverse orders: zero retains exp(A), not the uniform exp(1/4). -/
theorem inverseBudget_eq_legacy
    (d : PositiveVarianceFlowData (Space D)) (n : ℕ) (t : ℝ) :
    InverseFlow.inverseBudget d n t =
      if n = 0 then Real.exp (QuantitativeKernel.curvatureTime d.r d.ell d.b t)
      else QuantitativeKernel.curvatureTime d.r d.ell d.b t *
        QuantitativeKernel.spatialScale d.b^n * QuantitativeKernel.inverseConstant n := by
  simp only [InverseFlow.inverseBudget, flowClock_eq_curvatureTime, flowScale_eq_spatialScale,
    LegacyOrderConstantBridge.inverseConstant_eq_inverseOrderConstant n]

/-- Original-data P_n in the literal legacy coefficient and scalar conventions. -/
theorem original_data_legacy_flow_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    QuantitativeKernel.AllProper D
      (QuantitativeKernel.vectorJetCoeff n (QuantitativeKernel.actualY d t) y)
      (if n = 1 then Real.exp (QuantitativeKernel.curvatureTime d.r d.ell d.b t)
       else QuantitativeKernel.curvatureTime d.r d.ell d.b t *
         QuantitativeKernel.spatialScale d.b^(n-1) * QuantitativeKernel.flowConstant n) := by
  apply (allProper_iff _ _).mp
  rw [← actualJetCoeff_eq_legacy, ← flowBudget_eq_legacy d n hn t]
  exact FlowInduction.original_data_flow_allProper d hsmall n hn y ht

/-- Original-data Q_n, after the essential ((derivatives+input)+output)
to (derivatives+(input+output)) bijection supplied by InverseLegacySlotChart. -/
theorem original_data_legacy_inverse_allProper
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    QuantitativeKernel.AllProper D
      (QuantitativeKernel.operatorJetCoeff n (QuantitativeKernel.actualB d t) y)
      (if n = 0 then Real.exp (QuantitativeKernel.curvatureTime d.r d.ell d.b t)
       else QuantitativeKernel.curvatureTime d.r d.ell d.b t *
         QuantitativeKernel.spatialScale d.b^n * QuantitativeKernel.inverseConstant n) := by
  apply (allProper_iff _ _).mp
  rw [← inverseBudget_eq_legacy d n t]
  exact InverseFlow.original_data_inverse_legacy_slots d hsmall n y ht

/-- The genuine old flow proposition, proved rather than redefined or assumed. -/
theorem original_data_actualFlowBudgetStatement :
    QuantitativeKernel.ActualFlowBudgetStatement := by
  intro D d hsmall t ht y
  constructor
  · simpa using
      original_data_legacy_flow_allProper d hsmall 1 (by omega) y ht
  · intro n hn
    simpa only [ite_eq_right (show n ≠ 1 by omega)] using
      original_data_legacy_flow_allProper d hsmall n (by omega) y ht

/-- The genuine old inverse proposition, with its separate zero initialization. -/
theorem original_data_actualInverseBudgetStatement :
    QuantitativeKernel.ActualInverseBudgetStatement := by
  intro D d hsmall t ht y
  constructor
  · simpa using
      original_data_legacy_inverse_allProper d hsmall 0 y ht
  · intro n hn
    simpa only [ite_eq_right (show n ≠ 0 by omega)] using
      original_data_legacy_inverse_allProper d hsmall n y ht

end AcceleratedLogConcave.Tensor.LegacyOriginalDataBudgets
