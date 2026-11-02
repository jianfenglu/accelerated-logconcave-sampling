import AcceleratedLogConcave.Tensor.OriginalDataInverseBounds
import AcceleratedLogConcave.Tensor.QuantitativeBudgetTargets

/-!

-/
noncomputable section
set_option autoImplicit false
open Set
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.InverseFlow
open Conditional ActualCoefficient EdgeClosure FlowInduction
variable {D : ℕ}

/-- The older coefficient uses derivatives+(input+output), not (derivatives+input)+output. -/
def inverseLegacyChart (n : ℕ) : ((Fin n ⊕ Unit) ⊕ Unit) ≃ (Fin n ⊕ (Unit ⊕ Unit)) where
  toFun
    | .inl (.inl j) => .inl j
    | .inl (.inr u) => .inr (.inl u)
    | .inr u => .inr (.inr u)
  invFun
    | .inl j => .inl (.inl j)
    | .inr (.inl u) => .inl (.inr u)
    | .inr (.inr u) => .inr u
  left_inv := by intro a; rcases a with (j | u) | u <;> rfl
  right_inv := by intro a; rcases a with j | (u | u) <;> rfl

 theorem inverseJetCoeff_legacy_chart
    (d : PositiveVarianceFlowData (Space D)) (n : ℕ) (t : ℝ) (y : Space D) :
    relabel D (inverseLegacyChart n) (inverseJetCoeff d n t y) =
      QuantitativeKernel.operatorJetCoeff n (QuantitativeKernel.actualB d t) y := by
  ext a
  rfl

/-- Old slot notation, NEW inverseBudget constants. This is deliberately not a
proof of the older ActualInverseBudgetStatement, whose constant bridge is unpaid. -/
theorem original_data_inverse_legacy_slots
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : Space D) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    EdgeClosure.AllProper D
      (QuantitativeKernel.operatorJetCoeff n (QuantitativeKernel.actualB d t) y)
      (inverseBudget d n t) := by
  rw [← inverseJetCoeff_legacy_chart]
  exact (original_data_inverse_allProper d hsmall n y ht).relabel (inverseLegacyChart n)

end AcceleratedLogConcave.Tensor.InverseFlow
