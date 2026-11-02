import AcceleratedLogConcave.Tensor.HessianDerivativeCoefficient

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional

/-- A fixed ordinary Hilbert slot order for actual coefficient derivatives. -/
def coefficientDerivativeSlots (c : Name) (j : ℕ) : Type :=
  match c with
  | Sum.inl n => (Fin j ⊕ Fin (n+1)) ⊕ Unit
  | Sum.inr _ => (Fin j ⊕ Fin 1) ⊕ Unit

instance (c : Name) (j : ℕ) : Fintype (coefficientDerivativeSlots c j) := by
  cases c <;> dsimp [coefficientDerivativeSlots] <;> infer_instance
instance (c : Name) (j : ℕ) : DecidableEq (coefficientDerivativeSlots c j) := by
  cases c <;> dsimp [coefficientDerivativeSlots] <;> infer_instance

/-- Both branches are literal ordered derivatives of the existing environment,
not independently chosen coefficient fields. -/
def actualCoefficientDerivative {D : ℕ} (F : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) (ell r t : ℝ) (c : Name) (j : ℕ)
    (y : EuclideanSpace ℝ (Fin D)) : Coeff (coefficientDerivativeSlots c j) D :=
  match c with
  | Sum.inl n => normalizedJetDerivativeCoefficient F x ell r t n j y
  | Sum.inr _ => hessianDerivativeCoefficient F x ell r t j y

/-- The complete source coefficient premise, with c0=2 and R=sqrt(1-rho²),
for every named original-data coefficient and every spatial derivative order. -/
theorem actualCoefficientDerivative_split_budget {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (hsmall : d.r^2*d.ell ≤ 1/2) (c : Name) (j : ℕ)
    {t : ℝ} (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D))
    (S : Finset (coefficientDerivativeSlots c j)) (hS : NontrivialSplit S) :
    splitNorm D S (actualCoefficientDerivative d.F d.x d.ell d.r t c j y) ≤
      (2:ℝ)^(signature.size c+j) * ((signature.size c+j).factorial : ℝ) *
        (Real.sqrt (conditionalVariance t)) ^ (-(signature.weight c : ℝ) - (j : ℝ)) := by
  cases c with
  | inl n =>
    have hh := normalizedJetDerivativeCoefficient_budget d n j ht y S hS
    convert hh using 1 <;> simp [actualCoefficientDerivative,sub_eq_add_neg,←neg_add,
      ←Nat.cast_add,Real.rpow_neg,Real.rpow_natCast]
  | inr u =>
    have hh := hessianDerivativeCoefficient_budget d hsmall j ht y S hS
    convert hh using 1 <;> simp [actualCoefficientDerivative,Real.rpow_neg,Real.rpow_natCast]

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
