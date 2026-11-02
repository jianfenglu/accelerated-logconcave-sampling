import AcceleratedLogConcave.Tensor.ActualCoefficientBudgets

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional AdjointReduction

theorem partialAlong_eq_jet {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : L → E) (l : List L) (f : E → ℝ) :
    partialAlong v l f = JetCalculus.jet v l f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change AdjointReduction.dir (v i) (partialAlong v l f) = JetCalculus.dir (v i) (JetCalculus.jet v l f)
    rw [ih]
    rfl

/-- Move the distinguished output slot to the first coefficient slot,
leaving every derivative slot in its original order. -/
def terminalSlotEquiv (q j : ℕ) : ((Fin j ⊕ Fin q) ⊕ Unit) ≃ (Fin j ⊕ Fin (q+1)) where
  toFun
    | Sum.inl (Sum.inl i) => Sum.inl i
    | Sum.inl (Sum.inr k) => Sum.inr k.succ
    | Sum.inr _ => Sum.inr 0
  invFun
    | Sum.inl i => Sum.inl (Sum.inl i)
    | Sum.inr k => Fin.cases (Sum.inr ()) (fun i => Sum.inl (Sum.inr i)) k
  left_inv := by intro a; rcases a with (i | k) | ⟨⟩ <;> rfl
  right_inv := by
    intro a
    cases a with
    | inl i => rfl
    | inr k => refine Fin.cases ?_ (fun i => ?_) k <;> rfl

def coefficientTerminalSlotEquiv (c : Name) (j : ℕ) :
    coefficientDerivativeSlots c j ≃ (Fin j ⊕ Fin (signature.arity c)) :=
  match c with
  | Sum.inl n => terminalSlotEquiv (n+1) j
  | Sum.inr _ => terminalSlotEquiv 1 j

/-- The compiled coefficient tensor is exactly the decorated terminal
section used by the reduction calculus, after the fixed output-slot move. -/
theorem actualCoefficientDerivative_terminal {D : ℕ}
    (F : EuclideanSpace ℝ (Fin D) → ℝ) (x : EuclideanSpace ℝ (Fin D))
    (ell r t : ℝ) (c : Name) (j : ℕ) (y : EuclideanSpace ℝ (Fin D))
    (a : (Fin j ⊕ Fin (signature.arity c)) → Fin D) :
    actualCoefficientDerivative F x ell r t c j y
      (a ∘ coefficientTerminalSlotEquiv c j) =
    partialAlong (fun i : Fin j => coordinateDirection D (a (Sum.inl i)))
      (List.finRange j)
      (fun z => coefficientEnvironment F x ell r t c z (fun k => a (Sum.inr k))) y := by
  rw [partialAlong_eq_jet]
  cases c with
  | inl n =>
    change JetCalculus.jet _ _ _ y = _
    congr 2
  | inr u =>
    change JetCalculus.jet _ _ _ y = _
    congr 2

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
