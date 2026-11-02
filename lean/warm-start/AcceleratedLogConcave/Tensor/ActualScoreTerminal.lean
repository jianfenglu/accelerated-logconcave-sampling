import AcceleratedLogConcave.Tensor.ActualCoefficientTerminal

noncomputable section
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional AdjointReduction

/-- The leading score derivative and divergence direction become the
two literal Hessian slots. All remaining derivative slots keep their order. -/
def scoreTerminalSlotEquiv (j : ℕ) : (Fin (j+1) ⊕ Unit) ≃ (Fin j ⊕ Fin 2) where
  toFun
    | Sum.inl i => Fin.cases (Sum.inr 0) (fun k => Sum.inl k) i
    | Sum.inr _ => Sum.inr 1
  invFun
    | Sum.inl i => Sum.inl i.succ
    | Sum.inr k => Fin.cases (Sum.inl 0) (fun _ => Sum.inr ()) k
  left_inv := by
    intro a
    cases a with
    | inl i => refine Fin.cases ?_ (fun k => ?_) i <;> rfl
    | inr u => cases u; rfl
  right_inv := by
    intro a
    cases a with
    | inl i => rfl
    | inr i => fin_cases i <;> rfl

/-- Specialize the canonical nonempty-score/Hessian identity to the
actual coefficient environment, without introducing a formal Hessian hypothesis. -/
theorem nonempty_score_coefficient {D L : Type*} [Fintype D] [DecidableEq D]
    (v : L → EuclideanSpace ℝ D) (i : L) (J : List L)
    {H : EuclideanSpace ℝ D → ℝ} (hH : ContDiff ℝ ∞ H)
    (w : EuclideanSpace ℝ D) :
    partialAlong v (i::J) (dir w H) =
      partialAlong v J (dir (v i) (dir w H)) := by
  rw [nonempty_score_is_hessian v i J hH w,dir_dir_eq_hessian hH]

/-- Exact terminal tensor with |score derivatives|-1 spatial derivatives
of S. The two Hessian slots are leading derivative first, divergence second. -/
theorem actualScore_terminal {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (j : ℕ) {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D))
    (a : (Fin (j+1) ⊕ Unit) → Fin D) :
    partialAlong (fun i : Fin (j+1) => coordinateDirection D (a (Sum.inl i)))
      (List.finRange (j+1))
      (dir (coordinateDirection D (a (Sum.inr ())))
        (interpolationPotential d.F d.x d.r t)) y =
    actualCoefficientDerivative d.F d.x d.ell d.r t (Sum.inr ()) j y
      (a ∘ (scoreTerminalSlotEquiv j).symm ∘ coefficientTerminalSlotEquiv (Sum.inr ()) j) := by
  rw [List.finRange_succ]
  rw [nonempty_score_coefficient _ _ _
    (contDiff_interpolationPotential d.hF d.hlo d.hhi d.x d.r ht.1 ht.2)]
  symm
  refine (actualCoefficientDerivative_terminal d.F d.x d.ell d.r t (Sum.inr ()) j y
    (show (Fin j ⊕ Fin (signature.arity (Sum.inr ()))) → Fin D from
      a ∘ (scoreTerminalSlotEquiv j).symm)).trans ?_
  simp only [partialAlong_eq_jet,JetCalculus.jet_map]
  rfl

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
