import AcceleratedLogConcave.Tensor.OriginalDataInverseBase

/-!

-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff Classical BigOperators
namespace AcceleratedLogConcave.Tensor.InverseFlow
open Conditional Conditional.Transport.SpatialFlow
open ActualCoefficient EdgeClosure FlowInduction
variable {D : ℕ}

/-- The last Y derivative input is J's ordinary input; the output is unchanged. -/
def jacobianSlotChart (k : ℕ) : (Fin (k+1) ⊕ Unit) ≃ ((Fin k ⊕ Unit) ⊕ Unit) where
  toFun := fun a => match a with
    | .inl j => Fin.lastCases (.inl (.inr ())) (fun i => .inl (.inl i)) j
    | .inr _ => .inr ()
  invFun := fun a => match a with
    | .inl (.inl j) => .inl j.castSucc
    | .inl (.inr _) => .inl (Fin.last k)
    | .inr _ => .inr ()
  left_inv := by
    intro a
    rcases a with j | u
    · refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
    · cases u; rfl
  right_inv := by
    intro a
    rcases a with (j | u) | u
    · simp
    · cases u; simp
    · cases u; rfl

/-- All k spatial derivative labels and the ordinary input/output survive. -/
theorem jacobianJetCoeff_eq_flow_relabel (d : PositiveVarianceFlowData (Space D))
    (k : ℕ) (t : ℝ) (y : Space D) :
    operatorCoeff (iteratedFDeriv ℝ k (actualJ d t) y) =
      relabel D (jacobianSlotChart k) (actualJetCoeff d (k+1) y t) := by
  ext a
  change inner ℝ (basis D (a (.inr ())))
      ((iteratedFDeriv ℝ k (fderiv ℝ (actualY d t)) y
        (fun j => basis D (a (.inl (.inl j))))) (basis D (a (.inl (.inr ()))))) =
    inner ℝ (basis D (a (jacobianSlotChart k (.inr ()))))
      (iteratedFDeriv ℝ (k+1) (actualY d t) y
        (fun j => basis D (a (jacobianSlotChart k (.inl j)))))
  have hm : Fin.init (fun j => basis D (a (jacobianSlotChart k (.inl j)))) =
      fun j => basis D (a (.inl (.inl j))) := by
    funext j
    change basis D (a (jacobianSlotChart k (.inl j.castSucc))) = _
    simp [jacobianSlotChart]
  rw [iteratedFDeriv_succ_apply_right, hm]
  simp [jacobianSlotChart]

/-- All-proper J jets are now paid by the existing P_(k+1) theorem. -/
theorem original_data_J_jet_allProper (d : PositiveVarianceFlowData (Space D))
    (hsmall : d.r^2*d.ell ≤ 1/2) (k : ℕ) (y : Space D)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (operatorCoeff (iteratedFDeriv ℝ k (actualJ d t) y))
      (flowBudget d (k+1) t) := by
  rw [jacobianJetCoeff_eq_flow_relabel]
  exact (original_data_flow_allProper d hsmall (k+1) (by omega) y ht).relabel
    (jacobianSlotChart k)

 theorem original_data_J_jet_relabel {A : Type*} [Fintype A] [DecidableEq A]
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (k : ℕ) (e : ((Fin k ⊕ Unit) ⊕ Unit) ≃ A) (y : Space D)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    AllProper D (relabel D e (operatorCoeff (iteratedFDeriv ℝ k (actualJ d t) y)))
      (flowBudget d (k+1) t) :=
  (original_data_J_jet_allProper d hsmall k y ht).relabel e
end AcceleratedLogConcave.Tensor.InverseFlow
