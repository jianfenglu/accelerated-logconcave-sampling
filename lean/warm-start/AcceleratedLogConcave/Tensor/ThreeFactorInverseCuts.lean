import AcceleratedLogConcave.Tensor.OriginalDataInverseBase

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.InverseFlow
open ActualCoefficient EdgeClosure
variable {D : ℕ} {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

/-- Repackage the actual L M coefficient as an operator tensor before multiplying R. -/
def productOperatorChart : ((A ⊕ Unit) ⊕ (B ⊕ Unit)) ≃ (((A ⊕ B) ⊕ Unit) ⊕ Unit) where
  toFun
    | .inl (.inl a) => .inl (.inl (.inl a))
    | .inl (.inr u) => .inr u
    | .inr (.inl b) => .inl (.inl (.inr b))
    | .inr (.inr u) => .inl (.inr u)
  invFun
    | .inl (.inl (.inl a)) => .inl (.inl a)
    | .inl (.inl (.inr b)) => .inr (.inl b)
    | .inl (.inr u) => .inr (.inr u)
    | .inr u => .inl (.inr u)
  left_inv := by intro s; rcases s with (a | u) | (b | u) <;> rfl
  right_inv := by intro s; rcases s with ((a | b) | u) | u <;> rfl

/-- Delete only the impossible Fin 0 derivative of the undifferentiated R;
its ordinary input survives, and the final output remains that of L. -/
def pathExternalChart : (((A ⊕ B) ⊕ Unit) ⊕ (Fin 0 ⊕ Unit)) ≃
    ((A ⊕ B) ⊕ (Unit ⊕ Unit)) where
  toFun
    | .inl (.inl a) => .inl a
    | .inl (.inr u) => .inr (.inr u)
    | .inr (.inl j) => Fin.elim0 j
    | .inr (.inr u) => .inr (.inl u)
  invFun
    | .inl a => .inl (.inl a)
    | .inr (.inl u) => .inr (.inr u)
    | .inr (.inr u) => .inl (.inr u)
  left_inv := by
    intro s
    rcases s with (a | u) | (j | u)
    · rfl
    · rfl
    · exact Fin.elim0 j
    · rfl
  right_inv := by intro s; rcases s with a | (u | u) <;> rfl

def threeFactorCoeff
    (L : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D →L[ℝ] Space D))
    (M : ContinuousMultilinearMap ℝ (fun _ : B => Space D) (Space D →L[ℝ] Space D))
    (R : Space D →L[ℝ] Space D) : Coeff ((A ⊕ B) ⊕ (Unit ⊕ Unit)) D :=
  WithLp.toLp 2 (fun a => inner ℝ (basis D (a (.inr (.inr ()))))
    (((L (fun j => basis D (a (.inl (.inl j))))).comp
      ((M (fun j => basis D (a (.inl (.inr j))))).comp R))
      (basis D (a (.inr (.inl ()))))))

omit [DecidableEq A] [DecidableEq B] in
/-- Exact equality of every retained coefficient; operator order is L M R. -/
theorem threeFactorCoeff_eq_two_edges
    (L : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D →L[ℝ] Space D))
    (M : ContinuousMultilinearMap ℝ (fun _ : B => Space D) (Space D →L[ℝ] Space D))
    (R : Space D →L[ℝ] Space D) :
    relabel D pathExternalChart
      (operatorCompose D (relabel D productOperatorChart (composeCoeff L M))
        (relabel D zeroOperatorChart (rankTwoCoeff R))) = threeFactorCoeff L M R := by
  ext a
  change (∑ w : Fin D,
    inner ℝ (basis D (a (.inr (.inr ()))))
      (((L (fun j => basis D (a (.inl (.inl j))))).comp
        (M (fun j => basis D (a (.inl (.inr j)))))) (basis D w)) *
    inner ℝ (basis D w) (R (basis D (a (.inr (.inl ())))))) = _
  exact (inner_comp_basis
    ((L (fun j => basis D (a (.inl (.inl j))))).comp
      (M (fun j => basis D (a (.inl (.inr j)))))) R
    (a (.inr (.inl ()))) (a (.inr (.inr ())))).symm

/-- Both choices at each contracted edge are handled by single-edge all-proper.
Empty derivative groups and physical D=0 are permitted. -/
theorem threeFactorCoeff_allProper
    (L : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D →L[ℝ] Space D))
    (M : ContinuousMultilinearMap ℝ (fun _ : B => Space D) (Space D →L[ℝ] Space D))
    (R : Space D →L[ℝ] Space D)
    {CL CM CR : ℝ} (hCL : 0 ≤ CL) (hCM : 0 ≤ CM) (hCR : 0 ≤ CR)
    (hL : AllProper D (operatorCoeff L) CL)
    (hM : AllProper D (operatorCoeff M) CM)
    (hR : AllProper D (rankTwoCoeff R) CR) :
    AllProper D (threeFactorCoeff L M R) ((CL*CM)*CR) := by
  have hLM := (composeCoeff_allProper L M hCL hCM hL hM).relabel productOperatorChart
  have h := (operatorCompose_allProper D _ _ (mul_nonneg hCL hCM) hCR
    hLM (hR.relabel zeroOperatorChart)).relabel pathExternalChart
  rwa [threeFactorCoeff_eq_two_edges] at h
end AcceleratedLogConcave.Tensor.InverseFlow
