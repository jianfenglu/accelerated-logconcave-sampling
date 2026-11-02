import AcceleratedLogConcave.Tensor.DistinguishedOutputLift

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.ActualCoefficient
open OutputLift
variable {D : ℕ}

/-- Evaluation on a singleton slot group; valid also when Fin D is empty. -/
def oneAssignmentEquiv {A : Type*} (p : A) (h : ∀ a : A, a = p) :
    (A → Fin D) ≃ Fin D where
  toFun a := a p
  invFun i := fun _ => i
  left_inv a := by funext j; rw [h j]
  right_inv _ := rfl

/-- A literal two-slot unfolding is a reindexed matrix, not an HS estimate. -/
theorem twoSlot_splitNorm {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A) (hpq : p ≠ q) (hall : ∀ a : A, a = p ∨ a = q)
    (M : Matrix (Fin D) (Fin D) ℝ) :
    splitNorm D {p} (WithLp.toLp 2 (fun a : A → Fin D => M (a p) (a q))) =
      ‖matrixCLMEquiv M‖ := by
  let e : LeftAssignment D ({p} : Finset A) ≃ Fin D :=
    oneAssignmentEquiv ⟨p,by simp⟩ (fun a => Subtype.ext (Finset.mem_singleton.mp a.property))
  let f : RightAssignment D ({p} : Finset A) ≃ Fin D :=
    oneAssignmentEquiv ⟨q,by simpa using hpq.symm⟩ (fun a => Subtype.ext (by
      rcases hall a with h | h
      · exact False.elim (a.property (by simp [h]))
      · exact h))
  change ‖matrixCLMEquiv (unfoldEquiv D {p} _)‖ = _
  have he : unfoldEquiv D {p}
      (WithLp.toLp 2 (fun a : A → Fin D => M (a p) (a q))) =
      fun a b => M (e a) (f b) := by
    ext a b
    simp [unfold_apply,e,f,oneAssignmentEquiv,hpq.symm]
  rw [he]
  exact matrixCLM_reindex_norm M e f

def rankTwoCoeff (L : Space D →L[ℝ] Space D) : Coeff (Fin 1 ⊕ Unit) D :=
  WithLp.toLp 2 (fun a => inner ℝ (basis D (a (.inr ()))) (L (basis D (a (.inl 0)))))

theorem rankTwo_splitNorm_le (L : Space D →L[ℝ] Space D)
    (S : Finset (Fin 1 ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (rankTwoCoeff L) ≤ ‖L‖ := by
  have hcases : S = {Sum.inr ()} ∨ S = {Sum.inl 0} := by
    by_cases ho : Sum.inr () ∈ S
    · left
      have hi : Sum.inl (0 : Fin 1) ∉ S := by
        intro hi
        obtain ⟨a,ha⟩ := hS.2
        fin_cases a <;> simp_all
      ext a
      fin_cases a <;> simp_all
    · right
      have hi : Sum.inl (0 : Fin 1) ∈ S := by
        obtain ⟨a,ha⟩ := hS.1
        fin_cases a <;> simp_all
      ext a
      fin_cases a <;> simp_all
  rcases hcases with rfl | rfl
  · have he := twoSlot_splitNorm (D := D) (Sum.inr () : Fin 1 ⊕ Unit)
      (Sum.inl 0) (by simp) (by intro a; fin_cases a <;> simp)
      (derivativeMatrix L)
    change splitNorm D {Sum.inr ()} (rankTwoCoeff L) =
      ‖matrixCLMEquiv (derivativeMatrix L)‖ at he
    rw [he,derivativeMatrix_operator]
  · have he := twoSlot_splitNorm (D := D) (Sum.inl 0 : Fin 1 ⊕ Unit)
      (Sum.inr ()) (by simp) (by intro a; fin_cases a <;> simp)
      (derivativeMatrix L).transpose
    change splitNorm D {Sum.inl 0} (rankTwoCoeff L) =
      ‖matrixCLMEquiv (derivativeMatrix L).transpose‖ at he
    rw [he]
    exact (transpose_norm_le _).trans_eq (congrArg norm (derivativeMatrix_operator L))

theorem vectorCoeff_one_eq_rankTwo (f : Space D → Space D) (y : Space D) :
    vectorCoeff (iteratedFDeriv ℝ 1 f y) = rankTwoCoeff (fderiv ℝ f y) := by
  ext a
  simp [vectorCoeff,mapCoeff,rankTwoCoeff,iteratedFDeriv_one_apply]

end AcceleratedLogConcave.Tensor.ActualCoefficient
