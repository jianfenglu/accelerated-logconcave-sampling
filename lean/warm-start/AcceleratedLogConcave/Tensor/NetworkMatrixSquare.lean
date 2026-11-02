import AcceleratedLogConcave.Tensor.NetworkReplacement

/-! The literal two-copy rank-two Hilbert--Schmidt square is an admissible network. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph

 def matrixSquareGraph : Graph 1 Unit where
  source := fun _ => 0
  target := fun _ => 1
  forward := fun _ => by decide

 theorem matrixSquareGraph_admissible : matrixSquareGraph.Admissible := by
  intro v
  fin_cases v
  · exact ⟨⟨⟨none,rfl⟩⟩,⟨⟨some (),rfl⟩⟩⟩
  · exact ⟨⟨⟨some (),rfl⟩⟩,⟨⟨none,rfl⟩⟩⟩

private def matrixWireEquiv : Option Unit ≃ Fin 2 where
  toFun | none => 0 | some _ => 1
  invFun := Fin.cases none (fun _ => some ())
  left_inv w := by cases w with | none => rfl | some u => cases u; rfl
  right_inv v := by fin_cases v <;> rfl

private def matrixSlotOfWire (v : Fin 2) : Option Unit → matrixSquareGraph.Slot v := by
  by_cases h : v = 0
  · subst v
    exact fun w => match w with | none => .inl ⟨none,rfl⟩ | some _ => .inr ⟨some (),rfl⟩
  · have hv : v = 1 := by omega
    subst v
    exact fun w => match w with | none => .inr ⟨none,rfl⟩ | some _ => .inl ⟨some (),rfl⟩

 def matrixSlotEquiv (v : Fin 2) : matrixSquareGraph.Slot v ≃ Fin 2 :=
  (show matrixSquareGraph.Slot v ≃ Option Unit from {
    toFun := Sum.elim Subtype.val Subtype.val
    invFun := matrixSlotOfWire v
    left_inv := by
      intro a
      fin_cases v <;> cases a with
      | inl a =>
        rcases a with ⟨w,h⟩
        cases w with
        | none => simp_all [matrixSlotOfWire, incoming, matrixSquareGraph, Sum.elim] <;> norm_num [incoming, outgoing, matrixSquareGraph, Fin.ext_iff] at h
        | some u => cases u; simp_all [matrixSlotOfWire, incoming, matrixSquareGraph, Sum.elim] <;> norm_num [incoming, outgoing, matrixSquareGraph, Fin.ext_iff] at h
      | inr a =>
        rcases a with ⟨w,h⟩
        cases w with
        | none => simp_all [matrixSlotOfWire, outgoing, matrixSquareGraph, Sum.elim] <;> norm_num [incoming, outgoing, matrixSquareGraph, Fin.ext_iff] at h
        | some u => cases u; simp_all [matrixSlotOfWire, outgoing, matrixSquareGraph, Sum.elim] <;> norm_num [incoming, outgoing, matrixSquareGraph, Fin.ext_iff] at h
    right_inv := by intro w; fin_cases v <;> cases w with
      | none => rfl
      | some u => cases u; rfl }).trans matrixWireEquiv

variable {D : ℕ}
 def matrixSquareFamily (A : FinCoeff 2 D) : matrixSquareGraph.Tensors D :=
  fun v => WithLp.toLp 2 (fun a => A (fun i => a (matrixSlotOfWire v (matrixWireEquiv.symm i))))

 theorem matrixSquareFamily_value (A : FinCoeff 2 D) (c : Option Unit → Fin D) (v : Fin 2) :
    matrixSquareGraph.wireValue (matrixSquareFamily A) c v = A (c ∘ matrixWireEquiv.symm) := by
  unfold wireValue matrixSquareFamily
  apply congrArg (fun a => A a)
  funext i
  fin_cases v <;> fin_cases i <;> rfl

 theorem coordinateEval_matrixSquareFamily (A : FinCoeff 2 D) :
    matrixSquareGraph.coordinateEval D (matrixSquareFamily A) = ‖A‖^2 := by
  have hv : matrixSquareGraph.coordinateEval D (matrixSquareFamily A) =
      ∑ c : Option Unit → Fin D, (A (c ∘ matrixWireEquiv.symm))^2 := by
    unfold coordinateEval
    apply Finset.sum_congr
    · ext c; simp
    intro c _
    change (∏ v : Fin 2, matrixSquareGraph.wireValue (matrixSquareFamily A) c v) = _
    simp only [matrixSquareFamily_value, Fin.prod_univ_two, pow_two]
  calc
    matrixSquareGraph.coordinateEval D (matrixSquareFamily A) =
        ∑ c : Option Unit → Fin D, (A (c ∘ matrixWireEquiv.symm))^2 := hv
    _ = ∑ a : Fin 2 → Fin D, (A a)^2 := by
      apply Fintype.sum_equiv (Equiv.arrowCongr matrixWireEquiv (Equiv.refl (Fin D)))
      intro c
      rfl
    _ = ‖A‖^2 := by
      symm
      convert PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 → Fin D => ℝ) A using 1
      apply Finset.sum_congr rfl
      intro a _
      exact (sq_abs (A a)).symm
end AcceleratedLogConcave.Tensor.Ordered.Graph
