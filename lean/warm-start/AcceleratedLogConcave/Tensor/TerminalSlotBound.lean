import AcceleratedLogConcave.Tensor.SplitNormRestriction

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor

/-- A fixed slot bijection transports actual rectangular split bounds. -/
theorem splitNorm_slotEquiv_le {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (D : ℕ) (e : A ≃ B) (S : Finset A)
    (T : Coeff B D) :
    splitNorm D S (WithLp.toLp 2 (fun a => T (a ∘ e.symm))) ≤
      splitNorm D (S.map e.toEmbedding) T := by
  let l : S ≃ (S.map e.toEmbedding) :=
    Equiv.subtypeEquiv e (by intro a; simp)
  let r : {a : A // a ∉ S} ≃ {b : B // b ∉ S.map e.toEmbedding} :=
    Equiv.subtypeEquiv e (by intro a; simp)
  let er : LeftAssignment D S → LeftAssignment D (S.map e.toEmbedding) :=
    fun a => a ∘ l.symm
  let ec : RightAssignment D S → RightAssignment D (S.map e.toEmbedding) :=
    fun a => a ∘ r.symm
  have her : Function.Injective er := by
    intro a b h
    funext s
    simpa [er] using congrFun h (l s)
  have hec : Function.Injective ec := by
    intro a b h
    funext s
    simpa [ec] using congrFun h (r s)
  have hm : unfoldEquiv D S (WithLp.toLp 2 (fun a => T (a ∘ e.symm))) =
      (unfoldEquiv D (S.map e.toEmbedding) T).submatrix er ec := by
    ext a b
    change T (fun i => if h : e.symm i ∈ S then a ⟨e.symm i,h⟩ else b ⟨e.symm i,h⟩) =
      T (fun i => if h : i ∈ S.map e.toEmbedding then er a ⟨i,h⟩ else ec b ⟨i,h⟩)
    apply congrArg (fun a => T a)
    funext i
    by_cases hi : e.symm i ∈ S
    · have hi' : i ∈ S.map e.toEmbedding := by simpa using hi
      simp only [hi,hi',dite_true]
      rfl
    · have hi' : i ∉ S.map e.toEmbedding := by simpa using hi
      simp only [hi,hi',dite_false]
      rfl
  change ‖matrixCLMEquiv (unfoldEquiv D S _)‖ ≤ ‖matrixCLMEquiv (unfoldEquiv D _ T)‖
  rw [hm]
  exact matrixCLM_submatrix_norm_le _ er her ec hec

 theorem nontrivialSplit_map_equiv {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) {S : Finset A}
    (hS : NontrivialSplit S) : NontrivialSplit (S.map e.toEmbedding) := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := hS
  refine ⟨⟨e a,by simpa using ha⟩,⟨e b,?_⟩⟩
  simpa using hb

end AcceleratedLogConcave.Tensor
