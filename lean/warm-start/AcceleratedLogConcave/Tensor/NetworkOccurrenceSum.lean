import AcceleratedLogConcave.Tensor.NetworkSyntaxState
import AcceleratedLogConcave.Tensor.NetworkSplitForest

noncomputable section
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

/-- The retained occurrence equivalence preserves the literal forest sum. -/
theorem SyntaxState.sum_occurrences {s : List (TaggedPending σ)} (S : SyntaxState s)
    (f : TaggedPending σ → ℝ) :
    (∑ v : Fin (S.n+1), f (S.pending v)) = (s.map f).sum := by
  calc
    _ = ∑ i : Fin s.length, f (s.get i) := by
      symm
      apply Fintype.sum_equiv S.occurrence
      intro i
      rw [S.occurrence_spec]
    _ = _ := by
      rw [← List.sum_ofFn]
      congr 1
      ext i
      simp

/-- Removing the physical parent vertex is exactly removing its one syntax
occurrence. Repeated values or erased labels are not collapsed. -/
theorem SyntaxState.sum_other_occurrences
    (before after : List (TaggedPending σ)) (p : TaggedPending σ)
    (S : SyntaxState (before ++ [p] ++ after)) (f : TaggedPending σ → ℝ) :
    (∑ v : {v : Fin (S.n+1) // v ≠ S.occurrence (forestParentIndex before after p)},
      f (S.pending v.val)) = (before.map f).sum + (after.map f).sum := by
  let parent := S.occurrence (forestParentIndex before after p)
  have hp : S.pending parent = p := by
    rw [S.occurrence_spec]
    simp [forestParentIndex]
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin (S.n+1)))
    (fun v => f (S.pending v)) (Finset.mem_univ parent)
  rw [Finset.sum_subtype (p := fun v => v ≠ parent) _ (by intro v; simp) (fun v => f (S.pending v))] at he
  rw [S.sum_occurrences f,hp] at he
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
    List.sum_nil,add_zero] at he
  linarith

end AcceleratedLogConcave.Tensor.Ordered.Graph
