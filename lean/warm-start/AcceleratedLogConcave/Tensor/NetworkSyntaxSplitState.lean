import AcceleratedLogConcave.Tensor.NetworkSplitForest
import AcceleratedLogConcave.Tensor.NetworkReplacementOrigins

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

theorem splitVertex_other_succAbove {n : ℕ} (p v : Fin (n+1)) (hv : v ≠ p) :
    splitVertex p v false = p.succ.succAbove v := by
  rcases lt_or_gt_of_ne hv with h | h
  · rw [Fin.succAbove_succ_of_le _ _ h.le]
    apply Fin.ext
    simp [splitVertex, h]
  · rw [Fin.succAbove_succ_of_lt _ _ h]
    apply Fin.ext
    simp [splitVertex, h, not_lt.mpr h.le]

namespace SyntaxState
variable (before after : List (TaggedPending σ)) (parent left right : TaggedPending σ)
    (S : SyntaxState (before ++ [parent] ++ after))

/-- Assemble all retained syntax-state fields for a literal occurrence split.
The child hypotheses are syntax/origin data only, not value or norm certificates. -/
def splitOccurrence
    (part : S.graph.Slot (S.occurrence (forestParentIndex before after parent)) → Bool)
    (b : Bool)
    (hnew : (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).Admissible)
    (A : (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).SyntaxAt
      (σ := σ) (S.occurrence (forestParentIndex before after parent)).castSucc)
    (B : (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).SyntaxAt
      (σ := σ) (S.occurrence (forestParentIndex before after parent)).succ)
    (hA : A.1 = if b then right else left) (hB : B.1 = if b then left else right)
    (hAo : ∀ u o, pendingPortOrigin A.1 u = some o →
      Sum.elim Subtype.val Subtype.val (A.2.symm u) = oldWire (S.originWire o))
    (hBo : ∀ u o, pendingPortOrigin B.1 u = some o →
      Sum.elim Subtype.val Subtype.val (B.2.symm u) = oldWire (S.originWire o)) :
    SyntaxState (before ++ [left,right] ++ after) := by
  letI := S.edgeFintype
  let p := S.occurrence (forestParentIndex before after parent)
  let P : ∀ v, S.graph.SyntaxAt (σ := σ) v := fun v => ⟨S.pending v, S.ports v⟩
  let Q := S.graph.replacementSyntax p part P A B
  refine {
    n := S.n+1
    Edge := Option S.Edge
    edgeFintype := inferInstance
    graph := S.graph.replaceVertex p part
    admissible := hnew
    pending := fun w => (Q w).1
    occurrence := (finCongr (forestSplit_length before after parent left right)).trans
      (splitOccurrenceEquiv S.occurrence (forestParentIndex before after parent) b)
    occurrence_spec := ?_
    ports := fun w => (Q w).2
    originWire := fun o => oldWire (S.originWire o)
    origin_spec := ?_ }
  · apply forestSplit_occurrence before after parent left right S.occurrence b S.pending
      (fun w => (Q w).1) S.occurrence_spec
    · cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hA hB ⊢
      · exact (congrArg Sigma.fst (S.graph.replacementSyntax_left p part P A B)).trans hA
      · exact (congrArg Sigma.fst (S.graph.replacementSyntax_right p part P A B)).trans hB
    · cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hA hB ⊢
      · exact (congrArg Sigma.fst (S.graph.replacementSyntax_right p part P A B)).trans hB
      · exact (congrArg Sigma.fst (S.graph.replacementSyntax_left p part P A B)).trans hA
    · intro v hv
      have hne : S.occurrence v ≠ p := fun h => hv (S.occurrence.injective h)
      rw [← splitVertex_other_succAbove p (S.occurrence v) hne]
      exact congrArg Sigma.fst (S.graph.replacementSyntax_other p part P A B _ hne)
  · exact S.graph.replacementSyntax_origin p part P A B S.originWire S.origin_spec hAo hBo

end SyntaxState
end AcceleratedLogConcave.Tensor.Ordered.Graph
