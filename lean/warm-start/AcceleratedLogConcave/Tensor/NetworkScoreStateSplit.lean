import AcceleratedLogConcave.Tensor.NetworkSyntaxSplitState
import AcceleratedLogConcave.Tensor.NetworkSyntaxFamilyValue

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool)

/-- Origin transport for the assembled family, retaining both child proofs. -/
theorem replacementSyntax_origin_newWire
    (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.replaceVertex p part).SyntaxAt (σ := σ) p.castSucc)
    (B : (g.replaceVertex p part).SyntaxAt (σ := σ) p.succ)
    (wire : LabelOrigin → Option (Option Edge))
    (hP : ∀ v u o, pendingPortOrigin (P v).1 u = some o →
      oldWire (Sum.elim Subtype.val Subtype.val ((P v).2.symm u)) = wire o)
    (hA : ∀ u o, pendingPortOrigin A.1 u = some o →
      Sum.elim Subtype.val Subtype.val (A.2.symm u) = wire o)
    (hB : ∀ u o, pendingPortOrigin B.1 u = some o →
      Sum.elim Subtype.val Subtype.val (B.2.symm u) = wire o) :
    ∀ w u o, pendingPortOrigin (g.replacementSyntax p part P A B w).1 u = some o →
      Sum.elim Subtype.val Subtype.val
        ((g.replacementSyntax p part P A B w).2.symm u) = wire o := by
  intro w
  by_cases h₀ : w = p.castSucc
  · subst w
    rw [replacementSyntax_left]
    exact hA
  by_cases h₁ : w = p.succ
  · subst w
    rw [replacementSyntax_right]
    exact hB
  obtain ⟨v, hv, rfl⟩ := ((splitVertex_cover p w).resolve_left h₀).resolve_left h₁
  rw [replacementSyntax_other g p part P A B v hv]
  intro u o hu
  exact (g.replacementOtherSyntax_wire p part P v hv u).trans
    (hP v u o hu)

namespace SyntaxState
variable (before after : List (TaggedPending σ)) (parent left right : TaggedPending σ)
    (S : SyntaxState (before ++ [parent] ++ after))

/-- Assemble all retained syntax-state fields for a literal occurrence split.
The child hypotheses are syntax/origin data only, not value or norm certificates. -/
def splitOccurrenceNewWire
    (part : S.graph.Slot (S.occurrence (forestParentIndex before after parent)) → Bool)
    (b : Bool)
    (hnew : (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).Admissible)
    (A : (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).SyntaxAt
      (σ := σ) (S.occurrence (forestParentIndex before after parent)).castSucc)
    (B : (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).SyntaxAt
      (σ := σ) (S.occurrence (forestParentIndex before after parent)).succ)
    (hA : A.1 = if b then right else left) (hB : B.1 = if b then left else right)
    (wire : LabelOrigin → Option (Option S.Edge))
    (hOld : ∀ v u o, pendingPortOrigin (S.pending v) u = some o →
      oldWire (S.originWire o) = wire o)
    (hAo : ∀ u o, pendingPortOrigin A.1 u = some o →
      Sum.elim Subtype.val Subtype.val (A.2.symm u) = wire o)
    (hBo : ∀ u o, pendingPortOrigin B.1 u = some o →
      Sum.elim Subtype.val Subtype.val (B.2.symm u) = wire o) :
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
    originWire := wire
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
  · apply S.graph.replacementSyntax_origin_newWire p part P A B wire _ hAo hBo
    intro v u o hu
    exact (congrArg oldWire (S.origin_spec v u o hu)).trans (hOld v u o hu)

end SyntaxState
variable {D : ℕ}
namespace SyntaxState
variable (before after : List (TaggedPending σ)) (parent left right : TaggedPending σ)
    (S : SyntaxState (before ++ [parent] ++ after))

theorem splitOccurrenceNewWire_value
    (part : S.graph.Slot (S.occurrence (forestParentIndex before after parent)) → Bool)
    (b : Bool)
    (hnew : (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).Admissible)
    (A : (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).SyntaxAt
      (σ := σ) (S.occurrence (forestParentIndex before after parent)).castSucc)
    (B : (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).SyntaxAt
      (σ := σ) (S.occurrence (forestParentIndex before after parent)).succ)
    (hA : A.1 = if b then right else left) (hB : B.1 = if b then left else right)
    (wire : LabelOrigin → Option (Option S.Edge))
    (hOld : ∀ v u o, pendingPortOrigin (S.pending v) u = some o →
      oldWire (S.originWire o) = wire o)
    (hAo : ∀ u o, pendingPortOrigin A.1 u = some o →
      Sum.elim Subtype.val Subtype.val (A.2.symm u) = wire o)
    (hBo : ∀ u o, pendingPortOrigin B.1 u = some o →
      Sum.elim Subtype.val Subtype.val (B.2.symm u) = wire o)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    (S.splitOccurrenceNewWire before after parent left right part b hnew A B hA hB wire hOld hAo hBo).value ρ H x =
    letI := S.edgeFintype
    (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).coordinateEval D
      (S.graph.replacementFamily (S.occurrence (forestParentIndex before after parent)) part (S.tensors ρ H x)
        ((S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).pendingTensor (S.occurrence (forestParentIndex before after parent)).castSucc ρ H A.1 A.2 x)
        ((S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).pendingTensor (S.occurrence (forestParentIndex before after parent)).succ ρ H B.1 B.2 x)) := by
  let _ := S.edgeFintype
  change (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).coordinateEval D
    (fun w => (S.graph.replaceVertex (S.occurrence (forestParentIndex before after parent)) part).pendingTensor w ρ H
      (S.graph.replacementSyntax (S.occurrence (forestParentIndex before after parent)) part (fun v => ⟨S.pending v, S.ports v⟩) A B w).1
      (S.graph.replacementSyntax (S.occurrence (forestParentIndex before after parent)) part (fun v => ⟨S.pending v, S.ports v⟩) A B w).2 x) = _
  rw [replacementSyntax_tensorFamily]
  rfl

end SyntaxState
end AcceleratedLogConcave.Tensor.Ordered.Graph
