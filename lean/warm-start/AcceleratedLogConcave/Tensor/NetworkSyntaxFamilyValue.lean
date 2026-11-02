import AcceleratedLogConcave.Tensor.NetworkSyntaxSplitState
import AcceleratedLogConcave.Tensor.NetworkFamily

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {D n : ℕ} {Edge : Type*} [Fintype Edge]
    (g : Graph n Edge) (p : Fin (n+1)) (part : g.Slot p → Bool)

 theorem replacementSyntax_tensorFamily
    (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.replaceVertex p part).SyntaxAt (σ := σ) p.castSucc)
    (B : (g.replaceVertex p part).SyntaxAt (σ := σ) p.succ)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    (fun w => (g.replaceVertex p part).pendingTensor w ρ H
      (g.replacementSyntax p part P A B w).1 (g.replacementSyntax p part P A B w).2 x) =
    g.replacementFamily p part (fun v => g.pendingTensor v ρ H (P v).1 (P v).2 x)
      ((g.replaceVertex p part).pendingTensor p.castSucc ρ H A.1 A.2 x)
      ((g.replaceVertex p part).pendingTensor p.succ ρ H B.1 B.2 x) := by
  funext w
  by_cases h₀ : w = p.castSucc
  · subst w
    rw [replacementSyntax_left, replacementFamily_left]
  by_cases h₁ : w = p.succ
  · subst w
    rw [replacementSyntax_right, replacementFamily_right]
  obtain ⟨v,hv,rfl⟩ := ((splitVertex_cover p w).resolve_left h₀).resolve_left h₁
  rw [replacementSyntax_other, replacementFamily_other]
  exact g.replacementOtherSyntax_tensor p part P v hv ρ H x

namespace SyntaxState
variable (before after : List (TaggedPending σ)) (parent left right : TaggedPending σ)
    (S : SyntaxState (before ++ [parent] ++ after))

theorem splitOccurrence_value
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
      Sum.elim Subtype.val Subtype.val (B.2.symm u) = oldWire (S.originWire o))
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    (S.splitOccurrence before after parent left right part b hnew A B hA hB hAo hBo).value ρ H x =
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
