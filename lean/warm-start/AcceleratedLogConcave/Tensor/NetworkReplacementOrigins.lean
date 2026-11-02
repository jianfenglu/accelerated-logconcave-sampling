import AcceleratedLogConcave.Tensor.NetworkSyntaxReplacement

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool)

/-- Origin transport for the assembled family, retaining both child proofs. -/
theorem replacementSyntax_origin
    (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.replaceVertex p part).SyntaxAt (σ := σ) p.castSucc)
    (B : (g.replaceVertex p part).SyntaxAt (σ := σ) p.succ)
    (wire : LabelOrigin → Option Edge)
    (hP : ∀ v u o, pendingPortOrigin (P v).1 u = some o →
      Sum.elim Subtype.val Subtype.val ((P v).2.symm u) = wire o)
    (hA : ∀ u o, pendingPortOrigin A.1 u = some o →
      Sum.elim Subtype.val Subtype.val (A.2.symm u) = oldWire (wire o))
    (hB : ∀ u o, pendingPortOrigin B.1 u = some o →
      Sum.elim Subtype.val Subtype.val (B.2.symm u) = oldWire (wire o)) :
    ∀ w u o, pendingPortOrigin (g.replacementSyntax p part P A B w).1 u = some o →
      Sum.elim Subtype.val Subtype.val
        ((g.replacementSyntax p part P A B w).2.symm u) = oldWire (wire o) := by
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
    (congrArg oldWire (hP v u o hu))

end AcceleratedLogConcave.Tensor.Ordered.Graph
