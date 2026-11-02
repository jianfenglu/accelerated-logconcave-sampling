import AcceleratedLogConcave.Tensor.NetworkIBPEndpointSyntax
import AcceleratedLogConcave.Tensor.NetworkIBPForest

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge)
    (p q : Fin (n+1)) (hne : p ≠ q)

/-- Literal principal branch metadata, retaining every untouched vertex. -/
def ibpSyntaxFamily (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.recipientGraph p q hne).SyntaxAt (σ := σ) p)
    (B : (g.recipientGraph p q hne).SyntaxAt (σ := σ) q)
    (v : Fin (n+1)) : (g.recipientGraph p q hne).SyntaxAt (σ := σ) v :=
  if h : v = p then transportSyntaxAt _ h.symm A
  else if h' : v = q then transportSyntaxAt _ h'.symm B
  else g.ibpOtherSyntax p q hne v h h' (P v).1 (P v).2

 theorem ibpSyntaxFamily_source (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.recipientGraph p q hne).SyntaxAt (σ := σ) p)
    (B : (g.recipientGraph p q hne).SyntaxAt (σ := σ) q) :
    g.ibpSyntaxFamily p q hne P A B p = A := by
  simp [ibpSyntaxFamily, transportSyntaxAt]

 theorem ibpSyntaxFamily_target (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.recipientGraph p q hne).SyntaxAt (σ := σ) p)
    (B : (g.recipientGraph p q hne).SyntaxAt (σ := σ) q) :
    g.ibpSyntaxFamily p q hne P A B q = B := by
  simp [ibpSyntaxFamily, hne.symm, transportSyntaxAt]

 theorem ibpSyntaxFamily_other (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.recipientGraph p q hne).SyntaxAt (σ := σ) p)
    (B : (g.recipientGraph p q hne).SyntaxAt (σ := σ) q)
    (v : Fin (n+1)) (hvp : v ≠ p) (hvq : v ≠ q) :
    g.ibpSyntaxFamily p q hne P A B v =
      g.ibpOtherSyntax p q hne v hvp hvq (P v).1 (P v).2 := by
  simp [ibpSyntaxFamily, hvp, hvq]

 theorem ibpSyntaxFamily_origin (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.recipientGraph p q hne).SyntaxAt (σ := σ) p)
    (B : (g.recipientGraph p q hne).SyntaxAt (σ := σ) q)
    (wire : LabelOrigin → Option (Option Edge))
    (hP : ∀ v u o, pendingPortOrigin (P v).1 u = some o →
      oldWire (Sum.elim Subtype.val Subtype.val ((P v).2.symm u)) = wire o)
    (hA : ∀ u o, pendingPortOrigin A.1 u = some o →
      Sum.elim Subtype.val Subtype.val (A.2.symm u) = wire o)
    (hB : ∀ u o, pendingPortOrigin B.1 u = some o →
      Sum.elim Subtype.val Subtype.val (B.2.symm u) = wire o) :
    ∀ v u o, pendingPortOrigin (g.ibpSyntaxFamily p q hne P A B v).1 u = some o →
      Sum.elim Subtype.val Subtype.val
        ((g.ibpSyntaxFamily p q hne P A B v).2.symm u) = wire o := by
  intro v
  by_cases hp : v = p
  · subst v
    rw [ibpSyntaxFamily_source]
    exact hA
  by_cases hq : v = q
  · subst v
    rw [ibpSyntaxFamily_target]
    exact hB
  rw [ibpSyntaxFamily_other g p q hne P A B v hp hq]
  exact g.ibpOtherSyntax_origin p q hne v hp hq (P v).1 (P v).2 wire (hP v)

end AcceleratedLogConcave.Tensor.Ordered.Graph
