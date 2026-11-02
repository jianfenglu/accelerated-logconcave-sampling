import AcceleratedLogConcave.Tensor.NetworkChildOrigins
import AcceleratedLogConcave.Tensor.NetworkSyntaxReplacement

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool)
    (hi : ∃ q : g.InPort p, part (.inl q) = false)
    (ho : ∃ q : g.OutPort p, part (.inr q) = true)

/-- Literal child syntax, retaining the route's ordered origin list. -/
def contractChildSyntax {r j : ℕ} (J : List LabelOrigin) (hJ : J.length = j)
    (A : List (Fin j)) (node : NodeAddress) (E : Expr σ (r+2))
    (b : Bool) (i : Fin (r+2))
    (selected : (Fin A.length ⊕ Fin (r+1)) ≃ {z : g.Slot p // part z = b}) :
    (g.replaceVertex p part).SyntaxAt (σ := σ) (splitVertex p p b) :=
  ⟨.formula node E (A.map (fun u => J.get (Fin.cast hJ.symm u))),
    (g.decoratedOperandEquiv p part hi ho b i selected).symm.trans
      (Equiv.sumCongr (finCongr (List.length_map _).symm) (Equiv.refl _))⟩

theorem contractChildSyntax_origin {r j : ℕ} (J : List LabelOrigin) (hJ : J.length = j)
    (A : List (Fin j)) (node : NodeAddress) (E : Expr σ (r+2))
    (b : Bool) (i : Fin (r+2))
    (selected : (Fin A.length ⊕ Fin (r+1)) ≃ {z : g.Slot p // part z = b})
    (wire : LabelOrigin → Option Edge)
    (h : ∀ u, Sum.elim Subtype.val Subtype.val (selected (.inl u)).val =
      wire (J.get (Fin.cast hJ.symm (A.get u)))) :
    let Q := g.contractChildSyntax p part hi ho J hJ A node E b i selected
    ∀ u o, pendingPortOrigin Q.1 u = some o →
      Sum.elim Subtype.val Subtype.val (Q.2.symm u) = oldWire (wire o) := by
  dsimp only
  intro u o hu
  change Fin (A.map (fun v => J.get (Fin.cast hJ.symm v))).length ⊕ Fin (r+2) at u
  cases u with
  | inr v => cases hu
  | inl v =>
    have hv : o = J.get (Fin.cast hJ.symm (A.get (Fin.cast (List.length_map _) v))) := by
      simpa [pendingPortOrigin, contractChildSyntax] using hu.symm
    subst o
    exact g.decoratedOperandEquiv_origin p part hi ho b i selected
      (fun u => J.get (Fin.cast hJ.symm (A.get u))) wire h _

end AcceleratedLogConcave.Tensor.Ordered.Graph
