import AcceleratedLogConcave.Tensor.NetworkSyntaxState
import AcceleratedLogConcave.Tensor.NetworkReplacement

/-! Dependent syntax-and-port metadata at all vertices of a literal graph replacement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool)

abbrev SyntaxAt (v : Fin (n+1)) := Σ q : TaggedPending σ, g.Slot v ≃ pendingPorts q

def replacementOtherSyntax (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (v : Fin (n+1)) (hv : v ≠ p) :
    (g.replaceVertex p part).SyntaxAt (σ := σ) (splitVertex p v false) :=
  ⟨(P v).1, (Equiv.sumCongr (g.replaceInOtherEquiv p v part hv)
    (g.replaceOutOtherEquiv p v part hv)).symm.trans (P v).2⟩

private theorem old_vertex_exists (w : Fin (n+2))
    (h₀ : w ≠ p.castSucc) (h₁ : w ≠ p.succ) :
    ∃ v : Fin (n+1), v ≠ p ∧ splitVertex p v false = w :=
  ((splitVertex_cover p w).resolve_left h₀).resolve_left h₁

def replacementSyntax (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.replaceVertex p part).SyntaxAt (σ := σ) p.castSucc)
    (B : (g.replaceVertex p part).SyntaxAt (σ := σ) p.succ) :
    ∀ w, (g.replaceVertex p part).SyntaxAt (σ := σ) w := fun w =>
  if h₀ : w = p.castSucc then h₀.symm ▸ A
  else if h₁ : w = p.succ then h₁.symm ▸ B
  else
    let hv := old_vertex_exists p w h₀ h₁
    (Classical.choose_spec hv).2 ▸
      g.replacementOtherSyntax p part P (Classical.choose hv) (Classical.choose_spec hv).1

 theorem replacementSyntax_left (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.replaceVertex p part).SyntaxAt (σ := σ) p.castSucc)
    (B : (g.replaceVertex p part).SyntaxAt (σ := σ) p.succ) :
    g.replacementSyntax p part P A B p.castSucc = A := by simp [replacementSyntax]

 theorem replacementSyntax_right (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.replaceVertex p part).SyntaxAt (σ := σ) p.castSucc)
    (B : (g.replaceVertex p part).SyntaxAt (σ := σ) p.succ) :
    g.replacementSyntax p part P A B p.succ = B := by
  have h : p.succ ≠ p.castSucc := by intro he; have := congrArg Fin.val he; simp at this
  simp [replacementSyntax, h]

 theorem replacementSyntax_other (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (A : (g.replaceVertex p part).SyntaxAt (σ := σ) p.castSucc)
    (B : (g.replaceVertex p part).SyntaxAt (σ := σ) p.succ)
    (v : Fin (n+1)) (hv : v ≠ p) :
    g.replacementSyntax p part P A B (splitVertex p v false) =
      g.replacementOtherSyntax p part P v hv := by
  have h₀ : splitVertex p v false ≠ p.castSucc := by
    intro h
    exact hv (splitVertex_eq_implies p v p false false
      (h.trans (splitVertex_parent_false p).symm))
  have h₁ : splitVertex p v false ≠ p.succ := by
    intro h
    exact hv (splitVertex_eq_implies p v p false true
      (h.trans (splitVertex_parent_true p).symm))
  simp only [replacementSyntax, dite_eq_right h₀, dite_eq_right h₁]
  have ht (u : Fin (n+1)) (hu : u ≠ p)
      (he : splitVertex p u false = splitVertex p v false) :
      (he ▸ g.replacementOtherSyntax p part P u hu) = g.replacementOtherSyntax p part P v hv := by
    have huv := splitVertex_eq_implies p u v false false he
    subst u
    rfl
  exact ht _ _ _

 theorem replacementOtherSyntax_tensor {D : ℕ} [Fintype Edge]
    (P : ∀ v, g.SyntaxAt (σ := σ) v) (v : Fin (n+1)) (hv : v ≠ p)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    let Q := g.replacementOtherSyntax p part P v hv
    (g.replaceVertex p part).pendingTensor (splitVertex p v false) ρ H Q.1 Q.2 x =
      g.replacementOtherTensor p part (fun w => g.pendingTensor w ρ H (P w).1 (P w).2 x) v hv := by
  dsimp only
  unfold replacementOtherSyntax replacementOtherTensor
  dsimp only
  rcases hP : P v with ⟨q,e⟩
  have heq (a : (g.replaceVertex p part).Slot (splitVertex p v false) → Fin D) :
      (fun z : g.Slot v => a ((Equiv.sumCongr (g.replaceInOtherEquiv p v part hv)
        (g.replaceOutOtherEquiv p v part hv)) z)) =
      Sum.elim (fun z => a (.inl (g.replaceInOtherEmbedding p v part hv z)))
        (fun z => a (.inr (g.replaceOutOtherEmbedding p v part hv z))) := by
    funext z
    cases z <;> rfl
  cases q <;> ext a <;>
    simp only [pendingTensor, decoratedSectionTensor, WithLp.ofLp_toLp]
  all_goals rw [← heq]; rfl


theorem replacementOtherSyntax_wire (P : ∀ v, g.SyntaxAt (σ := σ) v)
    (v : Fin (n+1)) (hv : v ≠ p) (u : pendingPorts (P v).1) :
    Sum.elim Subtype.val Subtype.val
      ((g.replacementOtherSyntax p part P v hv).2.symm u) =
      oldWire (Sum.elim Subtype.val Subtype.val ((P v).2.symm u)) := by
  unfold replacementOtherSyntax
  change Sum.elim Subtype.val Subtype.val
    ((Equiv.sumCongr (g.replaceInOtherEquiv p v part hv)
      (g.replaceOutOtherEquiv p v part hv)) ((P v).2.symm u)) = _
  cases (P v).2.symm u <;> rfl

end AcceleratedLogConcave.Tensor.Ordered.Graph
