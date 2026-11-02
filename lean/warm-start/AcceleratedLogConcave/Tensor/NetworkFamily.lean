import AcceleratedLogConcave.Tensor.NetworkContract

/-! Assemble the actual refined family at all occurrence positions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n D : ℕ} {Edge : Type*} [Fintype Edge]
variable (g : Graph n Edge) (p : Fin (n+1)) (part : g.Slot p → Bool)

omit [Fintype Edge] in
private theorem replacement_old_exists (w : Fin (n+2))
    (h₀ : w ≠ p.castSucc) (h₁ : w ≠ p.succ) :
    ∃ v : Fin (n+1), v ≠ p ∧ splitVertex p v false = w :=
  ((splitVertex_cover p w).resolve_left h₀).resolve_left h₁

def replacementFamily (T : g.Tensors D)
    (A : Coeff ((g.replaceVertex p part).Slot p.castSucc) D)
    (B : Coeff ((g.replaceVertex p part).Slot p.succ) D) :
    (g.replaceVertex p part).Tensors D := fun w =>
  if h₀ : w = p.castSucc then h₀.symm ▸ A
  else if h₁ : w = p.succ then h₁.symm ▸ B
  else
    let hv := replacement_old_exists p w h₀ h₁
    (Classical.choose_spec hv).2 ▸
      g.replacementOtherTensor p part T (Classical.choose hv) (Classical.choose_spec hv).1

@[simp] theorem replacementFamily_left (T : g.Tensors D)
    (A : Coeff ((g.replaceVertex p part).Slot p.castSucc) D)
    (B : Coeff ((g.replaceVertex p part).Slot p.succ) D) :
    g.replacementFamily p part T A B p.castSucc = A := by simp [replacementFamily]

@[simp] theorem replacementFamily_right (T : g.Tensors D)
    (A : Coeff ((g.replaceVertex p part).Slot p.castSucc) D)
    (B : Coeff ((g.replaceVertex p part).Slot p.succ) D) :
    g.replacementFamily p part T A B p.succ = B := by
  have h : p.succ ≠ p.castSucc := by intro hh; have := congrArg Fin.val hh; simp at this
  simp [replacementFamily,h]

theorem replacementFamily_other (T : g.Tensors D)
    (A : Coeff ((g.replaceVertex p part).Slot p.castSucc) D)
    (B : Coeff ((g.replaceVertex p part).Slot p.succ) D)
    (v : Fin (n+1)) (hv : v ≠ p) :
    g.replacementFamily p part T A B (splitVertex p v false) =
      g.replacementOtherTensor p part T v hv := by
  have h₀ : splitVertex p v false ≠ p.castSucc := by
    intro h
    exact hv (splitVertex_eq_implies p v p false false
      (h.trans (splitVertex_parent_false p).symm))
  have h₁ : splitVertex p v false ≠ p.succ := by
    intro h
    exact hv (splitVertex_eq_implies p v p false true
      (h.trans (splitVertex_parent_true p).symm))
  simp only [replacementFamily, dite_eq_right h₀, dite_eq_right h₁]
  have htransport (u : Fin (n+1)) (hu : u ≠ p)
      (he : splitVertex p u false = splitVertex p v false) :
      (he ▸ g.replacementOtherTensor p part T u hu) =
        g.replacementOtherTensor p part T v hv := by
    have huv := splitVertex_eq_implies p u v false false he
    subst u
    rfl
  exact htransport _ _ _

/-- The full replaced-family equality now needs only the local parent contraction. -/
theorem coordinateEval_replacementFamily (T : g.Tensors D)
    (A : Coeff ((g.replaceVertex p part).Slot p.castSucc) D)
    (B : Coeff ((g.replaceVertex p part).Slot p.succ) D)
    (hparent : ∀ c, g.wireValue T c p = ∑ k : Fin D,
      A (Sum.elim (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) *
      B (Sum.elim (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val))) :
    g.coordinateEval D T =
      (g.replaceVertex p part).coordinateEval D (g.replacementFamily p part T A B) := by
  apply g.coordinateEval_replaceVertex p part T
  · intro c k v hv
    unfold wireValue
    rw [g.replacementFamily_other p part T A B v hv]
    exact g.replacementOtherTensor_wireValue p part T v hv c k
  · intro c
    simpa only [wireValue, replacementFamily_left, replacementFamily_right] using hparent c

private theorem transportTensor_value (v w : Fin (n+1)) (h : v = w)
    (A : Coeff (g.Slot v) D) (c : Option Edge → Fin D) :
    (h ▸ A : Coeff (g.Slot w) D)
      (Sum.elim (fun q => c q.val) (fun q => c q.val)) =
    A (Sum.elim (fun q => c q.val) (fun q => c q.val)) := by
  subst w
  rfl

/-- A literal parent contraction has a complete evaluated, admissible two-child replacement.
Only slot placement/orientation and the parent's actual local tensor representation are inputs. -/
theorem exists_contract_replacement {r s : ℕ} (hg : g.Admissible)
    (hI : ∃ q : g.InPort p, part (.inl q) = false)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true)
    (T : g.Tensors D) (A : Coeff (Fin (r+2)) D) (B : Coeff (Fin (s+2)) D)
    (i : Fin (r+2)) (j : Fin (s+2)) (e : g.Slot p ≃ Fin (r+s+2))
    (la : Fin (r+1) → g.Slot p) (ra : Fin (s+1) → g.Slot p)
    (hla : ∀ u, part (la u) = false) (hra : ∀ u, part (ra u) = true)
    (hel : ∀ u, e (la u) = Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.castAdd (s+1) u))
    (her : ∀ u, e (ra u) = Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.natAdd (r+1) u))
    (hparent : ∀ a, T p a = crossContract D A B i j (a ∘ e.symm)) :
    ∃ U : (g.replaceVertex p part).Tensors D,
      (g.replaceVertex p part).Admissible ∧
      g.coordinateEval D T = (g.replaceVertex p part).coordinateEval D U := by
  let A₀ := g.contractChildTensor p part hI hO false A i la hla
  let B₀ := g.contractChildTensor p part hI hO true B j ra hra
  let A' : Coeff ((g.replaceVertex p part).Slot p.castSucc) D :=
    splitVertex_parent_false p ▸ A₀
  let B' : Coeff ((g.replaceVertex p part).Slot p.succ) D :=
    splitVertex_parent_true p ▸ B₀
  refine ⟨g.replacementFamily p part T A' B', g.replaceVertex_admissible hg p part hI hO, ?_⟩
  apply g.coordinateEval_replacementFamily p part T A' B'
  intro c
  have hh := g.crossContract_children_value p part hI hO A B i j e la ra hla hra hel her c
  unfold wireValue
  rw [hparent]
  simp only [Function.comp_def]
  rw [hh]
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg₂ (fun x y : ℝ => x*y)
  · exact ((g.replaceVertex p part).transportTensor_value _ _
      (splitVertex_parent_false p) A₀ (extendAssignment c k)).symm
  · exact ((g.replaceVertex p part).transportTensor_value _ _
      (splitVertex_parent_true p) B₀ (extendAssignment c k)).symm

end AcceleratedLogConcave.Tensor.Ordered.Graph
