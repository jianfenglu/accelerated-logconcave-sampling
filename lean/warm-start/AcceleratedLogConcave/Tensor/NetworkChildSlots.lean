import AcceleratedLogConcave.Tensor.NetworkContract

/-! Exact child-slot equivalence: inherited parent ports plus the fresh joining port. -/
noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool)
    (hI : ∃ q : g.InPort p, part (.inl q) = false)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true)

def childSlotMap (b : Bool) : ({s : g.Slot p // part s = b} ⊕ Unit) →
    (g.replaceVertex p part).Slot (splitVertex p p b)
  | .inl s => g.inheritedChildSlot p part hI hO b s.val s.property
  | .inr _ => g.joiningChildSlot p part b

private theorem oldWire_ne_fresh (w : Option Edge) : oldWire w ≠ some none := by
  change Option.map some w ≠ some none
  cases w <;> simp

private theorem splitVertex_parent_injective : Function.Injective (fun b : Bool => splitVertex p p b) := by
  intro a b h
  cases a <;> cases b <;> simp_all [Fin.ext_iff]

 theorem childSlotMap_injective (b : Bool) : Function.Injective (g.childSlotMap p part hI hO b) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      apply congrArg Sum.inl
      apply Subtype.ext
      rcases x with ⟨x,hx⟩
      rcases y with ⟨y,hy⟩
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have hh := congrArg Subtype.val (Sum.inl.inj h)
          exact congrArg Sum.inl (Subtype.ext (oldWire.injective hh))
        | inr y => cases h
      | inr x =>
        cases y with
        | inl y => cases h
        | inr y =>
          have hh := congrArg Subtype.val (Sum.inr.inj h)
          exact congrArg Sum.inr (Subtype.ext (oldWire.injective hh))
    | inr y =>
      rcases x with ⟨x,hx⟩
      cases x <;> cases b <;>
        simp_all [childSlotMap,inheritedChildSlot,joiningChildSlot,
          replaceInChildEmbedding,replaceOutChildEmbedding,oldWire]
      all_goals exact oldWire_ne_fresh _ (congrArg Subtype.val h)
  | inr x =>
    cases y with
    | inl y =>
      rcases y with ⟨y,hy⟩
      cases y <;> cases b <;>
        simp_all [childSlotMap,inheritedChildSlot,joiningChildSlot,
          replaceInChildEmbedding,replaceOutChildEmbedding,oldWire]
      all_goals exact oldWire_ne_fresh _ (congrArg Subtype.val h).symm
    | inr y => cases x; cases y; rfl

 theorem childSlotMap_surjective (b : Bool) : Function.Surjective (g.childSlotMap p part hI hO b) := by
  intro z
  cases z with
  | inl q =>
    rcases q with ⟨w,h⟩
    cases w with
    | none =>
      change splitVertex p p b = 0 at h
      have hp : p = 0 := splitVertex_eq_implies p p 0 b false (h.trans (splitVertex_zero p).symm)
      subst p
      have hb : b = false := splitVertex_parent_injective 0 (h.trans (splitVertex_zero 0).symm)
      subst b
      obtain ⟨q,hq⟩ := hI
      have he : q = ⟨none,rfl⟩ := Subtype.ext (g.first_inPort q)
      subst q
      refine ⟨.inl ⟨.inl ⟨none,rfl⟩,hq⟩, ?_⟩
      rfl
    | some w =>
      cases w with
      | none =>
        change p.succ = splitVertex p p b at h
        have hb : b = true := splitVertex_parent_injective p
          (h.symm.trans (splitVertex_parent_true p).symm)
        subst b
        exact ⟨.inr (), rfl⟩
      | some e =>
        change splitVertex p (g.target e) (g.replacementInFlag p part e) = splitVertex p p b at h
        have ht : g.target e = p := splitVertex_eq_implies p _ _ _ _ h
        have hf : part (.inl ⟨some e,ht⟩) = b := splitVertex_parent_injective p
          (by simpa [replacementInFlag,ht] using h)
        exact ⟨.inl ⟨.inl ⟨some e,ht⟩,hf⟩, rfl⟩
  | inr q =>
    rcases q with ⟨w,h⟩
    cases w with
    | none =>
      change splitVertex p p b = Fin.last (n+1) at h
      have hp : p = Fin.last n := splitVertex_eq_implies p p (Fin.last n) b true
        (h.trans (splitVertex_last p).symm)
      subst p
      have hb : b = true := splitVertex_parent_injective (Fin.last n)
        (h.trans (splitVertex_last (Fin.last n)).symm)
      subst b
      obtain ⟨q,hq⟩ := hO
      have he : q = ⟨none,rfl⟩ := Subtype.ext (g.last_outPort q)
      subst q
      exact ⟨.inl ⟨.inr ⟨none,rfl⟩,hq⟩, rfl⟩
    | some w =>
      cases w with
      | none =>
        change p.castSucc = splitVertex p p b at h
        have hb : b = false := splitVertex_parent_injective p
          (h.symm.trans (splitVertex_parent_false p).symm)
        subst b
        exact ⟨.inr (), rfl⟩
      | some e =>
        change splitVertex p (g.source e) (g.replacementOutFlag p part e) = splitVertex p p b at h
        have ht : g.source e = p := splitVertex_eq_implies p _ _ _ _ h
        have hf : part (.inr ⟨some e,ht⟩) = b := splitVertex_parent_injective p
          (by simpa [replacementOutFlag,ht] using h)
        exact ⟨.inl ⟨.inr ⟨some e,ht⟩,hf⟩, rfl⟩

/-- No unused or duplicated child coordinate is hidden in replacement. -/
def childSlotEquiv (b : Bool) : ({s : g.Slot p // part s = b} ⊕ Unit) ≃
    (g.replaceVertex p part).Slot (splitVertex p p b) :=
  Equiv.ofBijective (g.childSlotMap p part hI hO b)
    ⟨g.childSlotMap_injective p part hI hO b, g.childSlotMap_surjective p part hI hO b⟩

@[simp] theorem childSlotEquiv_apply_inherited (b : Bool) (s : g.Slot p) (hs : part s = b) :
    g.childSlotEquiv p part hI hO b (.inl ⟨s,hs⟩) =
      g.inheritedChildSlot p part hI hO b s hs := rfl

@[simp] theorem childSlotEquiv_apply_joining (b : Bool) :
    g.childSlotEquiv p part hI hO b (.inr ()) = g.joiningChildSlot p part b := rfl

include hI hO in
theorem childSlot_card [Fintype Edge] (b : Bool) :
    Fintype.card ((g.replaceVertex p part).Slot (splitVertex p p b)) =
      Fintype.card {s : g.Slot p // part s = b} + 1 := by
  rw [← Fintype.card_congr (g.childSlotEquiv p part hI hO b)]
  simp

end AcceleratedLogConcave.Tensor.Ordered.Graph
