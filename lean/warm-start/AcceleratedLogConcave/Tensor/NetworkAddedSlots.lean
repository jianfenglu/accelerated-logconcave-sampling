import AcceleratedLogConcave.Tensor.NetworkAddedEdge

/-! Exact endpoint coordinate inventories for principal IBP edges. -/
noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge)
    (p q : Fin (n+1)) (hpq : p < q)

private def slotWire {g : Graph n Edge} {v : Fin (n+1)} : g.Slot v → Option Edge :=
  Sum.elim Subtype.val Subtype.val

private theorem oldWire_ne_fresh (w : Option Edge) : oldWire w ≠ some none := by
  change Option.map some w ≠ some none
  cases w <;> simp

 theorem addedOldSlot_injective (v : Fin (n+1)) :
    Function.Injective (g.addedOldSlot p q hpq v) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl ((g.addEdgeInEmbedding p q hpq v).injective (Sum.inl.inj h))
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b => exact congrArg Sum.inr ((g.addEdgeOutEmbedding p q hpq v).injective (Sum.inr.inj h))

private theorem addedSlot_cases (v : Fin (n+1)) (a : (g.addOrderedEdge p q hpq).Slot v) :
    (∃ b, g.addedOldSlot p q hpq v b = a) ∨ slotWire a = some none := by
  cases a with
  | inl a =>
    rcases a with ⟨w,h⟩
    cases w with
    | none => exact Or.inl ⟨.inl ⟨none,h⟩,rfl⟩
    | some w =>
      cases w with
      | none => exact Or.inr rfl
      | some e => exact Or.inl ⟨.inl ⟨some e,h⟩,rfl⟩
  | inr a =>
    rcases a with ⟨w,h⟩
    cases w with
    | none => exact Or.inl ⟨.inr ⟨none,h⟩,rfl⟩
    | some w =>
      cases w with
      | none => exact Or.inr rfl
      | some e => exact Or.inl ⟨.inr ⟨some e,h⟩,rfl⟩

private theorem source_fresh_unique (a : (g.addOrderedEdge p q hpq).Slot p)
    (ha : slotWire a = some none) : a = g.addedSourceSlot p q hpq := by
  cases a with
  | inl a =>
    rcases a with ⟨w,h⟩
    change w = some none at ha
    subst w
    change q = p at h
    exact False.elim ((ne_of_gt hpq) h)
  | inr a => exact congrArg Sum.inr (Subtype.ext ha)

private theorem target_fresh_unique (a : (g.addOrderedEdge p q hpq).Slot q)
    (ha : slotWire a = some none) : a = g.addedTargetSlot p q hpq := by
  cases a with
  | inl a => exact congrArg Sum.inl (Subtype.ext ha)
  | inr a =>
    rcases a with ⟨w,h⟩
    change w = some none at ha
    subst w
    change p = q at h
    exact False.elim ((ne_of_lt hpq) h)

private theorem endpointSlot_bijective (v : Fin (n+1))
    (fresh : (g.addOrderedEdge p q hpq).Slot v)
    (hf : slotWire fresh = some none)
    (hu : ∀ a, slotWire a = some none → a = fresh) :
    Function.Bijective (Sum.elim (g.addedOldSlot p q hpq v) (fun _ : Unit => fresh)) := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (g.addedOldSlot_injective p q hpq v hab)
      | inr b =>
        have hw := congrArg slotWire hab
        have ho : slotWire (g.addedOldSlot p q hpq v a) = oldWire (slotWire a) := by cases a <;> rfl
        exact False.elim (oldWire_ne_fresh _ (ho.symm.trans (hw.trans hf)))
    | inr a =>
      cases b with
      | inl b =>
        have hw := congrArg slotWire hab.symm
        have ho : slotWire (g.addedOldSlot p q hpq v b) = oldWire (slotWire b) := by cases b <;> rfl
        exact False.elim (oldWire_ne_fresh _ (ho.symm.trans (hw.trans hf)))
      | inr b => cases a; cases b; rfl
  · intro a
    rcases g.addedSlot_cases p q hpq v a with ⟨b,hb⟩ | ha
    · exact ⟨.inl b,hb⟩
    · exact ⟨.inr (), (hu a ha).symm⟩

/-- Source has precisely its old ports and one new outgoing port. -/
def addedSourceSlotEquiv : (g.Slot p ⊕ Unit) ≃ (g.addOrderedEdge p q hpq).Slot p :=
  Equiv.ofBijective (Sum.elim (g.addedOldSlot p q hpq p) (fun _ : Unit => g.addedSourceSlot p q hpq))
    (g.endpointSlot_bijective p q hpq p _ rfl (g.source_fresh_unique p q hpq))

/-- Target has precisely its old ports and one new incoming port. -/
def addedTargetSlotEquiv : (g.Slot q ⊕ Unit) ≃ (g.addOrderedEdge p q hpq).Slot q :=
  Equiv.ofBijective (Sum.elim (g.addedOldSlot p q hpq q) (fun _ : Unit => g.addedTargetSlot p q hpq))
    (g.endpointSlot_bijective p q hpq q _ rfl (g.target_fresh_unique p q hpq))

 theorem addedSourceSlotEquiv_old (a : g.Slot p) :
    g.addedSourceSlotEquiv p q hpq (.inl a) = g.addedOldSlot p q hpq p a := rfl
 theorem addedSourceSlotEquiv_fresh :
    g.addedSourceSlotEquiv p q hpq (.inr ()) = g.addedSourceSlot p q hpq := rfl
 theorem addedTargetSlotEquiv_old (a : g.Slot q) :
    g.addedTargetSlotEquiv p q hpq (.inl a) = g.addedOldSlot p q hpq q a := rfl
 theorem addedTargetSlotEquiv_fresh :
    g.addedTargetSlotEquiv p q hpq (.inr ()) = g.addedTargetSlot p q hpq := rfl
/-- No coordinate is added to an unaffected occurrence. -/
def addedOtherSlotEquiv (v : Fin (n+1)) (hvp : v ≠ p) (hvq : v ≠ q) :
    g.Slot v ≃ (g.addOrderedEdge p q hpq).Slot v :=
  Equiv.ofBijective (g.addedOldSlot p q hpq v) ⟨g.addedOldSlot_injective p q hpq v, by
    intro a
    rcases g.addedSlot_cases p q hpq v a with h | ha
    · exact h
    · cases a with
      | inl a =>
        rcases a with ⟨w,h⟩
        change w = some none at ha
        subst w
        exact False.elim (hvq h.symm)
      | inr a =>
        rcases a with ⟨w,h⟩
        change w = some none at ha
        subst w
        exact False.elim (hvp h.symm)⟩

 theorem addedOtherSlotEquiv_old (v : Fin (n+1)) (hvp : v ≠ p) (hvq : v ≠ q) (a : g.Slot v) :
    g.addedOtherSlotEquiv p q hpq v hvp hvq a = g.addedOldSlot p q hpq v a := rfl
end AcceleratedLogConcave.Tensor.Ordered.Graph
