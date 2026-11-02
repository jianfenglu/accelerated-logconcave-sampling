import AcceleratedLogConcave.Tensor.NetworkScoreCoordinates
import AcceleratedLogConcave.Tensor.NetworkChildOrigins

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))

def selectedScoreEquiv {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (A : List (Fin j)) (hA : A.Nodup) (part : g.Slot p → Bool) (b : Bool)
    (hlabel : ∀ u, part (e.symm (.inl u)) = b ↔ u ∈ A)
    (hfree : ∀ u, part (e.symm (.inr u)) = !b) :
    Fin A.length ≃ {z : g.Slot p // part z = b} :=
  Equiv.ofBijective (fun u => ⟨e.symm (.inl (A.get u)),(hlabel _).2 (List.get_mem ..)⟩) (by
    constructor
    · intro u v h
      have he : A.get u = A.get v := by
        simpa using congrArg e (congrArg Subtype.val h)
      exact hA.injective_get he
    · intro z
      have hz := e.symm_apply_apply z.val
      generalize hw : e z.val = w at hz
      cases w with
      | inl u =>
        have hu : u ∈ A := (hlabel u).1 (by rw [hz]; exact z.property)
        let v := (List.Nodup.getEquiv A hA).symm ⟨u,hu⟩
        have hv : A.get v = u := congrArg Subtype.val
          ((List.Nodup.getEquiv A hA).apply_symm_apply ⟨u,hu⟩)
        refine ⟨v,Subtype.ext ?_⟩
        change e.symm (.inl (A.get v)) = z.val
        rw [hv,hz]
      | inr u =>
        have hh := hfree u
        rw [hz,z.property] at hh
        cases b <;> cases hh)

def selectedScoreOperandEquiv {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (A : List (Fin j)) (hA : A.Nodup) (part : g.Slot p → Bool) (b : Bool)
    (hlabel : ∀ u, part (e.symm (.inl u)) = b ↔ u ∈ A)
    (hfree : ∀ u, part (e.symm (.inr u)) = b) :
    (Fin A.length ⊕ Fin f) ≃ {z : g.Slot p // part z = b} :=
  Equiv.ofBijective (fun z => match z with
    | .inl u => ⟨e.symm (.inl (A.get u)),(hlabel _).2 (List.get_mem ..)⟩
    | .inr u => ⟨e.symm (.inr u),hfree u⟩) (by
    constructor
    · intro u v h
      have he := congrArg e (congrArg Subtype.val h)
      cases u with
      | inl u =>
        cases v with
        | inl v => exact congrArg Sum.inl (hA.injective_get (by simpa using he))
        | inr v => simp at he
      | inr u =>
        cases v with
        | inl v => simp at he
        | inr v => exact congrArg Sum.inr (by simpa using he)
    · intro z
      have hz := e.symm_apply_apply z.val
      generalize hw : e z.val = w at hz
      cases w with
      | inl u =>
        have hu : u ∈ A := (hlabel u).1 (by rw [hz]; exact z.property)
        let v := (List.Nodup.getEquiv A hA).symm ⟨u,hu⟩
        have hv : A.get v = u := congrArg Subtype.val
          ((List.Nodup.getEquiv A hA).apply_symm_apply ⟨u,hu⟩)
        refine ⟨.inl v,Subtype.ext ?_⟩
        change e.symm (.inl (A.get v)) = z.val
        rw [hv,hz]
      | inr u => exact ⟨.inr u,Subtype.ext hz⟩)

def scoreRouteSelected {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ scoreRoutes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hs : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (ho : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (hf : ∀ u, part (g.adjointFreeSlot p e u) = !b) :
    Fin route.1.length ≃ {z : g.Slot p // part z = b} := by
  have hr' : route ∈ routes (List.finRange j) := by rw [routes_eq]; exact List.mem_cons_of_mem _ hr
  exact g.selectedScoreEquiv p e route.1
    ((List.nodup_append.mp ((route_perm _ route hr').nodup_iff.mpr (List.nodup_finRange j))).1)
    part b (fun u => route_left_flag_iff route hr' _ b hs ho u) hf

def scoreOperandSelected {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ scoreRoutes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hs : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (ho : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (hf : ∀ u, part (g.adjointFreeSlot p e u) = !b) :
    (Fin route.2.length ⊕ Fin f) ≃ {z : g.Slot p // part z = !b} := by
  have hr' : route ∈ routes (List.finRange j) := by rw [routes_eq]; exact List.mem_cons_of_mem _ hr
  apply g.selectedScoreOperandEquiv p e route.2
    ((List.nodup_append.mp ((route_perm _ route hr').nodup_iff.mpr (List.nodup_finRange j))).2.1)
    part (!b) _ hf
  intro u
  constructor
  · intro h
    have hm := (route_perm _ route hr').mem_iff.mpr (List.mem_finRange u)
    rcases List.mem_append.mp hm with hA | hB
    · have hh := h.symm.trans (hs u hA)
      cases b <;> cases hh
    · exact hB
  · exact ho u

theorem scoreRouteSelected_apply {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ scoreRoutes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hs : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (ho : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (hf : ∀ u, part (g.adjointFreeSlot p e u) = !b) (u : Fin route.1.length) :
    (g.scoreRouteSelected p e route hr part b hs ho hf u).val =
      g.decoratedLabelSlot p e (route.1.get u) := rfl

theorem scoreOperandSelected_derivative {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ scoreRoutes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hs : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (ho : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (hf : ∀ u, part (g.adjointFreeSlot p e u) = !b) (u : Fin route.2.length) :
    (g.scoreOperandSelected p e route hr part b hs ho hf (.inl u)).val =
      g.decoratedLabelSlot p e (route.2.get u) := rfl

theorem scoreOperandSelected_free {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ scoreRoutes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hs : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (ho : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (hf : ∀ u, part (g.adjointFreeSlot p e u) = !b) (u : Fin f) :
    (g.scoreOperandSelected p e route hr part b hs ho hf (.inr u)).val =
      g.adjointFreeSlot p e u := rfl

variable (part : g.Slot p → Bool)
    (hi : ∃ q : g.InPort p, part (.inl q) = false)
    (ho : ∃ q : g.OutPort p, part (.inr q) = true)

def scoreChildEquiv {a : ℕ} (b : Bool)
    (selected : Fin a ≃ {z : g.Slot p // part z = b}) :
    (Fin a ⊕ Unit) ≃ (g.replaceVertex p part).Slot (splitVertex p p b) :=
  (Equiv.sumCongr selected (Equiv.refl Unit)).trans (g.childSlotEquiv p part hi ho b)

theorem scoreChildEquiv_derivative {a : ℕ} (b : Bool)
    (selected : Fin a ≃ {z : g.Slot p // part z = b}) (u : Fin a) :
    g.scoreChildEquiv p part hi ho b selected (.inl u) =
      g.inheritedChildSlot p part hi ho b (selected u).val (selected u).property := rfl

theorem scoreChildEquiv_joining {a : ℕ} (b : Bool)
    (selected : Fin a ≃ {z : g.Slot p // part z = b}) :
    g.scoreChildEquiv p part hi ho b selected (.inr ()) = g.joiningChildSlot p part b := rfl

end AcceleratedLogConcave.Tensor.Ordered.Graph
