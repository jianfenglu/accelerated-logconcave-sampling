import AcceleratedLogConcave.Tensor.NetworkDecoratedPartition

/-! Nonempty score routes determine an admissible, provenance-retaining split. -/
noncomputable section
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))

def adjointFreeSlot {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f)) (u : Fin f) :
    g.Slot p := e.symm (.inr u)

def scorePartition {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (route : List (Fin j) × List (Fin j)) (a : g.Slot p) : Bool :=
  match e a with
  | .inl u => decide (u ∈ route.2)
  | .inr _ => true

 theorem scorePartition_free {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (route : List (Fin j) × List (Fin j)) (u : Fin f) :
    g.scorePartition p e route (g.adjointFreeSlot p e u) = true := by
  simp [scorePartition, adjointFreeSlot]

 theorem scorePartition_scoreLabel {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ scoreRoutes (List.finRange j))
    (u : Fin j) (hu : u ∈ route.1) :
    g.scorePartition p e route (g.decoratedLabelSlot p e u) = false := by
  have hr' : route ∈ routes (List.finRange j) := by rw [routes_eq]; exact List.mem_cons_of_mem _ hr
  have hn : (route.1 ++ route.2).Nodup :=
    (route_perm (List.finRange j) route hr').nodup_iff.mpr (List.nodup_finRange j)
  have hu' : u ∉ route.2 := (List.disjoint_left.mp (List.disjoint_of_nodup_append hn)) hu
  simp [scorePartition, decoratedLabelSlot, hu']

 theorem scorePartition_operandLabel {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f))
    (route : List (Fin j) × List (Fin j)) (u : Fin j) (hu : u ∈ route.2) :
    g.scorePartition p e route (g.decoratedLabelSlot p e u) = true := by
  simp [scorePartition, decoratedLabelSlot, hu]

/-- Score gets precisely its nonempty derivative group; operand keeps all original
free slots and the complementary derivative group. Syntax order is independent of b. -/
theorem exists_score_orientation {j f : ℕ} (hg : g.Admissible)
    (e : g.Slot p ≃ (Fin j ⊕ Fin (f+1)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ scoreRoutes (List.finRange j)) :
    ∃ (part : g.Slot p → Bool) (b : Bool),
      (∃ q : g.InPort p, part (.inl q) = false) ∧
      (∃ q : g.OutPort p, part (.inr q) = true) ∧
      (g.replaceVertex p part).Admissible ∧
      (∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b) ∧
      (∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b) ∧
      (∀ u, part (g.adjointFreeSlot p e u) = !b) := by
  have hne := scoreRoutes_left_ne_nil (List.finRange j) route hr
  obtain ⟨u,hu⟩ : ∃ u, u ∈ route.1 := by
    cases h : route.1 with
    | nil => exact False.elim (hne h)
    | cons u J => exact ⟨u, by simp⟩
  obtain ⟨part,hpart,hi,ho,hg'⟩ := g.exists_oriented_replacement hg p
    (g.scorePartition p e route)
    ⟨g.decoratedLabelSlot p e u,g.scorePartition_scoreLabel p e route hr u hu⟩
    ⟨g.adjointFreeSlot p e 0,g.scorePartition_free p e route 0⟩
  rcases hpart with rfl | rfl
  · exact ⟨_,false,hi,ho,hg',g.scorePartition_scoreLabel p e route hr,
      g.scorePartition_operandLabel p e route,g.scorePartition_free p e route⟩
  · refine ⟨_,true,hi,ho,hg',?_,?_,?_⟩
    · intro v hv; simp [g.scorePartition_scoreLabel p e route hr v hv]
    · intro v hv; simp [g.scorePartition_operandLabel p e route v hv]
    · intro v; simp [g.scorePartition_free p e route v]
end AcceleratedLogConcave.Tensor.Ordered.Graph
