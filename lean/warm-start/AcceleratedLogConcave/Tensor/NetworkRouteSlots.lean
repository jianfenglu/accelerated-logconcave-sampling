import AcceleratedLogConcave.Tensor.NetworkDecoratedSlotEquiv
import AcceleratedLogConcave.Tensor.NetworkDecoratedPartition
import AcceleratedLogConcave.Tensor.PolynomialClosure

/-! Canonical positional routes instantiate exact child-slot enumeration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))

def decoratedParentBlocks {r s j : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2))) :
    g.Slot p ≃ (Fin j ⊕ (Fin (r+1) ⊕ Fin (s+1))) :=
  e.trans (Equiv.sumCongr (Equiv.refl _)
    ((finCongr (by omega : r+s+2 = (r+1)+(s+1))).trans finSumFinEquiv.symm))

theorem route_left_flag_iff {j : ℕ} (route : List (Fin j) × List (Fin j))
    (hr : route ∈ routes (List.finRange j)) (flag : Fin j → Bool) (b : Bool)
    (hl : ∀ u ∈ route.1, flag u = b) (hright : ∀ u ∈ route.2, flag u = !b)
    (u : Fin j) : flag u = b ↔ u ∈ route.1 := by
  constructor
  · intro h
    have hm : u ∈ route.1 ++ route.2 := (route_perm _ route hr).mem_iff.mpr (List.mem_finRange u)
    rcases List.mem_append.mp hm with hA | hB
    · exact hA
    · have hb := h.symm.trans (hright u hB)
      cases b <;> cases hb
  · exact hl u

def routeLeftSelected {r s j : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ routes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hlf : ∀ u, part (g.decoratedLeftFreeSlot p e u) = b)
    (hrf : ∀ u, part (g.decoratedRightFreeSlot p e u) = !b)
    (hll : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hrl : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b) :
    (Fin route.1.length ⊕ Fin (r+1)) ≃ {z : g.Slot p // part z = b} :=
  g.selectedDecoratedEquiv p (g.decoratedParentBlocks p e) route.1
    ((List.nodup_append.mp ((route_perm _ route hr).nodup_iff.mpr (List.nodup_finRange j))).1)
    part b (fun u => route_left_flag_iff route hr _ b hll hrl u) hlf hrf

 theorem routeLeftSelected_derivative {r s j : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ routes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hlf : ∀ u, part (g.decoratedLeftFreeSlot p e u) = b)
    (hrf : ∀ u, part (g.decoratedRightFreeSlot p e u) = !b)
    (hll : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hrl : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (u : Fin route.1.length) :
    (g.routeLeftSelected p e route hr part b hlf hrf hll hrl (.inl u)).val =
      g.decoratedLabelSlot p e (route.1.get u) := rfl

 theorem routeLeftSelected_free {r s j : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ routes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hlf : ∀ u, part (g.decoratedLeftFreeSlot p e u) = b)
    (hrf : ∀ u, part (g.decoratedRightFreeSlot p e u) = !b)
    (hll : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hrl : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b) (u : Fin (r+1)) :
    (g.routeLeftSelected p e route hr part b hlf hrf hll hrl (.inr u)).val =
      g.decoratedLeftFreeSlot p e u := rfl

def routeRightSelected {r s j : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ routes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hlf : ∀ u, part (g.decoratedLeftFreeSlot p e u) = b)
    (hrf : ∀ u, part (g.decoratedRightFreeSlot p e u) = !b)
    (hll : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hrl : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b) :
    (Fin route.2.length ⊕ Fin (s+1)) ≃ {z : g.Slot p // part z = !b} :=
  g.selectedDecoratedEquiv p
    ((g.decoratedParentBlocks p e).trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _))) route.2
    ((List.nodup_append.mp ((route_perm _ route hr).nodup_iff.mpr (List.nodup_finRange j))).2.1)
    part (!b) (by
      intro u
      constructor
      · intro h
        have hm : u ∈ route.1 ++ route.2 := (route_perm _ route hr).mem_iff.mpr (List.mem_finRange u)
        rcases List.mem_append.mp hm with hA | hB
        · have hb := h.symm.trans (hll u hA)
          cases b <;> cases hb
        · exact hB
      · exact hrl u) hrf (by
        intro u
        rw [Bool.not_not]
        change part (g.decoratedLeftFreeSlot p e u) = b
        exact hlf u)

 theorem routeRightSelected_derivative {r s j : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ routes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hlf : ∀ u, part (g.decoratedLeftFreeSlot p e u) = b)
    (hrf : ∀ u, part (g.decoratedRightFreeSlot p e u) = !b)
    (hll : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hrl : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (u : Fin route.2.length) :
    (g.routeRightSelected p e route hr part b hlf hrf hll hrl (.inl u)).val =
      g.decoratedLabelSlot p e (route.2.get u) := rfl

 theorem routeRightSelected_free {r s j : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ routes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hlf : ∀ u, part (g.decoratedLeftFreeSlot p e u) = b)
    (hrf : ∀ u, part (g.decoratedRightFreeSlot p e u) = !b)
    (hll : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hrl : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b) (u : Fin (s+1)) :
    (g.routeRightSelected p e route hr part b hlf hrf hll hrl (.inr u)).val =
      g.decoratedRightFreeSlot p e u := rfl

/-- Reindex ordered derivatives by list positions without losing repeated values. -/
theorem partialAlong_list_positions {V L : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : L → V) (J : List L) (f : V → ℝ) :
    partialAlong d J f = partialAlong (fun i => d (J.get i)) (List.finRange J.length) f := by
  conv_lhs => rw [PolynomialClosure.partialAlong_map_id]
  conv_rhs => rw [PolynomialClosure.partialAlong_map_id]
  congr 1
  rw [← List.ofFn_eq_map, List.ofFn_comp', List.ofFn_get]

theorem routeLeft_child_tensor {D : ℕ} {Name : Type*}
    {σ : CoefficientSignature Name} [Fintype Edge] {r s j : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ routes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hi : ∃ q : g.InPort p, part (.inl q) = false)
    (ho : ∃ q : g.OutPort p, part (.inr q) = true)
    (hlf : ∀ u, part (g.decoratedLeftFreeSlot p e u) = b)
    (hrf : ∀ u, part (g.decoratedRightFreeSlot p e u) = !b)
    (hll : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hrl : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (i : Fin (r+2)) (x : EuclideanSpace ℝ (Fin D)) :
    g.decoratedContractChildTensor p part hi ho b ρ H E i
      (g.decoratedLeftFreeSlot p e) hlf (g.decoratedLabelSlot p e) route.1 x =
    (g.replaceVertex p part).decoratedSectionTensor (splitVertex p p b) ρ H E
      (g.decoratedOperandEquiv p part hi ho b i
        (g.routeLeftSelected p e route hr part b hlf hrf hll hrl)).symm x := by
  let selected := g.routeLeftSelected p e route hr part b hlf hrf hll hrl
  calc
    _ = g.decoratedContractChildTensor p part hi ho b ρ H E i
        (fun u => (selected (.inr u)).val) (fun u => (selected (.inr u)).property)
        (fun u => (selected (.inl u)).val) (List.finRange route.1.length) x := by
      ext c
      unfold decoratedContractChildTensor
      dsimp only
      rw [partialAlong_list_positions]
      rfl
    _ = _ := g.decoratedOperandEquiv_tensor p part hi ho b i selected ρ H E x

theorem routeRight_child_tensor {D : ℕ} {Name : Type*}
    {σ : CoefficientSignature Name} [Fintype Edge] {r s j : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ routes (List.finRange j))
    (part : g.Slot p → Bool) (b : Bool)
    (hi : ∃ q : g.InPort p, part (.inl q) = false)
    (ho : ∃ q : g.OutPort p, part (.inr q) = true)
    (hlf : ∀ u, part (g.decoratedLeftFreeSlot p e u) = b)
    (hrf : ∀ u, part (g.decoratedRightFreeSlot p e u) = !b)
    (hll : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hrl : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (s+2)) (i : Fin (s+2)) (x : EuclideanSpace ℝ (Fin D)) :
    g.decoratedContractChildTensor p part hi ho (!b) ρ H E i
      (g.decoratedRightFreeSlot p e) hrf (g.decoratedLabelSlot p e) route.2 x =
    (g.replaceVertex p part).decoratedSectionTensor (splitVertex p p (!b)) ρ H E
      (g.decoratedOperandEquiv p part hi ho (!b) i
        (g.routeRightSelected p e route hr part b hlf hrf hll hrl)).symm x := by
  let selected := g.routeRightSelected p e route hr part b hlf hrf hll hrl
  calc
    _ = g.decoratedContractChildTensor p part hi ho (!b) ρ H E i
        (fun u => (selected (.inr u)).val) (fun u => (selected (.inr u)).property)
        (fun u => (selected (.inl u)).val) (List.finRange route.2.length) x := by
      ext c
      unfold decoratedContractChildTensor
      dsimp only
      rw [partialAlong_list_positions]
      rfl
    _ = _ := g.decoratedOperandEquiv_tensor p part hi ho (!b) i selected ρ H E x

end AcceleratedLogConcave.Tensor.Ordered.Graph
