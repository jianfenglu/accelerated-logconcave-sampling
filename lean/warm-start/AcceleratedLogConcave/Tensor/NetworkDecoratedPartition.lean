import AcceleratedLogConcave.Tensor.NetworkDecoratedChildren
import AcceleratedLogConcave.Tensor.NetworkFamily

/-! Actual positional derivative routing determines every replacement port. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction
variable {n D : ℕ} {Edge Name : Type*} [Fintype Edge] {σ : CoefficientSignature Name}
variable (g : Graph n Edge) (p : Fin (n+1))

omit [Fintype Edge] in
def decoratedLabelSlot {j f : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin f)) (u : Fin j) :
    g.Slot p := e.symm (.inl u)

omit [Fintype Edge] in
def decoratedLeftFreeSlot {r s j : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (u : Fin (r+1)) : g.Slot p :=
  e.symm (.inr (Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.castAdd (s+1) u)))

omit [Fintype Edge] in
def decoratedRightFreeSlot {r s j : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (u : Fin (s+1)) : g.Slot p :=
  e.symm (.inr (Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.natAdd (r+1) u)))

omit [Fintype Edge] in
def decoratedPartition {r s j : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (a : g.Slot p) : Bool :=
  match e a with
  | .inl u => decide (u ∈ route.2)
  | .inr u => decide (r+1 ≤ u.val)

omit [Fintype Edge] in
theorem decoratedPartition_leftFree {r s j : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (u : Fin (r+1)) :
    g.decoratedPartition p e route (g.decoratedLeftFreeSlot p e u) = false := by
  simp [decoratedPartition, decoratedLeftFreeSlot, Nat.not_le.mpr u.isLt]

omit [Fintype Edge] in
theorem decoratedPartition_rightFree {r s j : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (u : Fin (s+1)) :
    g.decoratedPartition p e route (g.decoratedRightFreeSlot p e u) = true := by
  simp [decoratedPartition, decoratedRightFreeSlot]

omit [Fintype Edge] in
theorem decoratedPartition_leftLabel {r s j : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (hr : route ∈ routes (List.finRange j))
    (u : Fin j) (hu : u ∈ route.1) :
    g.decoratedPartition p e route (g.decoratedLabelSlot p e u) = false := by
  have hn : (route.1 ++ route.2).Nodup :=
    (route_perm (List.finRange j) route hr).nodup_iff.mpr (List.nodup_finRange j)
  have hd := List.disjoint_of_nodup_append hn
  have hu' : u ∉ route.2 := (List.disjoint_left.mp hd) hu
  simp [decoratedPartition, decoratedLabelSlot, hu']

omit [Fintype Edge] in
theorem decoratedPartition_rightLabel {r s j : ℕ} (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2)))
    (route : List (Fin j) × List (Fin j)) (u : Fin j) (hu : u ∈ route.2) :
    g.decoratedPartition p e route (g.decoratedLabelSlot p e u) = true := by
  simp [decoratedPartition, decoratedLabelSlot, hu]

omit [Fintype Edge] in
/-- Routing labels does not require freezing any derivative coordinate; either child order
can be used while the same exact free and derivative port groups are retained. -/
theorem exists_decorated_orientation {r s j : ℕ} (hg : g.Admissible)
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2))) (route : List (Fin j) × List (Fin j))
    (hr : route ∈ routes (List.finRange j)) :
    ∃ (part : g.Slot p → Bool) (b : Bool),
      (∃ q : g.InPort p, part (.inl q) = false) ∧
      (∃ q : g.OutPort p, part (.inr q) = true) ∧
      (g.replaceVertex p part).Admissible ∧
      (∀ u, part (g.decoratedLeftFreeSlot p e u) = b) ∧
      (∀ u, part (g.decoratedRightFreeSlot p e u) = !b) ∧
      (∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b) ∧
      (∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b) := by
  obtain ⟨part,hpart,hi,ho,hg'⟩ := g.exists_oriented_replacement hg p
    (g.decoratedPartition p e route)
    ⟨g.decoratedLeftFreeSlot p e 0, g.decoratedPartition_leftFree p e route 0⟩
    ⟨g.decoratedRightFreeSlot p e 0, g.decoratedPartition_rightFree p e route 0⟩
  rcases hpart with rfl | rfl
  · exact ⟨_, false, hi, ho, hg', g.decoratedPartition_leftFree p e route,
      g.decoratedPartition_rightFree p e route, g.decoratedPartition_leftLabel p e route hr,
      g.decoratedPartition_rightLabel p e route⟩
  · refine ⟨_, true, hi, ho, hg', ?_, ?_, ?_, ?_⟩
    · intro u; simp [g.decoratedPartition_leftFree p e route u]
    · intro u; simp [g.decoratedPartition_rightFree p e route u]
    · intro u hu; simp [g.decoratedPartition_leftLabel p e route hr u hu]
    · intro u hu; simp [g.decoratedPartition_rightLabel p e route u hu]

/-- A positional route tensor is exactly the contraction of its actual decorated children. -/
theorem decoratedRoute_children_value {r s j : ℕ} (part : g.Slot p → Bool)
    (hI : ∃ q : g.InPort p, part (.inl q) = false)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true) (b : Bool)
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (F : Expr σ (s+2)) (i : Fin (r+2)) (k : Fin (s+2))
    (e : g.Slot p ≃ (Fin j ⊕ Fin (r+s+2))) (route : List (Fin j) × List (Fin j))
    (hlf : ∀ u, part (g.decoratedLeftFreeSlot p e u) = b)
    (hrf : ∀ u, part (g.decoratedRightFreeSlot p e u) = !b)
    (hll : ∀ u ∈ route.1, part (g.decoratedLabelSlot p e u) = b)
    (hrl : ∀ u ∈ route.2, part (g.decoratedLabelSlot p e u) = !b)
    (x : EuclideanSpace ℝ (Fin D)) (c : Option Edge → Fin D) :
    g.decoratedContractRouteTensor p ρ H E F i k e route x
      (Sum.elim (fun q => c q.val) (fun q => c q.val)) = ∑ v : Fin D,
    g.decoratedContractChildTensor p part hI hO b ρ H E i
      (g.decoratedLeftFreeSlot p e) hlf (g.decoratedLabelSlot p e) route.1 x
      (Sum.elim (fun q => extendAssignment c v q.val) (fun q => extendAssignment c v q.val)) *
    g.decoratedContractChildTensor p part hI hO (!b) ρ H F k
      (g.decoratedRightFreeSlot p e) hrf (g.decoratedLabelSlot p e) route.2 x
      (Sum.elim (fun q => extendAssignment c v q.val) (fun q => extendAssignment c v q.val)) := by
  simp_rw [g.decoratedContractChildTensor_value p part hI hO b ρ H E i
    (g.decoratedLeftFreeSlot p e) hlf (g.decoratedLabelSlot p e) route.1 hll]
  simp_rw [g.decoratedContractChildTensor_value p part hI hO (!b) ρ H F k
    (g.decoratedRightFreeSlot p e) hrf (g.decoratedLabelSlot p e) route.2 hrl]
  rfl
end AcceleratedLogConcave.Tensor.Ordered.Graph
