import AcceleratedLogConcave.Tensor.NetworkSyntaxState

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

def erasePermutation (a : NodeAddress) : TaggedPending σ → TaggedPending σ
  | .formula b (.permute p E) J => .formula b (if a = b then E else .permute p E) J
  | p => p

/-- Child slots map to parent slots; ordered derivative ports are unchanged. -/
def erasePermutationPorts (a : NodeAddress) : (p : TaggedPending σ) →
    pendingPorts (erasePermutation a p) ≃ pendingPorts p
  | .formula b (.permute q _E) _J =>
      if a = b then Equiv.sumCongr (Equiv.refl _) q else Equiv.refl _
  | .formula _ (.coefficient _) _ => Equiv.refl _
  | .formula _ (.contract ..) _ => Equiv.refl _
  | .formula _ (.derivative _) _ => Equiv.refl _
  | .formula _ (.adjoint ..) _ => Equiv.refl _
  | .score .. => Equiv.refl _

 theorem erasePermutation_origin (a : NodeAddress) (p : TaggedPending σ)
    (u : pendingPorts (erasePermutation a p)) :
    pendingPortOrigin p (erasePermutationPorts a p u) =
      pendingPortOrigin (erasePermutation a p) u := by
  cases p with
  | score b J h => rfl
  | formula b E J =>
    cases E with
    | permute q E =>
      by_cases h : a = b
      · simp only [erasePermutationPorts, erasePermutation, h, ite_true]
        change (Fin J.length ⊕ _) at u
        cases u <;> rfl
      · simp only [erasePermutationPorts, erasePermutation, h, ite_false]
        cases u <;> rfl
    | coefficient c => rfl
    | contract E F i k => rfl
    | derivative E => rfl
    | adjoint i E => rfl

variable {D n : ℕ} {Edge : Type*} [Fintype Edge]
 theorem pendingTensor_erasePermutation (g : Graph n Edge) (v : Fin (n+1))
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (a : NodeAddress) (p : TaggedPending σ) (e : g.Slot v ≃ pendingPorts p)
    (x : EuclideanSpace ℝ (Fin D)) :
    g.pendingTensor v ρ H (erasePermutation a p)
      (e.trans (erasePermutationPorts a p).symm) x = g.pendingTensor v ρ H p e x := by
  cases p with
  | score b J h => rfl
  | formula b E J =>
    cases E with
    | permute q E =>
      by_cases h : a = b
      · simp only [erasePermutationPorts, erasePermutation, h, ite_true]
        change g.decoratedSectionTensor v ρ H (if a = b then E else .permute q E) _ x = _
        rw [ite_eq_left h]
        rfl
      · simp only [erasePermutationPorts, erasePermutation, h, ite_false]
        change g.decoratedSectionTensor v ρ H (if a = b then E else .permute q E) _ x = _
        rw [ite_eq_right h]
        rfl
    | coefficient c => rfl
    | contract E F i k => rfl
    | derivative E => rfl
    | adjoint i E => rfl

theorem erasePermutation_eq_self_of_tag_ne (a : NodeAddress) (p : TaggedPending σ)
    (hp : p.tag ≠ .formula a) : erasePermutation a p = p := by
  cases p with
  | score b J h => rfl
  | formula b E J =>
    cases E with
    | permute q E =>
      have hab : a ≠ b := by intro h; subst b; exact hp rfl
      simp only [erasePermutation, ite_eq_right hab]
    | coefficient c => rfl
    | contract E F i k => rfl
    | derivative E => rfl
    | adjoint i E => rfl

private theorem map_erasePermutation_fixed (a : NodeAddress) (s : List (TaggedPending σ))
    (h : ∀ p ∈ s, p.tag ≠ .formula a) : s.map (erasePermutation a) = s := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    rw [List.map_cons, erasePermutation_eq_self_of_tag_ne a p (h p (by simp))]
    rw [ih (by intro q hq; exact h q (by simp [hq]))]

/-- The mapped semantic state is the exact canonical permutation child, not an
unrelated simplification, whenever all other occurrence tags are distinct. -/
theorem map_erasePermutation_canonical {r : ℕ} (a : NodeAddress)
    (q : Equiv.Perm (Fin r)) (E : Expr σ r) (J : List LabelOrigin)
    (before after : List (TaggedPending σ))
    (h : ∀ p ∈ before ++ after, p.tag ≠ .formula a) :
    (before ++ [TaggedPending.formula a (.permute q E) J] ++ after).map (erasePermutation a) =
      before ++ [TaggedPending.formula a E J] ++ after := by
  rw [List.map_append, List.map_append]
  rw [map_erasePermutation_fixed a before (by intro p hp; exact h p (by simp [hp]))]
  rw [map_erasePermutation_fixed a after (by intro p hp; exact h p (by simp [hp]))]
  simp [erasePermutation]

namespace SyntaxState
variable {s : List (TaggedPending σ)} (S : SyntaxState s)

def erasePermutationAt (a : NodeAddress) : SyntaxState (s.map (erasePermutation a)) where
  n := S.n
  Edge := S.Edge
  edgeFintype := S.edgeFintype
  graph := S.graph
  admissible := S.admissible
  pending v := erasePermutation a (S.pending v)
  occurrence := (finCongr (List.length_map ..)).trans S.occurrence
  occurrence_spec := by
    intro i
    simp only [Equiv.trans_apply]
    rw [S.occurrence_spec]
    simp
  ports v := (S.ports v).trans (erasePermutationPorts a (S.pending v)).symm
  originWire := S.originWire
  origin_spec := by
    intro v u o h
    apply S.origin_spec
    change pendingPortOrigin (S.pending v) (erasePermutationPorts a (S.pending v) u) = some o
    rw [erasePermutation_origin]
    exact h

 theorem value_erasePermutationAt (a : NodeAddress) (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (x : EuclideanSpace ℝ (Fin D)) :
    (S.erasePermutationAt a).value ρ H x = S.value ρ H x := by
  let _ := S.edgeFintype
  unfold value
  congr 1
  funext v
  exact pendingTensor_erasePermutation S.graph v ρ H a (S.pending v) (S.ports v) x

end SyntaxState
end AcceleratedLogConcave.Tensor.Ordered.Graph
