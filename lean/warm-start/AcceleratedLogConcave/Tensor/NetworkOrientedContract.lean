import AcceleratedLogConcave.Tensor.NetworkFamily

/-! The parent slot equivalence determines the child partition; orientation is derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n D : ℕ} {Edge : Type*} [Fintype Edge]
variable (g : Graph n Edge) (p : Fin (n+1))

omit [Fintype Edge] in
def contractLeftSlot {r s : ℕ} (e : g.Slot p ≃ Fin (r+s+2)) (u : Fin (r+1)) : g.Slot p :=
  e.symm (Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.castAdd (s+1) u))

omit [Fintype Edge] in
def contractRightSlot {r s : ℕ} (e : g.Slot p ≃ Fin (r+s+2)) (u : Fin (s+1)) : g.Slot p :=
  e.symm (Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.natAdd (r+1) u))

omit [Fintype Edge] in
def contractPartition {r s : ℕ} (e : g.Slot p ≃ Fin (r+s+2)) (a : g.Slot p) : Bool :=
  decide (r+1 ≤ (e a).val)

omit [Fintype Edge] in
theorem contractPartition_left {r s : ℕ} (e : g.Slot p ≃ Fin (r+s+2)) (u : Fin (r+1)) :
    g.contractPartition p e (g.contractLeftSlot p e u) = false := by
  simp [contractPartition, contractLeftSlot, Nat.not_le.mpr u.isLt]

omit [Fintype Edge] in
theorem contractPartition_right {r s : ℕ} (e : g.Slot p ≃ Fin (r+s+2)) (u : Fin (s+1)) :
    g.contractPartition p e (g.contractRightSlot p e u) = true := by
  simp [contractPartition, contractRightSlot]

omit [Fintype Edge] in
/-- Every actual contract node has one of the two admissible child orientations. -/
theorem exists_contract_orientation {r s : ℕ} (hg : g.Admissible)
    (e : g.Slot p ≃ Fin (r+s+2)) :
    ∃ part : g.Slot p → Bool,
      (∃ q : g.InPort p, part (.inl q) = false) ∧
      (∃ q : g.OutPort p, part (.inr q) = true) ∧
      (g.replaceVertex p part).Admissible ∧
      ((∀ u, part (g.contractLeftSlot p e u) = false) ∧
        (∀ u, part (g.contractRightSlot p e u) = true) ∨
       (∀ u, part (g.contractLeftSlot p e u) = true) ∧
        (∀ u, part (g.contractRightSlot p e u) = false)) := by
  obtain ⟨part, hp, hi, ho, hg'⟩ := g.exists_oriented_replacement hg p (g.contractPartition p e)
    ⟨g.contractLeftSlot p e 0, g.contractPartition_left p e 0⟩
    ⟨g.contractRightSlot p e 0, g.contractPartition_right p e 0⟩
  refine ⟨part, hi, ho, hg', ?_⟩
  rcases hp with rfl | rfl
  · exact Or.inl ⟨g.contractPartition_left p e, g.contractPartition_right p e⟩
  · right
    constructor
    · intro u; simp [g.contractPartition_left p e u]
    · intro u; simp [g.contractPartition_right p e u]

theorem crossContract_children_value_reversed (part : g.Slot p → Bool)
    (hI : ∃ q : g.InPort p, part (.inl q) = false)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true) {r s : ℕ}
    (A : Coeff (Fin (r+2)) D) (B : Coeff (Fin (s+2)) D)
    (i : Fin (r+2)) (j : Fin (s+2)) (e : g.Slot p ≃ Fin (r+s+2))
    (la : Fin (r+1) → g.Slot p) (ra : Fin (s+1) → g.Slot p)
    (hla : ∀ u, part (la u) = true) (hra : ∀ u, part (ra u) = false)
    (hel : ∀ u, e (la u) = Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.castAdd (s+1) u))
    (her : ∀ u, e (ra u) = Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.natAdd (r+1) u))
    (c : Option Edge → Fin D) :
    crossContract D A B i j (fun z => Sum.elim
      (fun q : g.InPort p => c q.val) (fun q : g.OutPort p => c q.val) (e.symm z)) =
    ∑ k : Fin D,
      g.contractChildTensor p part hI hO true A i la hla (Sum.elim
        (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) *
      g.contractChildTensor p part hI hO false B j ra hra (Sum.elim
        (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) := by
  simp only [contractChildTensor_value]
  simp only [crossContract, WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg₂ (fun x y : ℝ => x*y)
  · apply congrArg (fun z => A z)
    congr 1
    funext u
    rw [← hel u, e.symm_apply_apply]
  · apply congrArg (fun z => B z)
    congr 1
    funext u
    rw [← her u, e.symm_apply_apply]


private theorem transportTensor_value (v w : Fin (n+1)) (h : v = w)
    (A : Coeff (g.Slot v) D) (c : Option Edge → Fin D) :
    (h ▸ A : Coeff (g.Slot w) D)
      (Sum.elim (fun q => c q.val) (fun q => c q.val)) =
    A (Sum.elim (fun q => c q.val) (fun q => c q.val)) := by
  subst w
  rfl

/-- A literal parent contraction has a complete evaluated, admissible two-child replacement.
Only slot placement/orientation and the parent's actual local tensor representation are inputs. -/
theorem exists_contract_replacement_reversed (part : g.Slot p → Bool) {r s : ℕ} (hg : g.Admissible)
    (hI : ∃ q : g.InPort p, part (.inl q) = false)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true)
    (T : g.Tensors D) (A : Coeff (Fin (r+2)) D) (B : Coeff (Fin (s+2)) D)
    (i : Fin (r+2)) (j : Fin (s+2)) (e : g.Slot p ≃ Fin (r+s+2))
    (la : Fin (r+1) → g.Slot p) (ra : Fin (s+1) → g.Slot p)
    (hla : ∀ u, part (la u) = true) (hra : ∀ u, part (ra u) = false)
    (hel : ∀ u, e (la u) = Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.castAdd (s+1) u))
    (her : ∀ u, e (ra u) = Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.natAdd (r+1) u))
    (hparent : ∀ a, T p a = crossContract D A B i j (a ∘ e.symm)) :
    ∃ U : (g.replaceVertex p part).Tensors D,
      (g.replaceVertex p part).Admissible ∧
      g.coordinateEval D T = (g.replaceVertex p part).coordinateEval D U := by
  let A₀ := g.contractChildTensor p part hI hO false B j ra hra
  let B₀ := g.contractChildTensor p part hI hO true A i la hla
  let A' : Coeff ((g.replaceVertex p part).Slot p.castSucc) D :=
    splitVertex_parent_false p ▸ A₀
  let B' : Coeff ((g.replaceVertex p part).Slot p.succ) D :=
    splitVertex_parent_true p ▸ B₀
  refine ⟨g.replacementFamily p part T A' B', g.replaceVertex_admissible hg p part hI hO, ?_⟩
  apply g.coordinateEval_replacementFamily p part T A' B'
  intro c
  have hh := g.crossContract_children_value_reversed p part hI hO A B i j e la ra hla hra hel her c
  unfold wireValue
  rw [hparent]
  simp only [Function.comp_def]
  rw [hh]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]
  apply congrArg₂ (fun x y : ℝ => x*y)
  · exact ((g.replaceVertex p part).transportTensor_value _ _
      (splitVertex_parent_false p) A₀ (extendAssignment c k)).symm
  · exact ((g.replaceVertex p part).transportTensor_value _ _
      (splitVertex_parent_true p) B₀ (extendAssignment c k)).symm

/-- No orientation or inherited-slot assignment is assumed: both are generated
from the actual parent's slot equivalence. -/
theorem exists_oriented_contract_replacement {r s : ℕ} (hg : g.Admissible)
    (T : g.Tensors D) (A : Coeff (Fin (r+2)) D) (B : Coeff (Fin (s+2)) D)
    (i : Fin (r+2)) (j : Fin (s+2)) (e : g.Slot p ≃ Fin (r+s+2))
    (hparent : ∀ a, T p a = crossContract D A B i j (a ∘ e.symm)) :
    ∃ part : g.Slot p → Bool, ∃ U : (g.replaceVertex p part).Tensors D,
      (g.replaceVertex p part).Admissible ∧
      g.coordinateEval D T = (g.replaceVertex p part).coordinateEval D U := by
  obtain ⟨part,hi,ho,hg',horient⟩ := g.exists_contract_orientation p hg e
  refine ⟨part, ?_⟩
  rcases horient with ⟨hla,hra⟩ | ⟨hla,hra⟩
  · exact g.exists_contract_replacement p part hg hi ho T A B i j e
      (g.contractLeftSlot p e) (g.contractRightSlot p e) hla hra
      (fun u => by simp [contractLeftSlot]) (fun u => by simp [contractRightSlot]) hparent
  · exact g.exists_contract_replacement_reversed p part hg hi ho T A B i j e
      (g.contractLeftSlot p e) (g.contractRightSlot p e) hla hra
      (fun u => by simp [contractLeftSlot]) (fun u => by simp [contractRightSlot]) hparent

end AcceleratedLogConcave.Tensor.Ordered.Graph
