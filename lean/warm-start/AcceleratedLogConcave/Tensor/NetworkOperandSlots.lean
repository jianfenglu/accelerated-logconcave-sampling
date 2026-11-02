import AcceleratedLogConcave.Tensor.NetworkChildSlots
import AcceleratedLogConcave.Tensor.NetworkOrientedContract
import Mathlib.Logic.Equiv.Option

/-! Exact operand coordinates on a refined contraction child. -/
noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n D : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))

/-- The original slots are precisely the two surviving operand blocks. -/
def contractParentEquiv {r s : ℕ} (e : g.Slot p ≃ Fin (r+s+2)) :
    (Fin (r+1) ⊕ Fin (s+1)) ≃ g.Slot p :=
  finSumFinEquiv.trans ((finCongr (by omega)).trans e.symm)

theorem contractParentEquiv_left {r s : ℕ} (e : g.Slot p ≃ Fin (r+s+2))
    (u : Fin (r+1)) : g.contractParentEquiv p e (.inl u) = g.contractLeftSlot p e u := rfl

theorem contractParentEquiv_right {r s : ℕ} (e : g.Slot p ≃ Fin (r+s+2))
    (u : Fin (s+1)) : g.contractParentEquiv p e (.inr u) = g.contractRightSlot p e u := rfl

/-- Both possible graph orientations retain the exact left-operand slot set. -/
def contractLeftSelectedEquiv {r s : ℕ} (e : g.Slot p ≃ Fin (r+s+2))
    (part : g.Slot p → Bool) (b : Bool)
    (hl : ∀ u, part (g.contractLeftSlot p e u) = b)
    (hr : ∀ u, part (g.contractRightSlot p e u) = !b) :
    Fin (r+1) ≃ {a : g.Slot p // part a = b} :=
  Equiv.ofBijective (fun u => ⟨g.contractLeftSlot p e u, hl u⟩) (by
    constructor
    · intro u v h
      apply Sum.inl_injective
      apply (g.contractParentEquiv p e).injective
      exact congrArg Subtype.val h
    · intro a
      obtain ⟨z,hz⟩ := (g.contractParentEquiv p e).surjective a.val
      cases z with
      | inl u => exact ⟨u, Subtype.ext hz⟩
      | inr u =>
        have hh := a.property
        rw [← hz, contractParentEquiv_right, hr] at hh
        cases b <;> cases hh)

/-- Both possible graph orientations retain the exact right-operand slot set. -/
def contractRightSelectedEquiv {r s : ℕ} (e : g.Slot p ≃ Fin (r+s+2))
    (part : g.Slot p → Bool) (b : Bool)
    (hl : ∀ u, part (g.contractLeftSlot p e u) = !b)
    (hr : ∀ u, part (g.contractRightSlot p e u) = b) :
    Fin (s+1) ≃ {a : g.Slot p // part a = b} :=
  Equiv.ofBijective (fun u => ⟨g.contractRightSlot p e u, hr u⟩) (by
    constructor
    · intro u v h
      apply Sum.inr_injective
      apply (g.contractParentEquiv p e).injective
      exact congrArg Subtype.val h
    · intro a
      obtain ⟨z,hz⟩ := (g.contractParentEquiv p e).surjective a.val
      cases z with
      | inl u =>
        have hh := a.property
        rw [← hz, contractParentEquiv_left, hl] at hh
        cases b <;> cases hh
      | inr u => exact ⟨u, Subtype.ext hz⟩)

variable (part : g.Slot p → Bool)
    (hI : ∃ q : g.InPort p, part (.inl q) = false)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true)

/-- Insert the contracted coordinate into an exact enumeration of inherited slots. -/
def operandChildEquiv {r : ℕ} (b : Bool) (i : Fin (r+2))
    (a : Fin (r+1) ≃ {s : g.Slot p // part s = b}) :
    Fin (r+2) ≃ (g.replaceVertex p part).Slot (splitVertex p p b) :=
  (finSuccEquiv' i).trans ((Equiv.optionEquivSumPUnit _).trans
    ((Equiv.sumCongr a (Equiv.refl Unit)).trans (g.childSlotEquiv p part hI hO b)))

theorem operandChildEquiv_joining {r : ℕ} (b : Bool) (i : Fin (r+2))
    (a : Fin (r+1) ≃ {s : g.Slot p // part s = b}) :
    g.operandChildEquiv p part hI hO b i a i = g.joiningChildSlot p part b := by
  simp [operandChildEquiv]

theorem operandChildEquiv_inherited {r : ℕ} (b : Bool) (i : Fin (r+2))
    (a : Fin (r+1) ≃ {s : g.Slot p // part s = b}) (u : Fin (r+1)) :
    g.operandChildEquiv p part hI hO b i a (i.succAbove u) =
      g.inheritedChildSlot p part hI hO b (a u).val (a u).property := by
  simp only [operandChildEquiv, Equiv.trans_apply, finSuccEquiv'_succAbove,
    Equiv.optionEquivSumPUnit_some, Equiv.sumCongr_apply, Sum.map_inl]
  exact g.childSlotEquiv_apply_inherited p part hI hO b (a u).val (a u).property

/-- The previously constructed child tensor is literally its operand reindexed by this
bijection, not an extension with unused dimensions. -/
theorem contractChildTensor_eq_operand [Fintype Edge] {r : ℕ} (b : Bool) (A : Coeff (Fin (r+2)) D)
    (i : Fin (r+2)) (a : Fin (r+1) ≃ {s : g.Slot p // part s = b})
    (x : (g.replaceVertex p part).Slot (splitVertex p p b) → Fin D) :
    g.contractChildTensor p part hI hO b A i (fun u => (a u).val)
      (fun u => (a u).property) x =
    A (x ∘ g.operandChildEquiv p part hI hO b i a) := by
  unfold contractChildTensor
  apply congrArg (fun z => A z)
  apply (Fin.insertNth_eq_iff).mpr
  constructor
  · simp [operandChildEquiv_joining]
  · funext u
    simp [Fin.removeNth, operandChildEquiv_inherited]
end AcceleratedLogConcave.Tensor.Ordered.Graph
