import AcceleratedLogConcave.Tensor.NetworkOperandSlots
import AcceleratedLogConcave.Tensor.NetworkDecoratedChildren
import Mathlib.Data.List.NodupEquivFin

/-! Ordered derivative positions and surviving operand coordinates enumerate every
selected parent slot once; the fresh coordinate is the contracted operand slot. -/
noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))

/-- The enumeration retains list order, not merely membership in a finite set. -/
def selectedDecoratedEquiv {j r s : ℕ}
    (e : g.Slot p ≃ (Fin j ⊕ (Fin r ⊕ Fin s)))
    (A : List (Fin j)) (hA : A.Nodup) (part : g.Slot p → Bool) (b : Bool)
    (hlabel : ∀ u, part (e.symm (.inl u)) = b ↔ u ∈ A)
    (hleft : ∀ u, part (e.symm (.inr (.inl u))) = b)
    (hright : ∀ u, part (e.symm (.inr (.inr u))) = !b) :
    (Fin A.length ⊕ Fin r) ≃ {z : g.Slot p // part z = b} :=
  Equiv.ofBijective
    (fun z => match z with
      | .inl i => ⟨e.symm (.inl (A.get i)), (hlabel _).2 (List.get_mem ..)⟩
      | .inr u => ⟨e.symm (.inr (.inl u)), hleft u⟩) (by
    constructor
    · intro x y h
      have hh := congrArg e (congrArg Subtype.val h)
      cases x with
      | inl i =>
        cases y with
        | inl k =>
          have hi : A.get i = A.get k := by simpa using hh
          exact congrArg Sum.inl (hA.injective_get hi)
        | inr u => simp at hh
      | inr u =>
        cases y with
        | inl i => simp at hh
        | inr v =>
          have hu : u = v := by simpa using hh
          exact congrArg Sum.inr hu
    · intro z
      have hz : e.symm (e z.val) = z.val := e.symm_apply_apply z.val
      generalize hw : e z.val = w at hz
      cases w with
      | inl u =>
        have hu : u ∈ A := (hlabel u).1 (by rw [hz]; exact z.property)
        let i := (List.Nodup.getEquiv A hA).symm ⟨u,hu⟩
        have hi : A.get i = u := congrArg Subtype.val ((List.Nodup.getEquiv A hA).apply_symm_apply ⟨u,hu⟩)
        refine ⟨.inl i, Subtype.ext ?_⟩
        change e.symm (.inl (A.get i)) = z.val
        rw [hi, hz]
      | inr w =>
        cases w with
        | inl u => exact ⟨.inr u, Subtype.ext hz⟩
        | inr u =>
          have hh := hright u
          rw [hz, z.property] at hh
          cases b <;> cases hh)

variable (part : g.Slot p → Bool)
    (hI : ∃ q : g.InPort p, part (.inl q) = false)
    (hO : ∃ q : g.OutPort p, part (.inr q) = true)

/-- Full syntax slots: all ordered derivative positions, then all operand slots. -/
def decoratedOperandEquiv {a r : ℕ} (b : Bool) (i : Fin (r+2))
    (selected : (Fin a ⊕ Fin (r+1)) ≃ {z : g.Slot p // part z = b}) :
    (Fin a ⊕ Fin (r+2)) ≃ (g.replaceVertex p part).Slot (splitVertex p p b) :=
  (Equiv.sumCongr (Equiv.refl _) (finSuccEquiv' i)).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.optionEquivSumPUnit _)).trans
      ((Equiv.sumAssoc _ _ _).symm.trans
        ((Equiv.sumCongr selected (Equiv.refl Unit)).trans
          (g.childSlotEquiv p part hI hO b))))

 theorem decoratedOperandEquiv_derivative {a r : ℕ} (b : Bool) (i : Fin (r+2))
    (selected : (Fin a ⊕ Fin (r+1)) ≃ {z : g.Slot p // part z = b}) (u : Fin a) :
    g.decoratedOperandEquiv p part hI hO b i selected (.inl u) =
      g.inheritedChildSlot p part hI hO b (selected (.inl u)).val
        (selected (.inl u)).property := by
  rfl

 theorem decoratedOperandEquiv_joining {a r : ℕ} (b : Bool) (i : Fin (r+2))
    (selected : (Fin a ⊕ Fin (r+1)) ≃ {z : g.Slot p // part z = b}) :
    g.decoratedOperandEquiv p part hI hO b i selected (.inr i) =
      g.joiningChildSlot p part b := by
  simp [decoratedOperandEquiv]

 theorem decoratedOperandEquiv_inherited {a r : ℕ} (b : Bool) (i : Fin (r+2))
    (selected : (Fin a ⊕ Fin (r+1)) ≃ {z : g.Slot p // part z = b}) (u : Fin (r+1)) :
    g.decoratedOperandEquiv p part hI hO b i selected (.inr (i.succAbove u)) =
      g.inheritedChildSlot p part hI hO b (selected (.inr u)).val
        (selected (.inr u)).property := by
  simp only [decoratedOperandEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, finSuccEquiv'_succAbove, Equiv.optionEquivSumPUnit_some]
  exact g.childSlotEquiv_apply_inherited p part hI hO b _ _

/-- The normalized child is literally the syntax evaluator with these exact ports. -/
theorem decoratedOperandEquiv_tensor {D : ℕ} {Name : Type*}
    {σ : CoefficientSignature Name} [Fintype Edge] {a r : ℕ}
    (b : Bool) (i : Fin (r+2))
    (selected : (Fin a ⊕ Fin (r+1)) ≃ {z : g.Slot p // part z = b})
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (x : EuclideanSpace ℝ (Fin D)) :
    g.decoratedContractChildTensor p part hI hO b ρ H E i
      (fun u => (selected (.inr u)).val) (fun u => (selected (.inr u)).property)
      (fun u => (selected (.inl u)).val) (List.finRange a) x =
    (g.replaceVertex p part).decoratedSectionTensor (splitVertex p p b) ρ H E
      (g.decoratedOperandEquiv p part hI hO b i selected).symm x := by
  ext c
  unfold decoratedContractChildTensor decoratedSectionTensor
  change AdjointReduction.partialAlong _ _ _ x = AdjointReduction.partialAlong _ _ _ x
  have hd : g.childCoordinateDirection p part hI hO b
      (fun u => (selected (.inl u)).val) c =
      fun u => coordinateDirection D
        (c (g.decoratedOperandEquiv p part hI hO b i selected (.inl u))) := by
    funext u
    rw [decoratedOperandEquiv_derivative]
    exact dite_eq_left (selected (.inl u)).property
  have hf : Fin.insertNth i (c (g.joiningChildSlot p part b))
      (fun u => c (g.inheritedChildSlot p part hI hO b
        (selected (.inr u)).val (selected (.inr u)).property)) =
      fun u => c (g.decoratedOperandEquiv p part hI hO b i selected (.inr u)) := by
    apply Fin.insertNth_eq_iff.mpr
    constructor
    · simp [decoratedOperandEquiv_joining]
    · funext u
      simp [Fin.removeNth, decoratedOperandEquiv_inherited]
  rw [hd, hf]
  rfl

end AcceleratedLogConcave.Tensor.Ordered.Graph
