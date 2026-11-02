import AcceleratedLogConcave.Tensor.LabeledOperatorLeibniz
import Mathlib.Data.Finset.Powerset

/-!

-/
noncomputable section
set_option autoImplicit false
open Function
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.InverseFlow
open LabeledOperatorLeibniz

/-- The unique assignment putting every derivative on the left. -/
def fullLeft : (n : ℕ) → Split n
  | 0 => ()
  | n+1 => .inl (fullLeft n)

@[simp] theorem fullLeft_leftCount (n : ℕ) : leftCount (fullLeft n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fullLeft,leftCount,ih]

@[simp] theorem fullLeft_rightCount (n : ℕ) : rightCount (fullLeft n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

 theorem fullLeft_encode (n : ℕ) (i : Fin n) : encode (fullLeft n) i = true := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih j

 theorem subsetEquiv_fullLeft (n : ℕ) : subsetEquiv n (fullLeft n) = Finset.univ := by
  ext i
  simp [subsetEquiv,fullLeft_encode]

 theorem subsetEquiv_symm_univ (n : ℕ) : (subsetEquiv n).symm Finset.univ = fullLeft n := by
  rw [← subsetEquiv_fullLeft n,Equiv.symm_apply_apply]

 theorem fullLeft_leftEmb_val (n : ℕ) (i : Fin (leftCount (fullLeft n))) :
    (leftEmb (fullLeft n) i).val = i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    change (Fin.cases (motive := fun _ => Fin (n+1)) 0
      (fun j : Fin (leftCount (fullLeft n)) => (leftEmb (fullLeft n) j).succ) i).val = i.val
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa only [Fin.cases_succ,Fin.val_succ] using congrArg (fun a : ℕ => a+1) (ih j)

 theorem fullLeft_leftEmb (n : ℕ) :
    leftEmb (fullLeft n) = Fin.cast (fullLeft_leftCount n) := by
  funext i
  apply Fin.ext
  exact fullLeft_leftEmb_val n i

/-- The two increasing lists concatenate bijectively onto the original labels.
This changes SLOT LABELS, not the numerical basis values assigned to them. -/
def splitLabelEquiv {n : ℕ} (s : Split n) :
    (Fin (leftCount s) ⊕ Fin (rightCount s)) ≃ Fin n :=
  Equiv.ofBijective (Sum.elim (leftEmb s) (rightEmb s)) (by
    constructor
    · intro a b hab
      rcases a with a | a <;> rcases b with b | b
      · exact congrArg Sum.inl ((left_strictMono s).injective hab)
      · have hl := (left_range s (leftEmb s a)).mp ⟨a,rfl⟩
        have hr := (right_range s (leftEmb s a)).mp ⟨b,hab.symm⟩
        exact False.elim (by rw [hl] at hr; cases hr)
      · have hl := (left_range s (rightEmb s a)).mp ⟨b,hab.symm⟩
        have hr := (right_range s (rightEmb s a)).mp ⟨a,rfl⟩
        exact False.elim (by rw [hl] at hr; cases hr)
      · exact congrArg Sum.inr ((right_strictMono s).injective hab)
    · intro i
      cases hi : encode s i with
      | false =>
        obtain ⟨j,hj⟩ := (right_range s i).mpr hi
        exact ⟨.inr j,hj⟩
      | true =>
        obtain ⟨j,hj⟩ := (left_range s i).mpr hi
        exact ⟨.inl j,hj⟩)

@[simp] theorem splitLabelEquiv_inl {n : ℕ} (s : Split n) (j : Fin (leftCount s)) :
    splitLabelEquiv s (.inl j) = leftEmb s j := rfl
@[simp] theorem splitLabelEquiv_inr {n : ℕ} (s : Split n) (j : Fin (rightCount s)) :
    splitLabelEquiv s (.inr j) = rightEmb s j := rfl

/-- Explicit associativity conversion: the path has slots (A+B)+(input+output),
while operatorCoeff has (derivatives+input)+output. -/
def inverseSubsetChart {n : ℕ} (S : Finset (Fin n)) :
    ((Fin (leftCount ((subsetEquiv n).symm S)) ⊕
      Fin (rightCount ((subsetEquiv n).symm S))) ⊕ (Unit ⊕ Unit)) ≃
    ((Fin n ⊕ Unit) ⊕ Unit) where
  toFun
    | .inl j => .inl (.inl (splitLabelEquiv ((subsetEquiv n).symm S) j))
    | .inr (.inl u) => .inl (.inr u)
    | .inr (.inr u) => .inr u
  invFun
    | .inl (.inl j) => .inl ((splitLabelEquiv ((subsetEquiv n).symm S)).symm j)
    | .inl (.inr u) => .inr (.inl u)
    | .inr u => .inr (.inr u)
  left_inv := by
    intro j
    rcases j with j | (u | u)
    · simp
    · rfl
    · rfl
  right_inv := by
    intro j
    rcases j with (j | u) | u
    · simp
    · rfl
    · rfl

abbrev properSubsets (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ

 theorem properSubset_card_lt {n : ℕ} {S : Finset (Fin n)} (hS : S ∈ properSubsets n) :
    S.card < n := by
  have hne : S ≠ Finset.univ := (Finset.mem_erase.mp hS).1
  have hstrict : S ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S,hne⟩
  simpa using Finset.card_lt_card hstrict

 theorem properSubset_left_lt {n : ℕ} {S : Finset (Fin n)} (hS : S ∈ properSubsets n) :
    leftCount ((subsetEquiv n).symm S) < n := by
  rw [subset_leftCount]
  exact properSubset_card_lt hS

 theorem properSubset_right_pos {n : ℕ} {S : Finset (Fin n)} (hS : S ∈ properSubsets n) :
    0 < rightCount ((subsetEquiv n).symm S) := by
  have hc := counts_add ((subsetEquiv n).symm S)
  have hl := properSubset_left_lt hS
  omega

/-- Exact fibers, hence binomial multiplicities. No quotient by repeated values. -/
theorem properSubset_card_fiber (n s : ℕ) (hs : s < n) :
    (properSubsets n).filter (fun S => S.card = s) =
      (Finset.univ : Finset (Fin n)).powersetCard s := by
  ext S
  simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,
    and_true,Finset.mem_powersetCard]
  constructor
  · exact fun h => ⟨Finset.subset_univ S,h.2⟩
  · intro h
    refine ⟨?_,h.2⟩
    intro he
    have : n = s := by simpa [he] using h.2
    omega

/-- Group the FULL labeled sum by cardinality, retaining exactly choose(n,s). -/
theorem properSubset_sum_card (n : ℕ) (f : ℕ → ℝ) :
    (∑ S ∈ properSubsets n, f S.card) =
      ∑ s ∈ Finset.range n, (n.choose s : ℝ)*f s := by
  have hm : ∀ S ∈ properSubsets n, S.card ∈ Finset.range n := by
    intro S hS
    exact Finset.mem_range.mpr (properSubset_card_lt hS)
  rw [← Finset.sum_fiberwise_of_maps_to' hm f]
  apply Finset.sum_congr rfl
  intro s hs
  rw [properSubset_card_fiber n s (Finset.mem_range.mp hs)]
  simp [Finset.card_powersetCard,nsmul_eq_mul]

end AcceleratedLogConcave.Tensor.InverseFlow
