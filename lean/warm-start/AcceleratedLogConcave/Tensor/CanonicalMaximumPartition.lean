import AcceleratedLogConcave.Tensor.FinitePartitionFibers
import Mathlib.Data.Finset.Sort

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.FlowInduction

abbrev LabeledSurjection (n k : ℕ) :=
  {f : Fin n → Fin k // Function.Surjective f}

/-- Nonempty freely labeled blocks are the actual fibers, not size profiles. -/
def surjectionFiber {n k : ℕ} (f : LabeledSurjection n k) (i : Fin k) : Finset (Fin n) :=
  Finset.univ.filter (fun x => f.val x = i)

@[simp] theorem mem_surjectionFiber {n k : ℕ} (f : LabeledSurjection n k)
    (i : Fin k) (x : Fin n) : x ∈ surjectionFiber f i ↔ f.val x = i := by
  simp [surjectionFiber]

theorem surjectionFiber_nonempty {n k : ℕ} (f : LabeledSurjection n k) (i : Fin k) :
    (surjectionFiber f i).Nonempty := by
  obtain ⟨x,hx⟩ := f.property i
  exact ⟨x, (mem_surjectionFiber f i x).mpr hx⟩

def surjectionMaximum {n k : ℕ} (f : LabeledSurjection n k) (i : Fin k) : Fin n :=
  (surjectionFiber f i).max' (surjectionFiber_nonempty f i)

@[simp] theorem surjectionMaximum_label {n k : ℕ} (f : LabeledSurjection n k)
    (i : Fin k) : f.val (surjectionMaximum f i) = i := by
  apply (mem_surjectionFiber f i _).mp
  exact Finset.max'_mem _ _

theorem surjectionMaximum_injective {n k : ℕ} (f : LabeledSurjection n k) :
    Function.Injective (surjectionMaximum f) := by
  intro i j h
  have := congrArg f.val h
  simpa using this

def surjectionMaxima {n k : ℕ} (f : LabeledSurjection n k) : Finset (Fin n) :=
  Finset.univ.image (surjectionMaximum f)

theorem surjectionMaxima_card {n k : ℕ} (f : LabeledSurjection n k) :
    (surjectionMaxima f).card = k := by
  rw [surjectionMaxima, Finset.card_image_of_injective _ (surjectionMaximum_injective f)]
  simp

/-- Labels are in bijection with their distinct maxima. -/
def labelMaximumEquiv {n k : ℕ} (f : LabeledSurjection n k) :
    Fin k ≃ {x // x ∈ surjectionMaxima f} :=
  Equiv.ofBijective (fun i => ⟨surjectionMaximum f i, by simp [surjectionMaxima]⟩) (by
    constructor
    · intro i j h
      exact surjectionMaximum_injective f (congrArg Subtype.val h)
    · intro x
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
      exact ⟨i, Subtype.ext hi⟩)

/-- Canonical position -> original block label; sorting occurs only here. -/
def maximumSortingPermutation {n k : ℕ} (f : LabeledSurjection n k) : Equiv.Perm (Fin k) :=
  ((surjectionMaxima f).orderIsoOfFin (surjectionMaxima_card f)).toEquiv.trans
    (labelMaximumEquiv f).symm

theorem maximumSortingPermutation_value {n k : ℕ} (f : LabeledSurjection n k)
    (i : Fin k) :
    surjectionMaximum f (maximumSortingPermutation f i) =
      (surjectionMaxima f).orderEmbOfFin (surjectionMaxima_card f) i := by
  have h := (labelMaximumEquiv f).apply_symm_apply
    ((surjectionMaxima f).orderIsoOfFin (surjectionMaxima_card f) i)
  exact congrArg Subtype.val h

theorem maximumSortingPermutation_strictMono {n k : ℕ} (f : LabeledSurjection n k) :
    StrictMono (fun i => surjectionMaximum f (maximumSortingPermutation f i)) := by
  intro i j hij
  simp_rw [maximumSortingPermutation_value]
  exact ((surjectionMaxima f).orderEmbOfFin (surjectionMaxima_card f)).strictMono hij

/-- Canonical literal partition reconstructed by increasingly enumerating each fiber,
with fibers ordered by increasing MAXIMUM, exactly as the pinned structure requires. -/
def canonicalMaximumPartition {n k : ℕ} (f : LabeledSurjection n k) :
    OrderedFinpartition n where
  length := k
  partSize i := (surjectionFiber f (maximumSortingPermutation f i)).card
  partSize_pos i := Finset.card_pos.mpr (surjectionFiber_nonempty f _)
  emb i := (surjectionFiber f (maximumSortingPermutation f i)).orderEmbOfFin rfl
  emb_strictMono i := ((surjectionFiber f (maximumSortingPermutation f i)).orderEmbOfFin rfl).strictMono
  parts_strictMono := by
    have hlast (i : Fin k) :
        (surjectionFiber f (maximumSortingPermutation f i)).orderEmbOfFin rfl
          ⟨(surjectionFiber f (maximumSortingPermutation f i)).card - 1,
            Nat.sub_one_lt_of_lt (Finset.card_pos.mpr (surjectionFiber_nonempty f _))⟩ =
          surjectionMaximum f (maximumSortingPermutation f i) := by
      exact Finset.orderEmbOfFin_last rfl (Finset.card_pos.mpr (surjectionFiber_nonempty f _))
    simpa only [hlast] using maximumSortingPermutation_strictMono f
  disjoint := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha⟩ ⟨b,hb⟩
    have hi := (mem_surjectionFiber f (maximumSortingPermutation f i) x).mp
      (ha ▸ Finset.orderEmbOfFin_mem _ rfl a)
    have hj := (mem_surjectionFiber f (maximumSortingPermutation f j) x).mp
      (hb ▸ Finset.orderEmbOfFin_mem _ rfl b)
    exact hij ((maximumSortingPermutation f).injective (hi.symm.trans hj))
  cover x := by
    let i := (maximumSortingPermutation f).symm (f.val x)
    have hx : x ∈ surjectionFiber f (maximumSortingPermutation f i) := by simp [i]
    refine ⟨i, ?_⟩
    rw [Finset.range_orderEmbOfFin]
    exact hx

/-- Recovering a block index after its increasing embedding. -/
@[simp] theorem partition_index_emb {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) (r : Fin (c.partSize i)) : c.index (c.emb i r) = i := by
  exact congrArg Sigma.fst (c.equivSigma.left_inv ⟨i,r⟩)

theorem partition_index_surjective {n : ℕ} (c : OrderedFinpartition n) :
    Function.Surjective c.index := by
  intro i
  exact ⟨c.emb i ⟨0,c.partSize_pos i⟩, partition_index_emb c i _⟩

theorem partition_index_iff {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) (x : Fin n) : c.index x = i ↔ x ∈ Set.range (c.emb i) := by
  constructor
  · intro h
    have hx : x ∈ Set.range (c.emb (c.index x)) := ⟨c.invEmbedding x, c.emb_invEmbedding x⟩
    exact h ▸ hx
  · rintro ⟨r,rfl⟩
    exact partition_index_emb c i r

/-- The constructed partition retains every original label. -/
theorem canonicalMaximumPartition_label {n k : ℕ} (f : LabeledSurjection n k)
    (x : Fin n) :
    maximumSortingPermutation f ((canonicalMaximumPartition f).index x) = f.val x := by
  let c := canonicalMaximumPartition f
  have hx := c.emb_invEmbedding x
  have hm : c.emb (c.index x) (c.invEmbedding x) ∈
      surjectionFiber f (maximumSortingPermutation f (c.index x)) :=
    Finset.orderEmbOfFin_mem _ rfl _
  rw [hx] at hm
  exact ((mem_surjectionFiber f _ x).mp hm).symm

/-- Decorate a literal partition by a bijection from its block positions to labels.
This avoids hiding length casts; at length k the decoration has exactly k! choices. -/
abbrev DecoratedPartition (n k : ℕ) := Σ c : OrderedFinpartition n, Fin c.length ≃ Fin k

def decoratedPartitionSurjection {n k : ℕ} (d : DecoratedPartition n k) :
    LabeledSurjection n k :=
  ⟨fun x => d.2 (d.1.index x), d.2.surjective.comp (partition_index_surjective d.1)⟩

def surjectionDecoratedPartition {n k : ℕ} (f : LabeledSurjection n k) :
    DecoratedPartition n k := ⟨canonicalMaximumPartition f, maximumSortingPermutation f⟩

theorem surjectionDecoratedPartition_right_inverse {n k : ℕ} :
    Function.RightInverse (surjectionDecoratedPartition (n := n) (k := k))
      decoratedPartitionSurjection := by
  intro f
  apply Subtype.ext
  funext x
  exact canonicalMaximumPartition_label f x

/-- The greatest actual element in a canonical block. -/
def partitionMaximum {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) : Fin n :=
  c.emb i ⟨c.partSize i - 1, Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩

theorem partition_le_maximum {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) (x : Fin n) (hx : c.index x = i) : x ≤ partitionMaximum c i := by
  obtain ⟨r,rfl⟩ := (partition_index_iff c i x).mp hx
  apply (c.emb_strictMono i).monotone
  apply Fin.le_iff_val_le_val.mpr
  exact Nat.le_sub_one_of_lt r.isLt

/-- A label-preserving relabeling necessarily preserves actual block maxima. -/
theorem partitionMaximum_relabel {n : ℕ} (c d : OrderedFinpartition n)
    (e : Fin c.length ≃ Fin d.length)
    (h : ∀ x, e (c.index x) = d.index x) (i : Fin c.length) :
    partitionMaximum c i = partitionMaximum d (e i) := by
  apply le_antisymm
  · apply partition_le_maximum d (e i)
    rw [← h, partitionMaximum, partition_index_emb]
  · apply partition_le_maximum c i
    apply e.injective
    rw [h, partitionMaximum, partition_index_emb]

/-- The maxima convention forces every block relabeling between canonical
representations to be order preserving. This is false for arbitrary size profiles. -/
theorem partition_relabel_strictMono {n : ℕ} (c d : OrderedFinpartition n)
    (e : Fin c.length ≃ Fin d.length)
    (h : ∀ x, e (c.index x) = d.index x) : StrictMono e := by
  intro i j hij
  have hm : partitionMaximum c i < partitionMaximum c j := c.parts_strictMono hij
  rw [partitionMaximum_relabel c d e h i, partitionMaximum_relabel c d e h j] at hm
  exact d.parts_strictMono.lt_iff_lt.mp hm

/-- Literal uniqueness, including increasing within-block embeddings.
Proof fields add no multiplicity. -/
theorem partition_eq_of_relabeling {n : ℕ} (c d : OrderedFinpartition n)
    (e : Fin c.length ≃ Fin d.length)
    (h : ∀ x, e (c.index x) = d.index x) : c = d := by
  have hlen : c.length = d.length := by
    simpa using Fintype.card_congr e
  have hmono := partition_relabel_strictMono c d e h
  rcases c with ⟨l,p,hp,a,ha,hm,hd,hcover⟩
  rcases d with ⟨l',q,hq,b,hb,hm',hd',hcover'⟩
  dsimp at hlen e hmono
  subst l'
  have he : ∀ i, e i = i := by
    have h₁ := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin l)))
      (by simp) (f := fun i => e i) (fun _ => Finset.mem_univ _) hmono
    have h₂ := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin l)))
      (by simp) (f := fun i : Fin l => i) (fun _ => Finset.mem_univ _) strictMono_id
    exact congrFun (h₁.trans h₂.symm)
  let c₀ : OrderedFinpartition n := ⟨l,p,hp,a,ha,hm,hd,hcover⟩
  let d₀ : OrderedFinpartition n := ⟨l,q,hq,b,hb,hm',hd',hcover'⟩
  have hr (i : Fin l) : Set.range (a i) = Set.range (b i) := by
    ext x
    rw [← partition_index_iff c₀ i x, ← partition_index_iff d₀ i x]
    have hx := h x
    rw [he] at hx
    rw [hx]
  have hpq : p = q := by
    funext i
    have hc : Fintype.card (Set.range (a i)) = Fintype.card (Set.range (b i)) :=
      Fintype.card_congr (Set.equivOfEq (hr i))
    rw [Set.card_range_of_injective (ha i).injective,
      Set.card_range_of_injective (hb i).injective] at hc
    simpa using hc
  subst q
  have hab : a = b := by
    funext i
    exact ((ha i).range_inj_of_wellFoundedLT (hb i)).mp (hr i)
  subst b
  rfl

/-- Canonical partitions plus bijective block labels have no duplicates. -/
theorem decoratedPartitionSurjection_injective {n k : ℕ} :
    Function.Injective (decoratedPartitionSurjection (n := n) (k := k)) := by
  rintro ⟨c,e⟩ ⟨d,g⟩ h
  have hx : ∀ x, e (c.index x) = g (d.index x) := by
    intro x
    exact congrFun (congrArg Subtype.val h) x
  have hcd : c = d := partition_eq_of_relabeling c d (e.trans g.symm) (by
    intro x
    change g.symm (e (c.index x)) = d.index x
    rw [hx, g.symm_apply_apply])
  subst d
  have heg : e = g := by
    apply Equiv.ext
    intro i
    obtain ⟨x,rfl⟩ := partition_index_surjective c i
    exact hx x
  subst g
  rfl

/-- The requested canonical-MAXIMUM partition/surjection equivalence.
No counting identity, recurrence, or mass estimate is a premise. -/
def canonicalMaximumSurjectionEquiv (n k : ℕ) :
    DecoratedPartition n k ≃ LabeledSurjection n k where
  toFun := decoratedPartitionSurjection
  invFun := surjectionDecoratedPartition
  left_inv d := decoratedPartitionSurjection_injective
    (surjectionDecoratedPartition_right_inverse (decoratedPartitionSurjection d))
  right_inv := surjectionDecoratedPartition_right_inverse

end AcceleratedLogConcave.Tensor.FlowInduction
