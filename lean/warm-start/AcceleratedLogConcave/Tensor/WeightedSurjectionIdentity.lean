import AcceleratedLogConcave.Tensor.SizedAssignmentCounts

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.FlowInduction

/-- Finite positive compositions, with each entry explicitly bounded by n. -/
abbrev PositiveSizeProfile (n k : ℕ) :=
  {j : Fin k → Fin (n+1) // (∀ i, 0 < (j i).val) ∧ (∑ i, (j i).val) = n}

def surjectionSizeProfile {n k : ℕ} (f : LabeledSurjection n k) : PositiveSizeProfile n k :=
  ⟨fun i => ⟨Fintype.card {x : Fin n // f.val x = i}, by
    have h := Fintype.card_le_of_injective
      (fun x : {x : Fin n // f.val x = i} => x.val) Subtype.val_injective
    simp only [Fintype.card_fin] at h
    omega⟩,
   surjection_fiber_card_pos f, assignment_fiber_card_sum f.val⟩

/-- Decompose all surjections by their ACTUAL positive size profile. -/
def profileAssignmentSurjectionEquiv (n k : ℕ) :
    (Σ j : PositiveSizeProfile n k, SizedAssignment (n := n) (fun i => (j.val i).val)) ≃
      LabeledSurjection n k :=
  Equiv.ofBijective (fun x => ⟨x.2.val, sizedAssignment_surjective x.1.property.1 x.2⟩) (by
    constructor
    · rintro ⟨j,f⟩ ⟨j',g⟩ h
      have hfg : f.val = g.val := congrArg Subtype.val h
      have hj : j = j' := by
        apply Subtype.ext
        funext i
        apply Fin.ext
        exact (f.property i).symm.trans ((by rw [hfg] :
          Fintype.card {x : Fin n // f.val x = i} =
            Fintype.card {x : Fin n // g.val x = i}).trans (g.property i))
      subst j'
      have hfg' : f = g := Subtype.ext hfg
      subst g
      rfl
    · intro f
      exact ⟨⟨surjectionSizeProfile f, ⟨f.val, fun _ => rfl⟩⟩, Subtype.ext rfl⟩)

/-- Exact weighted multinomial sum over freely labeled nonempty blocks. -/
theorem surjection_weighted_multinomial (n k : ℕ) (w : ℕ → ℝ) :
    (∑ f : LabeledSurjection n k, ∏ i, w (Fintype.card {x : Fin n // f.val x = i})) =
      ∑ j : PositiveSizeProfile n k,
        ((n.factorial : ℝ) / ∏ i, (((j.val i).val).factorial : ℝ)) *
          ∏ i, w ((j.val i).val) := by
  calc
    _ = ∑ jf : (Σ j : PositiveSizeProfile n k,
        SizedAssignment (n := n) (fun i => (j.val i).val)),
        ∏ i, w ((jf.1.val i).val) := by
      symm
      apply Fintype.sum_equiv (profileAssignmentSurjectionEquiv n k)
      intro jf
      apply Finset.prod_congr rfl
      intro i _
      exact congrArg w (jf.2.property i).symm
    _ = ∑ j : PositiveSizeProfile n k,
        ∑ f : SizedAssignment (n := n) (fun i => (j.val i).val),
          ∏ i, w ((j.val i).val) := by rw [Fintype.sum_sigma]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact sizedAssignment_weighted _ j.property.2 w

/-- Literal block embeddings parameterize the corresponding labeled fibers. -/
def decoratedPartitionFiberEquiv {n k : ℕ} (d : DecoratedPartition n k)
    (i : Fin d.1.length) :
    Fin (d.1.partSize i) ≃ {x : Fin n // (decoratedPartitionSurjection d).val x = d.2 i} :=
  Equiv.ofBijective (fun r => ⟨d.1.emb i r, by
    change d.2 (d.1.index (d.1.emb i r)) = d.2 i
    rw [partition_index_emb]⟩) (by
    constructor
    · intro r s h
      exact (d.1.emb_strictMono i).injective (congrArg Subtype.val h)
    · intro x
      have hx : d.1.index x.val = i := d.2.injective x.property
      obtain ⟨r,hr⟩ := (partition_index_iff d.1 i x.val).mp hx
      exact ⟨r, Subtype.ext hr⟩)

theorem decoratedPartition_weight {n k : ℕ} (d : DecoratedPartition n k) (w : ℕ → ℝ) :
    (∏ j, w (Fintype.card {x : Fin n // (decoratedPartitionSurjection d).val x = j})) =
      ∏ i, w (d.1.partSize i) := by
  symm
  apply Fintype.prod_equiv d.2
  intro i
  apply congrArg w
  simpa using Fintype.card_congr (decoratedPartitionFiberEquiv d i)

/-- Decoration count is k! exactly when the number of blocks is k. -/
theorem blockDecoration_card (l k : ℕ) :
    Fintype.card (Fin l ≃ Fin k) = if l = k then k.factorial else 0 := by
  by_cases h : l = k
  · subst l
    simp [Fintype.card_perm, Fintype.card_fin]
  · have hi : IsEmpty (Fin l ≃ Fin k) := ⟨fun e => h (by simpa using Fintype.card_congr e)⟩
    let := hi
    simp [h]

/-- The only canonical counting identity used is permutation-summed.
There is intentionally NO assertion about a canonical fixed ordered size profile. -/
theorem canonical_partition_weighted_multinomial (n k : ℕ) (w : ℕ → ℝ) :
    (k.factorial : ℝ) *
      (∑ c : OrderedFinpartition n, if c.length = k then ∏ i, w (c.partSize i) else 0) =
      ∑ j : PositiveSizeProfile n k,
        ((n.factorial : ℝ) / ∏ i, (((j.val i).val).factorial : ℝ)) *
          ∏ i, w ((j.val i).val) := by
  rw [← surjection_weighted_multinomial n k w]
  have htransport :
      (∑ d : DecoratedPartition n k, ∏ i, w (d.1.partSize i)) =
        ∑ f : LabeledSurjection n k, ∏ i, w (Fintype.card {x : Fin n // f.val x = i}) := by
    apply Fintype.sum_equiv (canonicalMaximumSurjectionEquiv n k)
    intro d
    exact (decoratedPartition_weight d w).symm
  rw [← htransport, Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  change (k.factorial : ℝ) * (if c.length = k then ∏ i, w (c.partSize i) else 0) =
    ∑ _d : Fin c.length ≃ Fin k, ∏ i, w (c.partSize i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, blockDecoration_card]
  split_ifs <;> simp

end AcceleratedLogConcave.Tensor.FlowInduction
