import AcceleratedLogConcave.Tensor.FlowOrderGrowthScalars
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor.FlowInduction

/-- Zero is a separate normalization convention; orderConstant 0 is unchanged. -/
def normalizedOrder (n : ℕ) : ℝ :=
  if n = 0 then 0 else orderConstant n / (n.factorial : ℝ)

@[simp] theorem normalizedOrder_zero : normalizedOrder 0 = 0 := by
  simp [normalizedOrder]

theorem normalizedOrder_pos_index (n : ℕ) (hn : 0 < n) :
    normalizedOrder n = orderConstant n / (n.factorial : ℝ) := by
  simp [normalizedOrder, Nat.ne_of_gt hn]

theorem normalizedOrder_nonneg (n : ℕ) : 0 ≤ normalizedOrder n := by
  unfold normalizedOrder
  split_ifs
  · exact le_refl _
  · exact div_nonneg (orderConstant_nonneg n) (Nat.cast_nonneg _)

@[simp] theorem normalizedOrder_one : normalizedOrder 1 = growthConstant := by
  rw [normalizedOrder_pos_index 1 (by omega)]
  simp [orderConstant_small (show 1 < 2 by omega)]

/-- The finite positive-order mass; no zero-order term occurs. -/
def orderMass (N : ℕ) : ℝ :=
  ∑ j : Fin N, normalizedOrder (j.val+1) * (1/32 : ℝ) ^ (j.val+1)

theorem orderMass_nonneg (N : ℕ) : 0 ≤ orderMass N := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (normalizedOrder_nonneg _) (pow_nonneg (by norm_num) _)

@[simp] theorem orderMass_zero : orderMass 0 = 0 := by
  simp [orderMass]

@[simp] theorem orderMass_one : orderMass 1 = growthConstant / 32 := by
  simp [orderMass]
  ring

/-- A term is bounded by its actual finite mass, without assuming a mass bound. -/
theorem normalizedOrder_term_le_mass (N : ℕ) (j : Fin N) :
    normalizedOrder (j.val+1) * (1/32 : ℝ) ^ (j.val+1) ≤ orderMass N := by
  unfold orderMass
  apply Finset.single_le_sum (f := fun i : Fin N =>
    normalizedOrder (i.val+1) * (1/32 : ℝ) ^ (i.val+1)) (s := Finset.univ)
  · intro i _
    exact mul_nonneg (normalizedOrder_nonneg _) (pow_nonneg (by norm_num) _)
  · exact Finset.mem_univ j

/-- Full finite box expansion. The box indices represent positive orders j+1. -/
theorem growth_tuple_box (N k : ℕ) :
    (∑ p : Fin k → Fin N,
      ∏ i, normalizedOrder ((p i).val+1) * (1/32 : ℝ) ^ ((p i).val+1)) =
      orderMass N ^ k := by
  exact (Fintype.sum_pow
    (fun j : Fin N => normalizedOrder (j.val+1) * (1/32 : ℝ) ^ (j.val+1)) k).symm

/-- Dropping any finite restriction can only enlarge a nonnegative convolution.
P may be the total-degree cutoff; the result pays all tuples, not a single coefficient. -/
theorem growth_tuple_truncation (N k : ℕ) (P : (Fin k → Fin N) → Prop)
    [DecidablePred P] :
    (∑ p ∈ (Finset.univ : Finset (Fin k → Fin N)).filter P,
      ∏ i, normalizedOrder ((p i).val+1) * (1/32 : ℝ) ^ ((p i).val+1)) ≤
      orderMass N ^ k := by
  rw [← growth_tuple_box N k]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p _ _
  exact Finset.prod_nonneg (fun i _ =>
    mul_nonneg (normalizedOrder_nonneg _) (pow_nonneg (by norm_num) _))

/-- The radius exponent distributes exactly over each finite tuple. -/
theorem growth_tuple_radius {k : ℕ} (j : Fin k → ℕ) (r : ℝ) :
    (∏ i, normalizedOrder (j i) * r ^ (j i)) =
      (∏ i, normalizedOrder (j i)) * r ^ (∑ i, j i) := by
  rw [Finset.prod_mul_distrib, prod_powers]

/-- With at least two positive entries, each entry is below the total.
This is the strict-support fact needed before embedding into the N-1 box. -/
theorem growth_tuple_entry_lt_total {k : ℕ} (hk : 2 ≤ k)
    (j : Fin k → ℕ) (hj : ∀ i, 0 < j i) (i : Fin k) :
    j i < ∑ a, j a := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Fin k, b ≠ i := by
    by_cases hi : i.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      exact hi (congrArg Fin.val h).symm
  have hbmem : b ∈ (Finset.univ : Finset (Fin k)).erase i := by
    simp [hb]
  have hl : j b ≤ ∑ a ∈ (Finset.univ : Finset (Fin k)).erase i, j a :=
    Finset.single_le_sum (fun a _ => Nat.zero_le _) hbmem
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin k)) j (Finset.mem_univ i)
  have hp := hj b
  omega

/-- The preceding strictness supplies the exact finite cutoff needed in induction. -/
theorem growth_tuple_entry_le_previous {k N : ℕ} (hk : 2 ≤ k)
    (j : Fin k → ℕ) (hj : ∀ i, 0 < j i)
    (hdegree : (∑ i, j i) ≤ N+1) (i : Fin k) : j i ≤ N := by
  have h := growth_tuple_entry_lt_total hk j hj i
  omega

end AcceleratedLogConcave.Tensor.FlowInduction
