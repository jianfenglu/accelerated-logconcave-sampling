import AcceleratedLogConcave.Tensor.WeightedSurjectionIdentity
import AcceleratedLogConcave.Tensor.FiniteGrowthTuples

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.FlowInduction
open AcceleratedLogConcave.Analysis.SpatialPartition

/-- A bounded finite selector used only to reindex the actual partition arity. -/
theorem growth_arity_selector (n l : ℕ) (hl : l ≤ n) (a : ℕ → ℝ) :
    (∑ k : Fin (n+1), if l = k.val then a k.val else 0) = a l := by
  rw [Finset.sum_eq_single ⟨l, by omega⟩]
  · simp
  · intro k _ hk
    have hne : l ≠ k.val := by
      intro h
      apply hk
      exact Fin.ext h.symm
    simp [hne]
  · simp

/-- The actual erased one-block condition is exactly arity at least two. -/
theorem properPartitions_arity_iff {n : ℕ} (hn : 0 < n) (c : OrderedFinpartition n) :
    c ∈ properPartitions n hn ↔ 2 ≤ c.length := by
  have hpos := c.length_pos hn
  have hone := OrderedFinpartition.eq_oneBlock_iff hn c
  simp only [properPartitions, Finset.mem_erase, Finset.mem_univ, and_true]
  simp only [ne_eq, hone]
  omega

/-- Split the literal forcing sum by its actual finite arity. -/
theorem forcingConstant_by_arity (n : ℕ) (hn : 0 < n) :
    forcingConstant n hn =
      ∑ k : Fin (n+1), if 2 ≤ k.val then
        primitiveConstant k.val *
          (∑ c : OrderedFinpartition n,
            if c.length = k.val then ∏ i, orderConstant (c.partSize i) else 0)
      else 0 := by
  have hset : properPartitions n hn =
      (Finset.univ : Finset (OrderedFinpartition n)).filter (fun c => 2 ≤ c.length) := by
    ext c
    simp [properPartitions_arity_iff hn c]
  unfold forcingConstant
  rw [hset, Finset.sum_filter]
  calc
    _ = ∑ c : OrderedFinpartition n, ∑ k : Fin (n+1),
        if c.length = k.val then
          (if 2 ≤ k.val then primitiveConstant k.val *
            ∏ i, orderConstant (c.partSize i) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      exact (growth_arity_selector n c.length c.length_le
        (fun k => if 2 ≤ k then primitiveConstant k *
          ∏ i, orderConstant (c.partSize i) else 0)).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : 2 ≤ k.val
      · simp only [hk, ite_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        split_ifs <;> simp
      · simp [hk]

/-- Normalizing one positive profile pays its complete factorial denominator. -/
theorem positiveProfile_normalized_weight {n k : ℕ} (j : PositiveSizeProfile n k) :
    ((n.factorial : ℝ) / ∏ i, (((j.val i).val).factorial : ℝ)) *
        (∏ i, orderConstant ((j.val i).val)) =
      (n.factorial : ℝ) * ∏ i, normalizedOrder ((j.val i).val) := by
  have hb (i : Fin k) := normalizedOrder_pos_index ((j.val i).val) (j.property.1 i)
  simp_rw [hb]
  rw [Finset.prod_div_distrib]
  ring

/-- The weighted identity with actual order constants and their explicit normalization. -/
theorem actual_partition_normalization (n k : ℕ) :
    (k.factorial : ℝ) *
      (∑ c : OrderedFinpartition n,
        if c.length = k then ∏ i, orderConstant (c.partSize i) else 0) =
      (n.factorial : ℝ) *
        ∑ j : PositiveSizeProfile n k, ∏ i, normalizedOrder ((j.val i).val) := by
  rw [canonical_partition_weighted_multinomial n k orderConstant, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact positiveProfile_normalized_weight j

/-- The ACTUAL normalized recurrence, not a recurrence hypothesis.
All inner orders are positive because the summation type enforces it. -/
theorem normalizedOrder_actual_recurrence (n : ℕ) (hn : 2 ≤ n) :
    normalizedOrder n = growthConstant *
      ∑ k : Fin (n+1), if 2 ≤ k.val then
        Real.sqrt 2 ^ (k.val+1) *
          (∑ j : PositiveSizeProfile n k.val, ∏ i, normalizedOrder ((j.val i).val))
        else 0 := by
  rw [normalizedOrder_pos_index n (by omega), orderConstant_recurrence hn,
    forcingConstant_by_arity n (by omega)]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  apply (div_eq_iff hf).mpr
  rw [mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : 2 ≤ k.val
  · simp only [hk, ite_true, primitiveConstant]
    have h := actual_partition_normalization n k.val
    calc
      _ = Real.sqrt 2 ^ (k.val+1) *
          ((k.val.factorial : ℝ) *
            ∑ c : OrderedFinpartition n,
              if c.length = k.val then ∏ i, orderConstant (c.partSize i) else 0) := by ring
      _ = _ := by rw [h]; ring
  · simp [hk]

end AcceleratedLogConcave.Tensor.FlowInduction
