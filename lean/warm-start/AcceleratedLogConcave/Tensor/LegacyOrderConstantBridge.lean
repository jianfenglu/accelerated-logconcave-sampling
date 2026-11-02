import AcceleratedLogConcave.Tensor.InverseOrderConstants
import AcceleratedLogConcave.Tensor.QuantitativeBudgetTargets

/-!
Finite compatibility of the legacy tabulations with the triangular order constants.
The flow equality is deliberately restricted to positive order. The legacy primitive
at arity one is different, but the recurrence uses only proper partitions of arity
at least two. This module proves no analytic jet bound, growth bound, or kernel bound.
-/
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

namespace AcceleratedLogConcave.Tensor.LegacyOrderConstantBridge
open QuantitativeKernel
open AcceleratedLogConcave.Analysis.SpatialPartition

/-- Once written, a diagonal table entry is unchanged by later horizons. -/
theorem flowTable_stable {j N : ℕ} (hj : j ≤ N) :
    flowTable N j = flowTable j j := by
  induction N with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    rfl
  | succ N ih =>
    by_cases he : j = N + 1
    · subst j; rfl
    · simp only [flowTable, ite_eq_right he]
      exact ih (by omega)

/-- Stability includes the separately initialized inverse entry at zero. -/
theorem inverseTable_stable {j N : ℕ} (hj : j ≤ N) :
    inverseTable N j = inverseTable j j := by
  induction N with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    rfl
  | succ N ih =>
    by_cases he : j = N + 1
    · subst j; rfl
    · simp only [inverseTable, ite_eq_right he]
      exact ih (by omega)

/-- The conditional legacy sum has exactly the new proper-partition support. -/
theorem mem_properPartitions_iff {n : ℕ} (hn : 0 < n)
    (p : OrderedFinpartition n) :
    p ∈ FlowInduction.properPartitions n hn ↔ 2 ≤ p.length := by
  simp only [FlowInduction.properPartitions, Finset.mem_erase, Finset.mem_univ, and_true]
  rw [ne_eq, OrderedFinpartition.eq_oneBlock_iff hn p]
  have hp := p.length_pos hn
  omega

theorem primitiveConstant_eq_of_two_le {q : ℕ} (hq : 2 ≤ q) :
    primitiveConstant q = FlowInduction.primitiveConstant q := by
  simp [primitiveConstant, FlowInduction.primitiveConstant, show q ≠ 1 by omega]

theorem flowConstant_zero : flowConstant 0 = 0 := rfl

theorem flowConstant_one : flowConstant 1 = universalExp := by
  simp [flowConstant, flowTable]

/-- Extract the finite flow recurrence without assuming any recurrence axiom. -/
theorem flowConstant_recurrence {n : ℕ} (hn : 2 ≤ n) :
    flowConstant n = universalExp * ∑ p : OrderedFinpartition n,
      if 2 ≤ p.length then primitiveConstant p.length *
        ∏ i : Fin p.length, flowConstant (p.partSize i) else 0 := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hN : N ≠ 0 := by omega
  change flowTable (N + 1) (N + 1) = _
  simp only [flowTable, ↓reduceIte, hN]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  split_ifs with hp
  · congr 1
    apply Finset.prod_congr rfl
    intro i _
    have hs := spatialForcing_support (N + 1) (by omega) p
      ((mem_properPartitions_iff (by omega) p).mpr hp) i
    exact flowTable_stable (by omega)
  · rfl

/-- Exact positive-order bridge. Zero is intentionally excluded. -/
theorem flowConstant_eq_orderConstant {n : ℕ} (hn : 1 ≤ n) :
    flowConstant n = FlowInduction.orderConstant n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : 2 ≤ n
    · rw [flowConstant_recurrence hn2, FlowInduction.orderConstant_recurrence hn2]
      change universalExp * _ = universalExp * _
      congr 1
      unfold FlowInduction.forcingConstant
      rw [show FlowInduction.properPartitions n (by omega) =
        Finset.univ.filter (fun p : OrderedFinpartition n => 2 ≤ p.length) by
          ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact mem_properPartitions_iff (by omega) p]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs with hp
      · rw [primitiveConstant_eq_of_two_le hp]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        have hs := spatialForcing_support n (by omega) p
          ((mem_properPartitions_iff (by omega) p).mpr hp) i
        exact ih _ hs.2 hs.1
      · rfl
    · have : n = 1 := by omega
      subst n
      rw [flowConstant_one, FlowInduction.orderConstant_small (by omega)]
      rfl

/-- Extract the legacy inverse recurrence, including its order-zero inner entry. -/
theorem inverseConstant_succ (N : ℕ) :
    inverseConstant (N + 1) = universalExp * ∑ i ∈ Finset.range (N + 1),
      ((N + 1).choose (i + 1) : ℝ) * flowConstant (i + 2) * inverseConstant (N - i) := by
  change inverseTable (N + 1) (N + 1) = _
  simp only [inverseTable, ↓reduceIte]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [inverseTable_stable (Nat.sub_le N i)]
  rfl

/-- Exact all-order inverse bridge, with a shared zero-order initialization. -/
theorem inverseConstant_eq_inverseOrderConstant (n : ℕ) :
    inverseConstant n = InverseFlow.inverseOrderConstant n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [InverseFlow.inverseOrderConstant_zero]
      rfl
    | succ N =>
      rw [inverseConstant_succ, InverseFlow.inverseOrderConstant_recurrence (by omega)]
      change universalExp * _ = universalExp * _
      congr 1
      rw [← Finset.sum_range_reflect
        (fun i => ((N + 1).choose (i + 1) : ℝ) * flowConstant (i + 2) *
          inverseConstant (N - i)) (N + 1)]
      apply Finset.sum_congr rfl
      intro s hs
      have hsN : s ≤ N := by have := Finset.mem_range.mp hs; omega
      have hsub : N - (N - s) = s := by omega
      have hchoose : N - s + 1 = N + 1 - s := by omega
      have hflow : N - s + 2 = N + 1 - s + 1 := by omega
      simp only [Nat.add_sub_cancel_right]
      rw [hsub, hchoose, Nat.choose_symm (by omega : s ≤ N + 1), hflow,
        flowConstant_eq_orderConstant (by omega), ih s (by omega)]
      ring

/-- Boundary guard: there is no all-order flow equality. -/
theorem flowConstant_zero_ne_orderConstant_zero :
    flowConstant 0 ≠ FlowInduction.orderConstant 0 := by
  rw [flowConstant_zero, FlowInduction.orderConstant_small (by omega)]
  exact (ne_of_gt (Real.exp_pos _)).symm

/-- The legacy arity-one primitive is one, whereas the new primitive is two. -/
theorem primitiveConstant_one_boundary :
    primitiveConstant 1 = 1 ∧ FlowInduction.primitiveConstant 1 = 2 := by
  constructor
  · simp [primitiveConstant]
  · norm_num [FlowInduction.primitiveConstant, Real.sq_sqrt]

/-- At order one there are no proper partitions, hence no forcing summands. -/
theorem properPartitions_one_empty :
    FlowInduction.properPartitions 1 (by omega) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hl := (mem_properPartitions_iff (by omega) p).mp hp
  have hu := p.length_le
  omega

theorem forcingConstant_one_zero : FlowInduction.forcingConstant 1 (by omega) = 0 := by
  simp [FlowInduction.forcingConstant, properPartitions_one_empty]

end AcceleratedLogConcave.Tensor.LegacyOrderConstantBridge
