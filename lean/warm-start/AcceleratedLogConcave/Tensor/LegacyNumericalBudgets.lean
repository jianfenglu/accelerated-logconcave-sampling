import AcceleratedLogConcave.Tensor.LegacyOrderConstantBridge
import AcceleratedLogConcave.Tensor.FiniteInverseOrderGrowth

/-!
Unconditional finite numerical estimates for the exact legacy budget constants.
This module imports no unvalidated analytic induction and assumes no recurrence,
flow-jet estimate, inverse-jet estimate, or kernel estimate.
-/
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

namespace AcceleratedLogConcave.Tensor.LegacyNumericalBudgets
open QuantitativeKernel LegacyOrderConstantBridge
open AcceleratedLogConcave.Analysis.SpatialPartition

/-- Legacy zero is genuinely zero; positive entries use the exact equality bridge. -/
theorem flowConstant_nonneg (n : ℕ) : 0 ≤ flowConstant n := by
  by_cases hn : n = 0
  · subst n; rw [flowConstant_zero]
  · rw [flowConstant_eq_orderConstant (by omega)]
    exact FlowInduction.orderConstant_nonneg n

/-- Unlike the new flow constant, the legacy constant satisfies this bound at zero too. -/
theorem flowConstant_growth (n : ℕ) :
    flowConstant n ≤ (n.factorial : ℝ) * (32 : ℝ)^n / 16 := by
  by_cases hn : n = 0
  · subst n; norm_num [flowConstant_zero]
  · rw [flowConstant_eq_orderConstant (by omega)]
    exact FlowInduction.orderConstant_growth n (by omega)

theorem inverseConstant_nonneg (n : ℕ) : 0 ≤ inverseConstant n := by
  rw [inverseConstant_eq_inverseOrderConstant]
  exact InverseFlow.inverseOrderConstant_nonneg n

theorem inverseConstant_growth (n : ℕ) :
    inverseConstant n ≤ universalExp * (n.factorial : ℝ) * (64 : ℝ)^n := by
  rw [inverseConstant_eq_inverseOrderConstant]
  exact InverseFlow.inverseOrderConstant_growth n

theorem inverseConstant_growth_clean (n : ℕ) :
    inverseConstant n ≤ (4/3 : ℝ) * (n.factorial : ℝ) * (64 : ℝ)^n := by
  rw [inverseConstant_eq_inverseOrderConstant]
  exact (InverseFlow.inverseOrderConstant_growth_clean n).2

theorem universalExp_nonneg : 0 ≤ universalExp := (Real.exp_pos _).le

theorem one_le_universalExp : 1 ≤ universalExp := by
  exact Real.one_le_exp (by norm_num)

theorem universalExp_le_four_thirds : universalExp ≤ (4/3 : ℝ) :=
  FlowInduction.growthConstant_le_four_thirds

/-- The finite forcing is bounded by the actual recursively defined flow constant. -/
theorem forcingConstant_le_orderConstant {n : ℕ} (hn : 0 < n) :
    FlowInduction.forcingConstant n hn ≤ FlowInduction.orderConstant n := by
  by_cases hn2 : 2 ≤ n
  · rw [FlowInduction.orderConstant_recurrence hn2]
    exact le_mul_of_one_le_left (FlowInduction.forcingConstant_nonneg n hn)
      one_le_universalExp
  · have : n = 1 := by omega
    subst n
    rw [forcingConstant_one_zero]
    exact FlowInduction.orderConstant_nonneg 1

/-- The shifted primitive costs only one linear arity factor. -/
theorem primitiveConstant_succ (k : ℕ) :
    FlowInduction.primitiveConstant (k+1) =
      ((k : ℝ)+1) * Real.sqrt 2 * FlowInduction.primitiveConstant k := by
  simp only [FlowInduction.primitiveConstant, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  ring

theorem primitiveConstant_succ_le {k n : ℕ} (hk : k ≤ n) :
    FlowInduction.primitiveConstant (k+1) ≤
      (2*((n : ℝ)+1)) * FlowInduction.primitiveConstant k := by
  rw [primitiveConstant_succ]
  have hk' : (k : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hk 1
  have hs : Real.sqrt 2 ≤ 2 := FlowInduction.growth_sqrt_two_le.trans (by norm_num)
  have h := mul_le_mul hk' hs (Real.sqrt_nonneg _) (by positivity : 0 ≤ (n : ℝ)+1)
  have hm := mul_le_mul_of_nonneg_right h (FlowInduction.primitiveConstant_nonneg k)
  nlinarith

/-- Only positive block sizes occur, so the flow equality never touches its false zero case. -/
theorem compositionConstant_eq_new {n : ℕ} (hn : 0 < n) :
    compositionConstant n = ∑ p : OrderedFinpartition n,
      FlowInduction.primitiveConstant (p.length+1) *
        ∏ i, FlowInduction.orderConstant (p.partSize i) := by
  rw [compositionConstant, ite_eq_right (by omega)]
  apply Finset.sum_congr rfl
  intro p _
  rw [primitiveConstant_eq_of_two_le (by have := p.length_pos hn; omega)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact flowConstant_eq_orderConstant (p.partSize_pos i)

/-- Exact one-block separation. The new arity-one primitive equals two, not one. -/
theorem full_primitive_sum {n : ℕ} (hn : 0 < n) :
    (∑ p : OrderedFinpartition n, FlowInduction.primitiveConstant p.length *
      ∏ i, FlowInduction.orderConstant (p.partSize i)) =
      FlowInduction.forcingConstant n hn + 2*FlowInduction.orderConstant n := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (OrderedFinpartition.oneBlock n hn))]
  change FlowInduction.forcingConstant n hn + _ = _
  congr 1
  change FlowInduction.primitiveConstant 1 * (∏ _i : Fin 1, FlowInduction.orderConstant n) = _
  simp [FlowInduction.primitiveConstant, Real.sq_sqrt]

/-- A recurrence comparison pays the complete composition partition sum. -/
theorem compositionConstant_le_flow {n : ℕ} (hn : 0 < n) :
    compositionConstant n ≤ 6*((n : ℝ)+1)*FlowInduction.orderConstant n := by
  rw [compositionConstant_eq_new hn]
  calc
    _ ≤ ∑ p : OrderedFinpartition n,
        (2*((n : ℝ)+1)) * (FlowInduction.primitiveConstant p.length *
          ∏ i, FlowInduction.orderConstant (p.partSize i)) := by
      apply Finset.sum_le_sum
      intro p _
      have hp : 0 ≤ ∏ i, FlowInduction.orderConstant (p.partSize i) :=
        Finset.prod_nonneg (fun i _ => FlowInduction.orderConstant_nonneg _)
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (primitiveConstant_succ_le p.length_le) hp
    _ = (2*((n : ℝ)+1)) *
        (FlowInduction.forcingConstant n hn + 2*FlowInduction.orderConstant n) := by
      rw [← Finset.mul_sum, full_primitive_sum hn]
    _ ≤ 6*((n : ℝ)+1)*FlowInduction.orderConstant n := by
      have h := forcingConstant_le_orderConstant hn
      have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*((n : ℝ)+1))
      nlinarith

/-- Linear order factors can be absorbed into a doubled exponential base. -/
theorem order_succ_le_two_pow (n : ℕ) : (n : ℝ)+1 ≤ (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-- A concrete all-order envelope, with the empty composition fixed to one. -/
theorem compositionConstant_growth (n : ℕ) :
    compositionConstant n ≤ (n.factorial : ℝ) * (64 : ℝ)^n := by
  by_cases hn : n = 0
  · subst n; simp [compositionConstant]
  · have hn' : 0 < n := by omega
    have h := compositionConstant_le_flow hn'
    have hg := mul_le_mul_of_nonneg_left (FlowInduction.orderConstant_growth n hn')
      (by positivity : 0 ≤ 6*((n : ℝ)+1))
    have hp := mul_le_mul_of_nonneg_left (order_succ_le_two_pow n)
      (by positivity : 0 ≤ (n.factorial : ℝ)*(32 : ℝ)^n)
    have he : (n.factorial : ℝ)*(32 : ℝ)^n*(2 : ℝ)^n =
        (n.factorial : ℝ)*(64 : ℝ)^n := by rw [mul_assoc, ← mul_pow]; norm_num
    rw [he] at hp
    have hf : 0 ≤ (n.factorial : ℝ)*(32 : ℝ)^n := by positivity
    nlinarith

theorem compositionConstant_nonneg (n : ℕ) : 0 ≤ compositionConstant n := by
  unfold compositionConstant
  split_ifs
  · norm_num
  · apply Finset.sum_nonneg
    intro p _
    apply mul_nonneg
    · unfold QuantitativeKernel.primitiveConstant
      split_ifs
      · norm_num
      · positivity
    · exact Finset.prod_nonneg (fun i _ => flowConstant_nonneg _)

/-- Every convolution summand pays exactly one factorial, including the endpoint n-i=0. -/
theorem kernel_summand_le {n j : ℕ} (hj : j ≤ n) :
    (n.choose j : ℝ) * inverseConstant j * compositionConstant (n-j) ≤
      universalExp * (n.factorial : ℝ) * (64 : ℝ)^n := by
  have hbound := mul_le_mul
    (mul_le_mul_of_nonneg_left (inverseConstant_growth j) (Nat.cast_nonneg _))
    (compositionConstant_growth (n-j)) (compositionConstant_nonneg _)
    (by unfold universalExp; positivity : 0 ≤ (n.choose j : ℝ) * (universalExp * (j.factorial : ℝ) * (64 : ℝ)^j))
  have hf : (n.choose j : ℝ)*(j.factorial : ℝ)*((n-j).factorial : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hp : (64 : ℝ)^j * (64 : ℝ)^(n-j) = (64 : ℝ)^n := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  calc
    _ ≤ _ := hbound
    _ = universalExp * ((n.choose j : ℝ)*(j.factorial : ℝ)*((n-j).factorial : ℝ)) *
        ((64 : ℝ)^j * (64 : ℝ)^(n-j)) := by ring
    _ = _ := by rw [hf, hp]

/-- The exact kernel constant has a dimension-free factorial/exponential envelope. -/
theorem kernelConstant_growth (n : ℕ) :
    kernelConstant n ≤ universalExp * (n.factorial : ℝ) * (128 : ℝ)^n := by
  have hc := mul_le_mul_of_nonneg_left (compositionConstant_growth n) universalExp_nonneg
  have hs : (∑ i ∈ Finset.range n,
      (n.choose (i+1) : ℝ)*inverseConstant (i+1)*compositionConstant (n-(i+1))) ≤
      (n : ℝ)*(universalExp*(n.factorial : ℝ)*(64 : ℝ)^n) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n,
          universalExp*(n.factorial : ℝ)*(64 : ℝ)^n := by
        apply Finset.sum_le_sum
        intro i hi
        exact kernel_summand_le (by have := Finset.mem_range.mp hi; omega)
      _ = _ := by simp
  have hn : (1 : ℝ)+(n : ℝ)/4 ≤ (2 : ℝ)^n := by
    have h := order_succ_le_two_pow n
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hm := mul_le_mul_of_nonneg_right hn
    (by unfold universalExp; positivity : 0 ≤ universalExp*(n.factorial : ℝ)*(64 : ℝ)^n)
  have he : (2 : ℝ)^n*(universalExp*(n.factorial : ℝ)*(64 : ℝ)^n) =
      universalExp*(n.factorial : ℝ)*(128 : ℝ)^n := by
    calc
      _ = universalExp*(n.factorial : ℝ)*((2 : ℝ)^n*(64 : ℝ)^n) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  rw [he] at hm
  unfold kernelConstant
  nlinarith

theorem kernelConstant_growth_clean (n : ℕ) :
    kernelConstant n ≤ (4/3 : ℝ) * (n.factorial : ℝ) * (128 : ℝ)^n := by
  exact (kernelConstant_growth n).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right universalExp_le_four_thirds (Nat.cast_nonneg _))
      (pow_nonneg (by norm_num) _))

/-- A single explicit threshold for a freely chosen universal budget parameter.
The extra power is necessary at order zero, since kernelConstant 0 = exp(1/4)>1. -/
theorem kernelConstant_le_universal_threshold {c : ℝ} (hc : 128 ≤ c) (n : ℕ) :
    kernelConstant n ≤ c^(n+1) * (n.factorial : ℝ) := by
  have hpow : (128 : ℝ)^n ≤ c^n := pow_le_pow_left₀ (by norm_num) hc n
  have hE : universalExp ≤ c := universalExp_le_four_thirds.trans (by linarith)
  have hprod := mul_le_mul hE hpow (pow_nonneg (by norm_num) n) (by linarith : 0 ≤ c)
  have h := mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg n.factorial)
  have hg := kernelConstant_growth n
  rw [pow_succ]
  nlinarith

/-- The literal kernel constant is nonnegative, including the empty convolution. -/
theorem kernelConstant_nonneg (n : ℕ) : 0 ≤ kernelConstant n := by
  apply add_nonneg (mul_nonneg universalExp_nonneg (compositionConstant_nonneg n))
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (inverseConstant_nonneg _))
    (compositionConstant_nonneg _)

end AcceleratedLogConcave.Tensor.LegacyNumericalBudgets
