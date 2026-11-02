import AcceleratedLogConcave.Tensor.InverseGrowthScalars
import AcceleratedLogConcave.Tensor.FiniteOrderMass
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.InverseFlow
open FlowInduction

/-- Unlike normalizedOrder, the inverse normalization retains D_0 = E. -/
def normalizedInverseOrder (n : ℕ) : ℝ :=
  inverseOrderConstant n / (n.factorial : ℝ)

def inverseWeightedOrder (n : ℕ) : ℝ :=
  normalizedInverseOrder n * (1/64 : ℝ)^n

/-- Shifted kernel: index k means actual positive order k+1. -/
def inverseKernelWeight (k : ℕ) : ℝ :=
  ((k+2 : ℕ) : ℝ) * normalizedOrder (k+2) * (1/64 : ℝ)^(k+1)

def inverseKernelMass (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, inverseKernelWeight k

def inverseOrderMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N+1), inverseWeightedOrder n

@[simp] theorem normalizedInverseOrder_zero :
    normalizedInverseOrder 0 = growthConstant := by
  simp [normalizedInverseOrder, inverseOrderConstant_zero]

@[simp] theorem inverseWeightedOrder_zero :
    inverseWeightedOrder 0 = growthConstant := by
  simp [inverseWeightedOrder]

@[simp] theorem inverseKernelMass_zero : inverseKernelMass 0 = 0 := by
  simp [inverseKernelMass]

@[simp] theorem inverseOrderMass_zero : inverseOrderMass 0 = growthConstant := by
  simp [inverseOrderMass]

theorem normalizedInverseOrder_nonneg (n : ℕ) : 0 ≤ normalizedInverseOrder n :=
  div_nonneg (inverseOrderConstant_nonneg n) (Nat.cast_nonneg _)

theorem inverseWeightedOrder_nonneg (n : ℕ) : 0 ≤ inverseWeightedOrder n :=
  mul_nonneg (normalizedInverseOrder_nonneg n) (pow_nonneg (by norm_num) _)

theorem inverseKernelWeight_nonneg (k : ℕ) : 0 ≤ inverseKernelWeight k :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (normalizedOrder_nonneg _))
    (pow_nonneg (by norm_num) _)

theorem inverseKernelMass_nonneg (N : ℕ) : 0 ≤ inverseKernelMass N :=
  Finset.sum_nonneg (fun k _ => inverseKernelWeight_nonneg k)

theorem inverseOrderMass_nonneg (N : ℕ) : 0 ≤ inverseOrderMass N :=
  Finset.sum_nonneg (fun n _ => inverseWeightedOrder_nonneg n)

/-- Exact binomial/factorial cancellation, before any inequalities. -/
theorem inverse_choose_factorial_ratio {n s : ℕ} (hs : s ≤ n) :
    (n.choose s : ℝ) / (n.factorial : ℝ) =
      1 / ((s.factorial : ℝ) * ((n-s).factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hsf : (s.factorial : ℝ) ≠ 0 := by positivity
  have hkf : ((n-s).factorial : ℝ) ≠ 0 := by positivity
  apply (div_eq_div_iff hn (mul_ne_zero hsf hkf)).2
  have h : (n.choose s : ℝ) * (s.factorial : ℝ) *
      ((n-s).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hs
  simpa only [mul_assoc, one_mul] using h

/-- Each literal summand normalizes without assuming a new recurrence. -/
theorem inverse_normalized_summand {n s : ℕ} (hs : s ≤ n) :
    ((n.choose s : ℝ) * inverseOrderConstant s * orderConstant (n-s+1)) /
        (n.factorial : ℝ) =
      normalizedInverseOrder s * ((n-s+1 : ℕ) : ℝ) * normalizedOrder (n-s+1) := by
  rw [normalizedInverseOrder, normalizedOrder_pos_index _ (by omega)]
  calc
    _ = ((n.choose s : ℝ) / (n.factorial : ℝ)) *
        inverseOrderConstant s * orderConstant (n-s+1) := by ring
    _ = _ := by
      rw [inverse_choose_factorial_ratio hs, Nat.factorial_succ]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hs' : (s.factorial : ℝ) ≠ 0 := by positivity
      have hk' : ((n-s).factorial : ℝ) ≠ 0 := by positivity
      have hj' : ((n-s : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hs', hk', hj']

/-- Normalized recurrence with the original s-index, valid only at n>0. -/
theorem normalizedInverseOrder_recurrence {n : ℕ} (hn : 0 < n) :
    normalizedInverseOrder n = growthConstant *
      ∑ s ∈ Finset.range n,
        normalizedInverseOrder s * ((n-s+1 : ℕ) : ℝ) * normalizedOrder (n-s+1) := by
  unfold normalizedInverseOrder at ⊢
  rw [inverseOrderConstant_recurrence hn, mul_div_assoc, Finset.sum_div]
  apply congrArg (fun z : ℝ => growthConstant * z)
  apply Finset.sum_congr rfl
  intro s hs
  exact inverse_normalized_summand (Nat.le_of_lt (Finset.mem_range.mp hs))

/-- Exact finite reversal. Here k ranges from 0 to n-1, so k+1 ranges 1..n. -/
theorem normalizedInverseOrder_recurrence_reversed (n : ℕ) :
    normalizedInverseOrder (n+1) = growthConstant *
      ∑ k ∈ Finset.range (n+1),
        normalizedInverseOrder (n-k) * ((k+2 : ℕ) : ℝ) * normalizedOrder (k+2) := by
  rw [normalizedInverseOrder_recurrence (by omega)]
  apply congrArg (fun z : ℝ => growthConstant * z)
  calc
    _ = ∑ k ∈ Finset.range (n+1),
        normalizedInverseOrder (n+1-1-k) *
          ((n+1-(n+1-1-k)+1 : ℕ) : ℝ) *
          normalizedOrder (n+1-(n+1-1-k)+1) :=
      (Finset.sum_range_reflect
        (fun s => normalizedInverseOrder s * ((n+1-s+1 : ℕ) : ℝ) *
          normalizedOrder (n+1-s+1)) (n+1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have h₁ : n+1-1-k = n-k := by omega
      have h₂ : n+1-(n-k)+1 = k+2 := by omega
      rw [h₁, h₂]

/-- Multiply radius powers, never divide by any spatial/clock parameter. -/
theorem inverseWeightedOrder_recurrence (n : ℕ) :
    inverseWeightedOrder (n+1) = growthConstant *
      ∑ s ∈ Finset.range (n+1), inverseWeightedOrder s * inverseKernelWeight (n-s) := by
  rw [inverseWeightedOrder, normalizedInverseOrder_recurrence (by omega),
    mul_assoc, Finset.sum_mul]
  apply congrArg (fun z : ℝ => growthConstant * z)
  apply Finset.sum_congr rfl
  intro s hs
  have hs' := Finset.mem_range.mp hs
  have hind : n+1-s+1 = n-s+2 := by omega
  have hpow : (1/64 : ℝ)^s * (1/64 : ℝ)^(n-s+1) = (1/64 : ℝ)^(n+1) := by
    rw [← pow_add, show s+(n-s+1)=n+1 by omega]
  simp only [inverseWeightedOrder, inverseKernelWeight, hind]
  rw [← hpow]
  ring

/-- Same weighted recurrence in positive-kernel order, for strong induction. -/
theorem inverseWeightedOrder_recurrence_reversed (n : ℕ) :
    inverseWeightedOrder (n+1) = growthConstant *
      ∑ k ∈ Finset.range (n+1), inverseWeightedOrder (n-k) * inverseKernelWeight k := by
  rw [inverseWeightedOrder_recurrence]
  apply congrArg (fun z : ℝ => growthConstant * z)
  calc
    _ = ∑ k ∈ Finset.range (n+1),
        inverseWeightedOrder (n+1-1-k) * inverseKernelWeight (n-(n+1-1-k)) :=
      (Finset.sum_range_reflect
        (fun s => inverseWeightedOrder s * inverseKernelWeight (n-s)) (n+1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have h₁ : n+1-1-k = n-k := by omega
      have h₂ : n-(n-k) = k := by omega
      rw [h₁, h₂]

/-- Exact radial scaling, with the derivative multiplier exposed. -/
theorem inverseKernelWeight_rescale (k : ℕ) :
    inverseKernelWeight k = 32 *
      (((k+2 : ℕ) : ℝ) * (1/2 : ℝ)^(k+1)) *
        (normalizedOrder (k+2) * (1/32 : ℝ)^(k+2)) := by
  unfold inverseKernelWeight
  rw [show (1/64 : ℝ) = (1/2 : ℝ)*(1/32 : ℝ) by norm_num, mul_pow]
  have hp : (1/32 : ℝ)^(k+2) = (1/32 : ℝ)^(k+1) * (1/32 : ℝ) := by
    rw [show k+2 = (k+1)+1 by omega, pow_succ]
  rw [hp]
  ring

theorem inverseKernelWeight_le_flow (k : ℕ) :
    inverseKernelWeight k ≤ 32 *
      (normalizedOrder (k+2) * (1/32 : ℝ)^(k+2)) := by
  have hw : ((k+2 : ℕ) : ℝ) * (1/2 : ℝ)^(k+1) ≤ 1 := by
    convert inverse_growth_half_weight (k+1) using 1
    push_cast
    ring
  have hp : 0 ≤ normalizedOrder (k+2) * (1/32 : ℝ)^(k+2) :=
    mul_nonneg (normalizedOrder_nonneg _) (pow_nonneg (by norm_num) _)
  rw [inverseKernelWeight_rescale]
  calc
    _ ≤ 32 * 1 * (normalizedOrder (k+2) * (1/32 : ℝ)^(k+2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num)) hp
    _ = _ := by ring

/-- Remove exactly C_1/1! times 1/32; C_0 never enters this identity. -/
theorem inverse_flow_tail_exact (N : ℕ) :
    (∑ k ∈ Finset.range N, normalizedOrder (k+2) * (1/32 : ℝ)^(k+2)) =
      orderMass (N+1) - growthConstant/32 := by
  have h : orderMass (N+1) = growthConstant/32 +
      ∑ k ∈ Finset.range N, normalizedOrder (k+2) * (1/32 : ℝ)^(k+2) := by
    unfold orderMass
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, zero_add, normalizedOrder_one, pow_one, Fin.val_succ]
    simp only [Nat.add_assoc]
    rw [Fin.sum_univ_eq_sum_range
      (fun k => normalizedOrder (k+2) * (1/32 : ℝ)^(k+2)) N]
    ring
  linarith

/-- Uniform finite kernel bound, including the empty cutoff N=0. -/
theorem inverseKernelMass_le (N : ℕ) :
    inverseKernelMass N ≤ 2-growthConstant := by
  calc
    inverseKernelMass N ≤ ∑ k ∈ Finset.range N,
        32 * (normalizedOrder (k+2) * (1/32 : ℝ)^(k+2)) :=
      Finset.sum_le_sum (fun k _ => inverseKernelWeight_le_flow k)
    _ = 32 * (orderMass (N+1) - growthConstant/32) := by
      rw [← Finset.mul_sum, inverse_flow_tail_exact]
    _ ≤ 2-growthConstant := by
      have h := orderMass_le_one_sixteenth (N+1)
      linarith

theorem inverseKernelMass_contraction (N : ℕ) :
    growthConstant * inverseKernelMass N ≤ (15/16 : ℝ) :=
  (mul_le_mul_of_nonneg_left (inverseKernelMass_le N) (Real.exp_pos _).le).trans
    inverse_growth_kernel_contraction

/-- Exact finite all-degree triangle rearrangement, not a per-degree box bound. -/
theorem inverse_triangle_exact (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑ s ∈ Finset.range (n+1),
      inverseWeightedOrder s * inverseKernelWeight (n-s)) =
    ∑ s ∈ Finset.range N, inverseWeightedOrder s * inverseKernelMass (N-s) := by
  rw [Finset.sum_range_diag_flip N
    (fun s k => inverseWeightedOrder s * inverseKernelWeight k)]
  apply Finset.sum_congr rfl
  intro s _
  exact (Finset.mul_sum _ _ _).symm

theorem inverseKernelMass_mono {M N : ℕ} (h : M ≤ N) :
    inverseKernelMass M ≤ inverseKernelMass N := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro k _ _
  exact inverseKernelWeight_nonneg k

/-- The finite triangle is enlarged once to the entire rectangle. -/
theorem inverse_triangle_le_rectangle (N : ℕ) :
    (∑ n ∈ Finset.range (N+1), ∑ s ∈ Finset.range (n+1),
      inverseWeightedOrder s * inverseKernelWeight (n-s)) ≤
        inverseOrderMass N * inverseKernelMass (N+1) := by
  rw [inverse_triangle_exact]
  calc
    _ ≤ ∑ s ∈ Finset.range (N+1),
        inverseWeightedOrder s * inverseKernelMass (N+1) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (inverseKernelMass_mono (Nat.sub_le _ _)) (inverseWeightedOrder_nonneg s)
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem inverseOrderMass_succ_exact (N : ℕ) :
    inverseOrderMass (N+1) = growthConstant + growthConstant *
      ∑ n ∈ Finset.range (N+1), ∑ s ∈ Finset.range (n+1),
        inverseWeightedOrder s * inverseKernelWeight (n-s) := by
  unfold inverseOrderMass
  rw [Finset.sum_range_succ', inverseWeightedOrder_zero]
  rw [add_comm]
  congr 1
  simp_rw [inverseWeightedOrder_recurrence]
  rw [← Finset.mul_sum]

theorem inverseOrderMass_succ_le (N : ℕ) :
    inverseOrderMass (N+1) ≤ growthConstant + (15/16 : ℝ)*inverseOrderMass N := by
  rw [inverseOrderMass_succ_exact]
  calc
    _ ≤ growthConstant + growthConstant *
        (inverseOrderMass N * inverseKernelMass (N+1)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left
        (inverse_triangle_le_rectangle N) (Real.exp_pos _).le) _
    _ = growthConstant + (growthConstant * inverseKernelMass (N+1)) *
        inverseOrderMass N := by ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right
      (inverseKernelMass_contraction (N+1)) (inverseOrderMass_nonneg N)) _

/-- Actual finite mass induction, retaining the nonzero constant term. -/
theorem inverseOrderMass_le (N : ℕ) : inverseOrderMass N ≤ 16*growthConstant := by
  induction N with
  | zero =>
      rw [inverseOrderMass_zero]
      have h : 0 ≤ growthConstant := (Real.exp_pos _).le
      linarith
  | succ N ih =>
      calc
        _ ≤ growthConstant + (15/16 : ℝ)*inverseOrderMass N := inverseOrderMass_succ_le N
        _ ≤ growthConstant + (15/16 : ℝ)*(16*growthConstant) := by linarith
        _ = 16*growthConstant := inverse_growth_mass_barrier

/-- Separate strong induction: bounded mass alone gives a weaker coefficient. -/
theorem inverseWeightedOrder_le (n : ℕ) : inverseWeightedOrder n ≤ growthConstant := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [inverseWeightedOrder_recurrence_reversed]
          calc
            _ ≤ growthConstant * ∑ k ∈ Finset.range (n+1),
                growthConstant * inverseKernelWeight k := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
              apply Finset.sum_le_sum
              intro k hk
              exact mul_le_mul_of_nonneg_right (ih (n-k) (by omega))
                (inverseKernelWeight_nonneg k)
            _ = growthConstant * (growthConstant * inverseKernelMass (n+1)) := by
              rw [← Finset.mul_sum]; rfl
            _ ≤ growthConstant * (15/16 : ℝ) :=
              mul_le_mul_of_nonneg_left (inverseKernelMass_contraction (n+1))
                (Real.exp_pos _).le
            _ ≤ growthConstant := by
              have h : 0 ≤ growthConstant := (Real.exp_pos _).le
              linarith

/-- Clean factorial-exponential bound at every order, including n=0. -/
theorem inverseOrderConstant_growth (n : ℕ) :
    inverseOrderConstant n ≤ growthConstant * (n.factorial : ℝ) * (64 : ℝ)^n := by
  have h := inverseWeightedOrder_le n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hp : 0 ≤ (64 : ℝ)^n := by positivity
  have hcancel : (1/64 : ℝ)^n * (64 : ℝ)^n = 1 := by
    rw [← mul_pow]; norm_num
  have hm := mul_le_mul_of_nonneg_right h hp
  unfold inverseWeightedOrder at hm
  rw [mul_assoc, hcancel, mul_one] at hm
  unfold normalizedInverseOrder at hm
  have h' := (div_le_iff₀ hf).mp hm
  nlinarith

theorem inverseOrderConstant_growth_clean (n : ℕ) :
    0 ≤ inverseOrderConstant n ∧
      inverseOrderConstant n ≤ (4/3 : ℝ) * (n.factorial : ℝ) * (64 : ℝ)^n := by
  refine ⟨inverseOrderConstant_nonneg n, (inverseOrderConstant_growth n).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right growthConstant_le_four_thirds (Nat.cast_nonneg _))
    (pow_nonneg (by norm_num) _)

theorem inverseOrderMass_le_clean (N : ℕ) : inverseOrderMass N ≤ (64/3 : ℝ) :=
  (inverseOrderMass_le N).trans inverse_growth_mass_clean

/-- Literal finite mass statement, exposing every normalization in the type. -/
theorem inverseOrderConstant_finite_mass (N : ℕ) :
    (∑ n ∈ Finset.range (N+1),
      (inverseOrderConstant n / (n.factorial : ℝ)) * (1/64 : ℝ)^n) ≤
        16*growthConstant :=
  inverseOrderMass_le N

/-- Numerical finite mass version, still with the literal D_0 included. -/
theorem inverseOrderConstant_finite_mass_clean (N : ℕ) :
    (∑ n ∈ Finset.range (N+1),
      (inverseOrderConstant n / (n.factorial : ℝ)) * (1/64 : ℝ)^n) ≤
        (64/3 : ℝ) :=
  inverseOrderMass_le_clean N

end AcceleratedLogConcave.Tensor.InverseFlow
