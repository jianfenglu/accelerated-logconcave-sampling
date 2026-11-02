import AcceleratedLogConcave.Tensor.FiniteDegreeInjection
import AcceleratedLogConcave.Tensor.FiniteGrowthBarrier
import Mathlib.Algebra.BigOperators.Fin

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.FlowInduction

/-- Positive profiles have no more slots than their total degree. -/
theorem positiveSizeProfile_arity_le {n k : ℕ} (j : PositiveSizeProfile n k) :
    k ≤ n := by
  have h : (∑ i : Fin k, (1 : ℕ)) ≤ ∑ i : Fin k, (j.val i).val :=
    Finset.sum_le_sum (fun i _ => by
      have hi := j.property.1 i
      omega)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, j.property.2] using h

/-- The exact positive-profile coefficient, including empty strata. -/
def profileCoefficient (n k : ℕ) : ℝ :=
  ∑ j : PositiveSizeProfile n k, ∏ i, normalizedOrder ((j.val i).val)

theorem profileCoefficient_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    profileCoefficient n k = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact False.elim (Nat.not_le_of_lt h (positiveSizeProfile_arity_le j))

/-- Zero outside the proper-partition arities, without changing b_0 or C_0. -/
def growthArityTerm (n k : ℕ) : ℝ :=
  if 2 ≤ k then Real.sqrt 2 ^ (k+1) * profileCoefficient n k else 0

theorem growthArityTerm_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    growthArityTerm n k = 0 := by
  simp [growthArityTerm, profileCoefficient_eq_zero_of_lt h]

theorem growthArityTerm_small_degree {n : ℕ} (hn : n < 2) (k : ℕ) :
    growthArityTerm n k = 0 := by
  by_cases hk : 2 ≤ k
  · exact growthArityTerm_eq_zero_of_lt (by omega)
  · simp [growthArityTerm, hk]

/-- Padding a finite natural-index sum adds only terms certified zero. -/
theorem growth_fin_sum_padding (a : ℕ → ℝ) {m M : ℕ} (hm : m ≤ M)
    (hz : ∀ k, m ≤ k → a k = 0) :
    (∑ k : Fin m, a k.val) = ∑ k : Fin M, a k.val := by
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  apply Finset.sum_subset (Finset.range_mono hm)
  intro k _ hk
  apply hz
  simpa only [Finset.mem_range, not_lt] using hk

/-- Actual recurrence at every degree with one common finite arity bound.
The explicit linear term is the only degree-one contribution. -/
theorem normalizedOrder_common_arity (n M : ℕ) (hM : n+1 ≤ M) :
    normalizedOrder n = (if n = 1 then growthConstant else 0) +
      growthConstant * ∑ k : Fin M, growthArityTerm n k.val := by
  by_cases hn : n < 2
  · have hz : (∑ k : Fin M, growthArityTerm n k.val) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact growthArityTerm_small_degree hn k.val
    rw [hz]
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl <;> simp
  · have hn2 : 2 ≤ n := by omega
    have hpad := growth_fin_sum_padding (growthArityTerm n) hM
      (fun k hk => growthArityTerm_eq_zero_of_lt (by omega : n < k))
    rw [normalizedOrder_actual_recurrence n hn2]
    change growthConstant * (∑ k : Fin (n+1), growthArityTerm n k.val) = _
    rw [hpad]
    simp [show n ≠ 1 by omega]

/-- Include the harmless b_0 term, not the actual nonzero C_0 term. -/
theorem orderMass_as_degrees (N : ℕ) :
    orderMass N = ∑ d : Fin (N+1),
      normalizedOrder d.val * (1/32 : ℝ) ^ d.val := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, normalizedOrder_zero, zero_mul, zero_add, Fin.val_succ]
  rfl

/-- A single padded recurrence, with the radius paid inside every summand. -/
theorem normalizedOrder_common_arity_weight (n M : ℕ) (hM : n+1 ≤ M) :
    normalizedOrder n * (1/32 : ℝ)^n =
      (if n = 1 then growthConstant / 32 else 0) +
      growthConstant * ∑ k : Fin M,
        growthArityTerm n k.val * (1/32 : ℝ)^n := by
  rw [normalizedOrder_common_arity n M hM, add_mul, mul_assoc,
    Finset.sum_mul]
  congr 1
  by_cases hn : n = 1
  · simp [hn, div_eq_mul_inv]
  · simp [hn]

/-- Collect all degrees at one arity into the dependent finite profile type. -/
theorem growthArityTerm_collect (N k : ℕ) :
    (∑ d : Fin (N+2), growthArityTerm d.val k * (1/32 : ℝ)^d.val) =
      if 2 ≤ k then Real.sqrt 2 ^ (k+1) *
        (∑ x : BoundedPositiveProfile N k,
          (∏ i, normalizedOrder ((x.2.val i).val)) * (1/32 : ℝ)^x.1.val)
      else 0 := by
  by_cases hk : 2 ≤ k
  · simp only [growthArityTerm, hk, ite_true]
    calc
      _ = ∑ d : Fin (N+2), Real.sqrt 2 ^ (k+1) *
          (∑ j : PositiveSizeProfile d.val k,
            (∏ i, normalizedOrder ((j.val i).val)) * (1/32 : ℝ)^d.val) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [← Finset.sum_mul]
        unfold profileCoefficient
        ring
      _ = Real.sqrt 2 ^ (k+1) *
          (∑ d : Fin (N+2), ∑ j : PositiveSizeProfile d.val k,
            (∏ i, normalizedOrder ((j.val i).val)) * (1/32 : ℝ)^d.val) := by
        rw [Finset.mul_sum]
      _ = _ := by rw [Fintype.sum_sigma]
  · simp [growthArityTerm, hk]

/-- Exact finite rearrangement. Each arity collects ALL degrees once, through
BoundedPositiveProfile; there is no repeated per-degree box payment. -/
theorem orderMass_succ_exact (N : ℕ) :
    orderMass (N+1) = growthConstant / 32 + growthConstant *
      ∑ k : Fin (N+2), if 2 ≤ k.val then
        Real.sqrt 2 ^ (k.val+1) *
          (∑ x : BoundedPositiveProfile N k.val,
            (∏ i, normalizedOrder ((x.2.val i).val)) * (1/32 : ℝ)^x.1.val)
        else 0 := by
  rw [orderMass_as_degrees]
  have hlinear : (∑ d : Fin (N+2),
      if d.val = 1 then growthConstant / 32 else 0) = growthConstant / 32 := by
    rw [Finset.sum_eq_single (⟨1, by omega⟩ : Fin (N+2))]
    · simp
    · intro d _ hd
      have hne : d.val ≠ 1 := by
        intro h
        apply hd
        exact Fin.ext h
      simp [hne]
    · simp
  calc
    _ = ∑ d : Fin (N+2), ((if d.val = 1 then growthConstant / 32 else 0) +
        growthConstant * ∑ k : Fin (N+2),
          growthArityTerm d.val k.val * (1/32 : ℝ)^d.val) := by
      apply Finset.sum_congr rfl
      intro d _
      exact normalizedOrder_common_arity_weight d.val (N+2) (by omega)
    _ = growthConstant / 32 + growthConstant *
        ∑ k : Fin (N+2), ∑ d : Fin (N+2),
          growthArityTerm d.val k.val * (1/32 : ℝ)^d.val := by
      rw [Finset.sum_add_distrib, hlinear, ← Finset.mul_sum, Finset.sum_comm]
    _ = _ := by
      apply congrArg (fun x : ℝ => growthConstant / 32 + growthConstant * x)
      apply Finset.sum_congr rfl
      intro k _
      exact growthArityTerm_collect N k.val

/-- The all-degree injection now bounds the literal next mass. -/
theorem orderMass_succ_le_box (N : ℕ) :
    orderMass (N+1) ≤ growthConstant / 32 + growthConstant *
      ∑ k : Fin (N+2), if 2 ≤ k.val then
        Real.sqrt 2 ^ (k.val+1) * orderMass N ^ k.val else 0 := by
  rw [orderMass_succ_exact]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : 2 ≤ k.val
  · simp only [hk, ite_true]
    exact mul_le_mul_of_nonneg_left (boundedPositiveProfile_mass_le N k.val hk)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  · simp [hk]

/-- The exact finite arity shift used by the already supplied barrier. -/
theorem growth_common_arity_barrier_sum (N : ℕ) :
    (∑ k : Fin (N+2), if 2 ≤ k.val then
      Real.sqrt 2 ^ (k.val+1) * (1/16 : ℝ)^k.val else 0) =
    ∑ h ∈ Finset.range N, Real.sqrt 2 ^ (h+3) * (1/16 : ℝ)^(h+2) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, show ¬ (2 ≤ (0 : ℕ)) by omega, ite_false, zero_add,
    Fin.val_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, show ¬ (2 ≤ (0 : ℕ)+1) by omega, ite_false, zero_add,
    Fin.val_succ]
  simp only [show ∀ h : ℕ, 2 ≤ h+1+1 from fun h => by omega, ite_true]
  simpa only [Nat.add_assoc] using
    (Fin.sum_univ_eq_sum_range
      (fun h => Real.sqrt 2 ^ (h+3) * (1/16 : ℝ)^(h+2)) N)

/-- The actual finite mass induction, using no user-supplied recurrence or bound. -/
theorem orderMass_le_one_sixteenth (N : ℕ) : orderMass N ≤ (1/16 : ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      calc
        orderMass (N+1) ≤ growthConstant / 32 + growthConstant *
            ∑ k : Fin (N+2), if 2 ≤ k.val then
              Real.sqrt 2 ^ (k.val+1) * orderMass N ^ k.val else 0 :=
          orderMass_succ_le_box N
        _ ≤ growthConstant / 32 + growthConstant *
            ∑ k : Fin (N+2), if 2 ≤ k.val then
              Real.sqrt 2 ^ (k.val+1) * (1/16 : ℝ)^k.val else 0 := by
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
          apply Finset.sum_le_sum
          intro k _
          by_cases hk : 2 ≤ k.val
          · simp only [hk, ite_true]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (orderMass_nonneg N) ih _)
              (pow_nonneg (Real.sqrt_nonneg _) _)
          · simp [hk]
        _ ≤ (1/16 : ℝ) := by
          rw [growth_common_arity_barrier_sum]
          exact growth_finite_arity_barrier N

/-- Extraction of a single positive normalized coefficient from its own mass. -/
theorem normalizedOrder_growth (n : ℕ) (hn : 1 ≤ n) :
    normalizedOrder n ≤ (32 : ℝ)^n / 16 := by
  have hterm := normalizedOrder_term_le_mass n (⟨n-1, by omega⟩ : Fin n)
  have hind := orderMass_le_one_sixteenth n
  have he : n-1+1 = n := by omega
  simp only [he] at hterm
  have hb : normalizedOrder n * (1/32 : ℝ)^n ≤ 1/16 := hterm.trans hind
  have hm := mul_le_mul_of_nonneg_right hb (pow_nonneg (by norm_num : (0 : ℝ) ≤ 32) n)
  have hcancel : (1/32 : ℝ)^n * (32 : ℝ)^n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    normalizedOrder n = (normalizedOrder n * (1/32 : ℝ)^n) * (32 : ℝ)^n := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ (1/16 : ℝ) * (32 : ℝ)^n := hm
    _ = (32 : ℝ)^n / 16 := by ring

/-- Final literal-source growth estimate, only at positive orders.
In particular this does NOT falsely assert C_0=0. -/
theorem orderConstant_growth (n : ℕ) (hn : 1 ≤ n) :
    orderConstant n ≤ (n.factorial : ℝ) * (32 : ℝ)^n / 16 := by
  have h := normalizedOrder_growth n hn
  rw [normalizedOrder_pos_index n (by omega)] at h
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hm := (div_le_iff₀ hf).mp h
  nlinarith

/-- Positive-order two-sided statement, retaining actual nonnegativity. -/
theorem orderConstant_growth_two_sided (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ orderConstant n ∧
      orderConstant n ≤ (n.factorial : ℝ) * (32 : ℝ)^n / 16 :=
  ⟨orderConstant_nonneg n, orderConstant_growth n hn⟩

end AcceleratedLogConcave.Tensor.FlowInduction
