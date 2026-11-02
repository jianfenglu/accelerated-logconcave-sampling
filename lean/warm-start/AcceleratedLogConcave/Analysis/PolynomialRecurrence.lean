import AcceleratedLogConcave.Analysis.PolynomialEnvelope
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Cast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-! finite triangular polynomial-envelope closure. This is scalar
bookkeeping for the already proved state-jet binomial recurrence. It bounds
only n+q≤K and consumes velocity orders strictly below K. -/
noncomputable section
open Set
namespace AcceleratedLogConcave.Analysis.PolynomialEnvelope

theorem exists_polynomial_triangular_bound
    {X : Type*} {s : Set X} {R : X → ℝ} (hR : ∀ x ∈ s, 1 ≤ R x)
    {f : ℕ → ℕ → X → ℝ} {v : ℕ → X → ℝ} (K : ℕ)
    (hbase : ∀ q ≤ K, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ x ∈ s, f 0 q x ≤ C * R x ^ N)
    (hvel : ∀ q < K, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ x ∈ s, v q x ≤ C * R x ^ N)
    (hvel_nonneg : ∀ q, ∀ x ∈ s, 0 ≤ v q x)
    (hrec : ∀ n q, n + q < K → ∀ x ∈ s,
      f (n + 1) q x ≤ ∑ i ∈ Finset.range (q + 1),
        (q.choose i : ℝ) * f n (i + 1) x * v (q - i) x) :
    ∀ n q, n + q ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ x ∈ s, f n q x ≤ C * R x ^ N := by
  classical
  intro n
  induction n with
  | zero =>
    intro q hq
    exact hbase q (by simpa using hq)
  | succ n ih =>
    intro q hq
    let a : (Fin (q + 1) ⊕ Fin (q + 1)) → X → ℝ :=
      Sum.elim (fun i => f n (i.val + 1)) (fun i => v (q - i.val))
    have ha : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
        ∀ x ∈ s, a i x ≤ C * R x ^ N := by
      intro i
      rcases i with i | i
      · exact ih (i.val + 1) (by have hi := i.isLt; omega)
      · exact hvel (q - i.val) (by omega)
    obtain ⟨A, hA, N, hbound⟩ := exists_common_finite_polynomial_bound hR ha
    let c : ℝ := ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    refine ⟨c * A ^ 2, mul_nonneg hc (sq_nonneg A), N * 2, ?_⟩
    intro x hx
    have hD : 0 ≤ A * R x ^ N :=
      mul_nonneg (zero_le_one.trans hA) (pow_nonneg (zero_le_one.trans (hR x hx)) _)
    have hprod (i : ℕ) (hi : i ∈ Finset.range (q + 1)) :
        f n (i + 1) x * v (q - i) x ≤ (A * R x ^ N) ^ 2 := by
      have hi' := Finset.mem_range.mp hi
      have hf := hbound (Sum.inl ⟨i, hi'⟩) x hx
      have hv := hbound (Sum.inr ⟨i, hi'⟩) x hx
      simpa only [a, Sum.elim_inl, Sum.elim_inr, pow_two] using
        mul_le_mul hf hv (hvel_nonneg (q - i) x hx) hD
    calc
      _ ≤ ∑ i ∈ Finset.range (q + 1),
          (q.choose i : ℝ) * f n (i + 1) x * v (q - i) x :=
        hrec n q (by omega) x hx
      _ ≤ ∑ i ∈ Finset.range (q + 1),
          (q.choose i : ℝ) * (A * R x ^ N) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hprod i hi) (by positivity)
      _ = (c * A ^ 2) * R x ^ (N * 2) := by
        rw [← Finset.sum_mul, mul_pow, pow_mul, mul_assoc]

end AcceleratedLogConcave.Analysis.PolynomialEnvelope
