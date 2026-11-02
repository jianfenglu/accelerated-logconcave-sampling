import AcceleratedLogConcave.Analysis.PolynomialEnvelope
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! finite-order polynomial closure under scalar multiplication.
Only quantitative bounds through the requested order are used. -/
noncomputable section
open Set Function
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.PolynomialEnvelope

variable {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_polynomial_smul_jet_bound
    {U S : Set P} (hU : UniqueDiffOn ℝ U) (hSU : S ⊆ U)
    {f : P → ℝ} {g : P → G}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {R : P → ℝ} (hR : ∀ p ∈ S, 1 ≤ R p) (n : ℕ)
    (hfbound : ∀ i ≤ n, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p ∈ S,
      ‖iteratedFDerivWithin ℝ i f U p‖ ≤ C * R p ^ N)
    (hgbound : ∀ i ≤ n, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p ∈ S,
      ‖iteratedFDerivWithin ℝ i g U p‖ ≤ C * R p ^ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p ∈ S,
      ‖iteratedFDerivWithin ℝ n (fun q => f q • g q) U p‖ ≤ C * R p ^ N := by
  let a : (Fin (n + 1) ⊕ Fin (n + 1)) → P → ℝ :=
    Sum.elim (fun i p => ‖iteratedFDerivWithin ℝ i.val f U p‖)
      (fun i p => ‖iteratedFDerivWithin ℝ i.val g U p‖)
  have ha : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p ∈ S, a i p ≤ C * R p ^ N := by
    intro i
    rcases i with i | i
    · exact hfbound i.val (Nat.lt_succ_iff.mp i.isLt)
    · exact hgbound i.val (Nat.lt_succ_iff.mp i.isLt)
  obtain ⟨A, hA, N, hbound⟩ := exists_common_finite_polynomial_bound hR ha
  let B : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B * A ^ 2, mul_nonneg hB (sq_nonneg A), N * 2, ?_⟩
  intro p hp
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U p‖ *
        ‖iteratedFDerivWithin ℝ (n - i) g U p‖ :=
      norm_iteratedFDerivWithin_smul_le hf hg hU (hSU hp) (by simp)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (A * R p ^ N) * (A * R p ^ N) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < n + 1 := Finset.mem_range.mp hi
      have hj : n - i < n + 1 := Nat.lt_succ_of_le (Nat.sub_le n i)
      have hfi := hbound (Sum.inl ⟨i, hi'⟩) p hp
      have hgi := hbound (Sum.inr ⟨n - i, hj⟩) p hp
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfi (by positivity)) hgi
        (norm_nonneg _) (mul_nonneg (by positivity)
          (mul_nonneg (zero_le_one.trans hA)
            (pow_nonneg (zero_le_one.trans (hR p hp)) _)))
    _ = (B * A ^ 2) * R p ^ (N * 2) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      change B * (A * R p ^ N) * (A * R p ^ N) = _
      rw [mul_assoc, ← pow_two, mul_pow, ← pow_mul, ← mul_assoc]

end AcceleratedLogConcave.Analysis.PolynomialEnvelope
