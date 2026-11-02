import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Choose

/-! Finite-envelope bookkeeping. A finite derivative family can be
bounded by one polynomial before applying normalization or bilinear estimates. -/
noncomputable section
open Set
namespace AcceleratedLogConcave.Analysis.PolynomialEnvelope

theorem exists_common_finite_polynomial_bound
    {ι X : Type*} [Fintype ι] {s : Set X} {R : X → ℝ} {f : ι → X → ℝ}
    (hR : ∀ x ∈ s, 1 ≤ R x)
    (hf : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ x ∈ s, f i x ≤ C * R x ^ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N : ℕ, ∀ i, ∀ x ∈ s, f i x ≤ C * R x ^ N := by
  classical
  choose C hC N hbound using hf
  let A : ℝ := 1 + ∑ i, C i
  let M : ℕ := ∑ i, N i
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hC i)
  refine ⟨A, hA, M, ?_⟩
  intro i x hx
  have hCi : C i ≤ A :=
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hNi : N i ≤ M :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
  exact (hbound i x hx).trans
    (mul_le_mul hCi (pow_le_pow_right₀ (hR x hx) hNi)
      (pow_nonneg (zero_le_one.trans (hR x hx)) _) (zero_le_one.trans hA))

end AcceleratedLogConcave.Analysis.PolynomialEnvelope
