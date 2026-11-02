import AcceleratedLogConcave.Analysis.PolynomialEnvelope
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! finite-order composition bookkeeping. The uniform outer
estimates are required at the actual inner image. No compactness of an
unrestricted space-time slab or quantitative derivative bound above the requested order is used. -/
noncomputable section
open Set Function
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.PolynomialEnvelope

variable {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_polynomial_comp_jet_bound
    {U S : Set P} {T : Set E} (hU : UniqueDiffOn ℝ U)
    (hT : UniqueDiffOn ℝ T) (hSU : S ⊆ U)
    {f : P → E} {g : E → G}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g T)
    (hmap : MapsTo f U T) {R : P → ℝ} (hR : ∀ p ∈ S, 1 ≤ R p)
    (n : ℕ)
    (houter : ∀ i ≤ n, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p ∈ S,
      ‖iteratedFDerivWithin ℝ i g T (f p)‖ ≤ C * R p ^ N)
    (hinner : ∀ i ≤ n, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p ∈ S,
      ‖iteratedFDerivWithin ℝ i f U p‖ ≤ C * R p ^ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p ∈ S,
      ‖iteratedFDerivWithin ℝ n (g ∘ f) U p‖ ≤ C * R p ^ N := by
  let a : (Fin (n + 1) ⊕ Fin (n + 1)) → P → ℝ :=
    Sum.elim
      (fun i p => ‖iteratedFDerivWithin ℝ i.val g T (f p)‖)
      (fun i p => ‖iteratedFDerivWithin ℝ i.val f U p‖)
  have ha : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p ∈ S, a i p ≤ C * R p ^ N := by
    intro i
    rcases i with i | i
    · exact houter i.val (Nat.lt_succ_iff.mp i.isLt)
    · exact hinner i.val (Nat.lt_succ_iff.mp i.isLt)
  obtain ⟨A, hA, N, hbound⟩ := exists_common_finite_polynomial_bound hR ha
  refine ⟨(n.factorial : ℝ) * A ^ (n + 1),
    mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hA) _), N * (n + 1), ?_⟩
  intro p hp
  have hD : 1 ≤ A * R p ^ N :=
    one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ (hR p hp))
  have hcomp : ‖iteratedFDerivWithin ℝ n (g ∘ f) U p‖ ≤
      (n.factorial : ℝ) * (A * R p ^ N) * (A * R p ^ N) ^ n := by
    apply norm_iteratedFDerivWithin_comp_le hg hf (by simp) hT hU hmap (hSU hp)
    · intro i hi
      exact hbound (Sum.inl ⟨i, Nat.lt_succ_of_le hi⟩) p hp
    · intro i hi hi'
      exact (hbound (Sum.inr ⟨i, Nat.lt_succ_of_le hi'⟩) p hp).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hD hi)
  calc
    _ ≤ (n.factorial : ℝ) * (A * R p ^ N) * (A * R p ^ N) ^ n := hcomp
    _ = ((n.factorial : ℝ) * A ^ (n + 1)) * R p ^ (N * (n + 1)) := by
      rw [mul_assoc, ← pow_succ', mul_pow, ← pow_mul, mul_assoc]

end AcceleratedLogConcave.Analysis.PolynomialEnvelope
