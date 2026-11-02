import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Finite-order normalized derivative bounds at a fixed normalization point.
The caller freezes the partition value at p as a scalar constant before
forming S and G. Only their derivatives through the requested order enter.
This is a qualitative finite polynomial bound, not a sharp factorial budget. -/
noncomputable section
open Set
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.NormalizedJetBound

/-- The scalar inverse derivatives at the normalized value one. -/
theorem norm_iteratedFDerivWithin_inv_one (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (fun x : ℝ => x⁻¹) (Ioi 0) 1‖ = n.factorial := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have he := (iteratedDerivWithin_one_div (𝕜 := ℝ) n (s := Ioi 0) isOpen_Ioi)
    (by norm_num : (1 : ℝ) ∈ Ioi 0)
  simpa [one_div, norm_mul, norm_pow] using congrArg norm he

variable {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- If the partition has been rescaled by the constant S(p) so that its value
at p is one, polynomial bounds for the rescaled raw derivatives remain
polynomial after normalization. No derivative bound of order n+1 is assumed. -/
theorem norm_iteratedFDerivWithin_normalized_le
    {s : Set P} (hs : UniqueDiffOn ℝ s) {p : P} (hp : p ∈ s)
    {S : P → ℝ} {g : P → G}
    (hS : ContDiffOn ℝ ∞ S s) (hg : ContDiffOn ℝ ∞ g s)
    (hpositive : ∀ q ∈ s, 0 < S q) (hunit : S p = 1)
    (n : ℕ) {D : ℝ} (hD : 1 ≤ D)
    (hSbound : ∀ i ≤ n, ‖iteratedFDerivWithin ℝ i S s p‖ ≤ D)
    (hgbound : ∀ i ≤ n, ‖iteratedFDerivWithin ℝ i g s p‖ ≤ D) :
    ‖iteratedFDerivWithin ℝ n (fun q => (S q)⁻¹ • g q) s p‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ((i.factorial : ℝ) * (n.factorial : ℝ) * D ^ i) * D := by
  have hinv : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) (Ioi 0) :=
    contDiffOn_id.inv (fun x hx => ne_of_gt hx)
  have hSinv : ContDiffOn ℝ ∞ (fun q => (S q)⁻¹) s :=
    hS.inv (fun q hq => (hpositive q hq).ne')
  have hInvBound (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i (fun q => (S q)⁻¹) s p‖ ≤
        (i.factorial : ℝ) * (n.factorial : ℝ) * D ^ i := by
    apply norm_iteratedFDerivWithin_comp_le hinv hS (by simp)
      (isOpen_Ioi.uniqueDiffOn) hs (fun q hq => hpositive q hq) hp
    · intro j hj
      rw [hunit, norm_iteratedFDerivWithin_inv_one]
      exact_mod_cast Nat.factorial_le (hj.trans hi)
    · intro j hj hj'
      exact (hSbound j (hj'.trans hi)).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hD hj)
  apply (norm_iteratedFDerivWithin_smul_le hSinv hg hs hp (by simp : (n : ℕ∞ω) ≤ ∞)).trans
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsub : n - i ≤ n := Nat.sub_le n i
  have hInv := hInvBound i hin
  have hg' := hgbound (n - i) hsub
  gcongr

/-- Constant rescaling commutes with every derivative in the finite ladder.
The normalization point is fixed before the function is differentiated. -/
theorem norm_iteratedFDerivWithin_const_smul
    {s : Set P} (hs : UniqueDiffOn ℝ s) {p : P} (hp : p ∈ s)
    {g : P → G} (hg : ContDiffOn ℝ ∞ g s) (n : ℕ) (c : ℝ) :
    ‖iteratedFDerivWithin ℝ n (fun q => c • g q) s p‖ =
      |c| * ‖iteratedFDerivWithin ℝ n g s p‖ := by
  rw [show (fun q => c • g q) = c • g from rfl,
    iteratedFDerivWithin_const_smul_apply ((hg p hp).of_le (by simp)) hs hp,
    norm_smul, Real.norm_eq_abs]

/-- A ratio can be normalized at the evaluation point without differentiating
the partition value at that point. This supplies the explicit cancellation
needed before applying the scalar-inverse bound at one. -/
theorem norm_iteratedFDerivWithin_ratio_le
    {s : Set P} (hs : UniqueDiffOn ℝ s) {p : P} (hp : p ∈ s)
    {S : P → ℝ} {g : P → G}
    (hS : ContDiffOn ℝ ∞ S s) (hg : ContDiffOn ℝ ∞ g s)
    (hpositive : ∀ q ∈ s, 0 < S q)
    (n : ℕ) {D : ℝ} (hD : 1 ≤ D)
    (hSbound : ∀ i ≤ n, (S p)⁻¹ * ‖iteratedFDerivWithin ℝ i S s p‖ ≤ D)
    (hgbound : ∀ i ≤ n, (S p)⁻¹ * ‖iteratedFDerivWithin ℝ i g s p‖ ≤ D) :
    ‖iteratedFDerivWithin ℝ n (fun q => (S q)⁻¹ • g q) s p‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ((i.factorial : ℝ) * (n.factorial : ℝ) * D ^ i) * D := by
  let c : ℝ := (S p)⁻¹
  have hc : 0 < c := inv_pos.mpr (hpositive p hp)
  have heq : (fun q => (S q)⁻¹ • g q) =
      (fun q => (c • S q)⁻¹ • (c • g q)) := by
    funext q
    simp only [smul_eq_mul, mul_inv_rev, smul_smul]
    rw [mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
  rw [heq]
  apply norm_iteratedFDerivWithin_normalized_le hs hp (hS.const_smul c)
    (hg.const_smul c) (fun q hq => mul_pos hc (hpositive q hq))
    (by exact inv_mul_cancel₀ (hpositive p hp).ne') n hD
  · intro i hi
    rw [norm_iteratedFDerivWithin_const_smul hs hp hS i c, abs_of_pos hc]
    exact hSbound i hi
  · intro i hi
    rw [norm_iteratedFDerivWithin_const_smul hs hp hg i c, abs_of_pos hc]
    exact hgbound i hi

/-- The finite normalization polynomial is bounded by a single monomial.
Its coefficient is retained as a finite sum; no sharp budget is asserted. -/
theorem normalizedJetSum_le (n : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ((i.factorial : ℝ) * (n.factorial : ℝ) * D ^ i) * D) ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (i.factorial : ℝ) * (n.factorial : ℝ)) * D ^ (n + 1) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  calc
    _ = ((n.choose i : ℝ) * (i.factorial : ℝ) * (n.factorial : ℝ)) * D ^ (i + 1) := by
      rw [pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD (Nat.add_le_add_right hin 1)) (by positivity)

end AcceleratedLogConcave.Analysis.NormalizedJetBound
