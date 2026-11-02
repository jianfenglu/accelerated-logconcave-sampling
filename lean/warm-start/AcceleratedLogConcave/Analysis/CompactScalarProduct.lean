import AcceleratedLogConcave.Analysis.CompactScalarJets
import AcceleratedLogConcave.Analysis.ODEJetPolynomial

/-! compact scalar-time coefficient times a linear spatial map.
Only scalar derivative bounds through the requested order enter the finite
binomial estimate. The other coordinates remain unrestricted. -/
noncomputable section
open Set Function
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.CompactScalarJets

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_linear_jet_scalar_times_linear_bound
    {T S : Set ℝ} (hT : IsOpen T) (hS : IsCompact S) (hST : S ⊆ T)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ ∞ φ T)
    (L : P →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (M : P →L[ℝ] E) (hM : ‖M‖ ≤ 1) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, L p ∈ S →
      ‖iteratedFDerivWithin ℝ n (fun q => φ (L q) • M q) (L ⁻¹' T) p‖ ≤
        C * (1 + ‖p‖) := by
  let slab : Set P := L ⁻¹' S
  let f (i : Fin (n + 1)) (p : P) :=
    ‖iteratedFDerivWithin ℝ i.val (φ ∘ L) (L ⁻¹' T) p‖
  have hf : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p ∈ slab, f i p ≤ C * (1 : ℝ) ^ N := by
    intro i
    obtain ⟨C, hC, hb⟩ := exists_uniform_jet_comp_linear_bound hT hS hST hφ L hL i.val
    refine ⟨C, hC, 0, ?_⟩
    intro p hp
    simpa only [pow_zero, mul_one] using hb p hp
  obtain ⟨C, hC, N, hbound⟩ := PolynomialEnvelope.exists_common_finite_polynomial_bound
    (s := slab) (R := fun _ => (1 : ℝ)) (fun _ _ => le_rfl) hf
  let A : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A * C, mul_nonneg hA (zero_le_one.trans hC), ?_⟩
  intro p hp
  have hU : UniqueDiffOn ℝ (L ⁻¹' T) := (hT.preimage L.continuous).uniqueDiffOn
  have hpU : p ∈ L ⁻¹' T := hST hp
  have hφL : ContDiffOn ℝ ∞ (φ ∘ L) (L ⁻¹' T) :=
    hφ.comp_continuousLinearMap L
  have hraw := norm_iteratedFDerivWithin_smul_le hφL M.contDiff.contDiffOn
    hU hpU (by simp : (n : ℕ∞ω) ≤ ∞)
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (φ ∘ L) (L ⁻¹' T) p‖ *
        ‖iteratedFDerivWithin ℝ (n - i) M (L ⁻¹' T) p‖ := hraw
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C * (1 + ‖p‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hs : ‖iteratedFDerivWithin ℝ i (φ ∘ L) (L ⁻¹' T) p‖ ≤ C := by
        simpa only [f, one_pow, mul_one] using hbound ⟨i, hi'⟩ p hp
      have hm : ‖iteratedFDerivWithin ℝ (n - i) M (L ⁻¹' T) p‖ ≤ 1 + ‖p‖ := by
        apply (ODEJet.norm_iteratedFDerivWithin_linear_le hU hpU M (n - i)).trans
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hM (show 0 ≤ 1 + ‖p‖ by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hm
        (norm_nonneg _) (mul_nonneg (by positivity) (zero_le_one.trans hC))
    _ = (A * C) * (1 + ‖p‖) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]

end AcceleratedLogConcave.Analysis.CompactScalarJets
