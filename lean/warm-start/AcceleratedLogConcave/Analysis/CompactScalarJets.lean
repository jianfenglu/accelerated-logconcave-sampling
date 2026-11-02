import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! compact-time jet supplier. Compactness is used only in the
scalar coefficient's time argument. The input of the linear pullback remains
unrestricted in every other coordinate. No rational derivative formula or
compactness of an unrestricted space-time slab is assumed. -/
noncomputable section
open Set Function
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.CompactScalarJets

variable {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A smooth time coefficient has uniform finite jets on a compact subset of
its open time domain, after any norm-at-most-one linear time projection. -/
theorem exists_uniform_jet_comp_linear_bound
    {T S : Set ℝ} (hT : IsOpen T) (hS : IsCompact S) (hST : S ⊆ T)
    {φ : ℝ → G} (hφ : ContDiffOn ℝ ∞ φ T)
    (L : P →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, L p ∈ S →
      ‖iteratedFDerivWithin ℝ n (φ ∘ L) (L ⁻¹' T) p‖ ≤ C := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn
    ((hφ.continuousOn_iteratedFDerivWithin (by simp : (n : ℕ∞ω) ≤ ∞)
      hT.uniqueDiffOn).mono hST)
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro p hp
  rw [L.iteratedFDerivWithin_comp_right hφ hT.uniqueDiffOn
    (hT.preimage L.continuous).uniqueDiffOn (hST hp) (by simp : (n : ℕ∞ω) ≤ ∞)]
  have hn : ‖L‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg L) hL
  calc
    _ ≤ ‖iteratedFDerivWithin ℝ n φ T (L p)‖ * ‖L‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDerivWithin ℝ n φ T (L p)).norm_compContinuousLinearMap_le
          (fun _ : Fin n => L)
    _ ≤ ‖iteratedFDerivWithin ℝ n φ T (L p)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hn
    _ ≤ C := hC (L p) hp
    _ ≤ |C| := le_abs_self C

end AcceleratedLogConcave.Analysis.CompactScalarJets
