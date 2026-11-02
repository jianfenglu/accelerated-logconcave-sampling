import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! fixed-direction derivative restriction. This keeps the exact
one-order shift needed by the natural-parameter first-jet adapter. -/
noncomputable section
open Set Function
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.DerivativeRestriction
variable {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Restrict a derivative on P along one fixed continuous linear input map. -/
def restrictDerivative (L : E →L[ℝ] P) : (P →L[ℝ] G) →L[ℝ] (E →L[ℝ] G) :=
  (ContinuousLinearMap.compL ℝ E P G).flip L

theorem norm_restrictDerivative_le (L : E →L[ℝ] P) :
    ‖restrictDerivative (G := G) L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro A
  change ‖A.comp L‖ ≤ ‖L‖ * ‖A‖
  simpa only [mul_comm] using A.opNorm_comp_le L

/-- Taking n derivatives after restricting DQ consumes exactly Q through n+1,
with no next-order bound. Differentiation uses the same fixed domain U. -/
theorem norm_iteratedFDerivWithin_restrict_fderivWithin_le
    {U : Set P} (hU : UniqueDiffOn ℝ U) {Q : P → G}
    (hQ : ContDiffOn ℝ ∞ Q U) (L : E →L[ℝ] P)
    (n : ℕ) {p : P} (hp : p ∈ U) :
    ‖iteratedFDerivWithin ℝ n
      (fun q => (fderivWithin ℝ Q U q).comp L) U p‖ ≤
      ‖L‖ * ‖iteratedFDerivWithin ℝ (n + 1) Q U p‖ := by
  have hD : ContDiffOn ℝ ∞ (fderivWithin ℝ Q U) U :=
    hQ.fderivWithin hU (by simp)
  have hb := (restrictDerivative (G := G) L).norm_iteratedFDerivWithin_comp_left
    (hD p hp) hU hp (by simp : (n : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDerivWithin ℝ n
    (fun q => (fderivWithin ℝ Q U q).comp L) U p‖ ≤ _ at hb
  apply hb.trans
  rw [norm_iteratedFDerivWithin_fderivWithin hU hp]
  exact mul_le_mul_of_nonneg_right (norm_restrictDerivative_le L) (norm_nonneg _)

end AcceleratedLogConcave.Analysis.DerivativeRestriction
