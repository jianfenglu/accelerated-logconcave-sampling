import AcceleratedLogConcave.External.OAI.GlobalODE
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Backward differentiation of the actual linearized ODE -/

noncomputable section
open Set Function
open scoped Topology NNReal

namespace OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
  {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)

/-- A total definition of the inverse fundamental matrix. On the construction
interval this is the fundamental matrix with its two times exchanged. -/
def inverseFundamental (s : Icc a b) (t : ℝ) : E →L[ℝ] E :=
  Ring.inverse (fundamental s hA hK t)

theorem inverseFundamental_eq (s t : Icc a b) :
    inverseFundamental hA hK s t = fundamental t hA hK s := by
  let u := (fundamentalEquiv hA hK s t).toUnit
  change Ring.inverse (u : E →L[ℝ] E) = _
  rw [Ring.inverse_unit]
  rfl

/-- Inverse differentiation gives the right multiplication order required by
the backward Jacobian equation. This includes both interval endpoints. -/
theorem inverseFundamental_deriv (s : Icc a b) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (inverseFundamental hA hK s)
      (-(inverseFundamental hA hK s t).comp (A t)) (Icc a b) t := by
  let u := (fundamentalEquiv hA hK s ⟨t, ht⟩).toUnit
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).comp_hasDerivWithinAt t
    (fundamental_deriv s hA hK t ht)
  have he : (↑u⁻¹ : E →L[ℝ] E) = inverseFundamental hA hK s t := by
    change fundamental ⟨t, ht⟩ hA hK s = _
    exact (inverseFundamental_eq hA hK s ⟨t, ht⟩).symm
  convert hi using 1
  · rfl
  · change -(inverseFundamental hA hK s t).comp (A t) =
      -(↑u⁻¹ * ((A t).comp (fundamental s hA hK t)) * ↑u⁻¹)
    rw [he, inverseFundamental_eq hA hK s ⟨t, ht⟩]
    ext v
    simp only [neg_apply, ContinuousLinearMap.comp_apply,
      mul_apply_eq_comp]
    rw [fundamental_cocycle hA hK ⟨t, ht⟩ s ⟨t, ht⟩ v, fundamental_apply_initial]

end OAI.LogConcaveSampling.GlobalODE
