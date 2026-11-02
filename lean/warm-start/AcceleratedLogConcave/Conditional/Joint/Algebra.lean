import AcceleratedLogConcave.Conditional.Definitions

/-! # Gaussian square completion at probability time zero

The identities use only the positive variance `1 - ρ²`, and never divide by ρ.
-/

noncomputable section
namespace AcceleratedLogConcave.Conditional
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The joint quadratic is symmetric after extracting the standard Gaussian marginal. -/
theorem conditional_quadratic_completion (ρ : ℝ) (hv : conditionalVariance ρ ≠ 0)
    (z y : E) :
    ‖z‖ ^ 2 / 2 + ‖y - ρ • z‖ ^ 2 / (2 * conditionalVariance ρ) =
      ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ) + ‖y‖ ^ 2 / 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right,
    real_inner_smul_right, real_inner_comm y z, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, sq_abs, mul_pow]
  unfold conditionalVariance at *
  field_simp
  ring

/-- Exponential form of Gaussian square completion, including ρ = 0. -/
theorem conditional_exponent_completion (B : E → ℝ) (ρ : ℝ)
    (hv : conditionalVariance ρ ≠ 0) (z y : E) :
    -(B z + ‖z‖ ^ 2 / 2) +
        (-‖y - ρ • z‖ ^ 2 / (2 * conditionalVariance ρ)) =
      -(B z + ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ)) +
        (-‖y‖ ^ 2 / 2) := by
  have h := conditional_quadratic_completion ρ hv z y
  linear_combination -h

end AcceleratedLogConcave.Conditional
