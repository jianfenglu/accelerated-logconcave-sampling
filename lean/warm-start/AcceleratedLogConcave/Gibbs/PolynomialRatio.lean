import AcceleratedLogConcave.Gibbs.CenteredQuadratic
import AcceleratedLogConcave.Gibbs.GaussianSandwich

/-! Uniform qualitative polynomial moments from a Hessian sandwich.
The only center dependence retained is through the derivative at the origin.
This is designed for a positive-variance Gaussian-regularized C² potential. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Gibbs
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For fixed strictly positive Hessian bounds, the normalized nth polynomial
moment grows at most polynomially in the derivative at the origin. All
integral, minimizer and centering steps are derived inside the proof. -/
theorem exists_polynomial_ratio_bound_of_hessian_sandwich
    {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : E → ℝ, ContDiff ℝ 2 F →
      (∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) →
      (∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ L * ‖v‖ ^ 2) →
      (∫ u, (1 + ‖u‖) ^ n * Real.exp (-F u)) /
        (∫ u, Real.exp (-F u)) ≤ C * (1 + ‖fderiv ℝ F 0‖) ^ n := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_polynomial_ratio_bound_of_quadratic_sandwich (E := E)
      (by positivity : 0 < m / 2) (by positivity : 0 < L / 2) n
  let A := 1 + (m / 2)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C * A ^ n, mul_nonneg hC (pow_nonneg hA n), ?_⟩
  intro F hF hlo hhi
  obtain ⟨z, _, _, hz, hquad⟩ := exists_minimizer_quadratic_sandwich hF hm hlo hhi
  have hnorm : 1 + ‖z‖ ≤ A * (1 + ‖fderiv ℝ F 0‖) := by
    dsimp [A]
    rw [div_eq_mul_inv] at hz
    nlinarith [norm_nonneg (fderiv ℝ F 0), inv_nonneg.mpr (by positivity : 0 ≤ m / 2)]
  rw [normalized_exp_ratio_eq_centered F (fun u => (1 + ‖u‖) ^ n) z]
  calc
    _ ≤ C * (1 + ‖z‖) ^ n :=
      hbound (fun w => F (z + w) - F z)
        ((hF.continuous.comp (continuous_const.add continuous_id)).sub continuous_const)
        (fun w => (hquad w).1) (fun w => (hquad w).2) z
    _ ≤ C * (A * (1 + ‖fderiv ℝ F 0‖)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnorm n) hC
    _ = _ := by rw [mul_pow, mul_assoc]

end AcceleratedLogConcave.Gibbs
