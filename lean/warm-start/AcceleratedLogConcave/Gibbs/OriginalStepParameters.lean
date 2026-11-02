import AcceleratedLogConcave.Gibbs.HeatContinuityEquation

/-! Compiled original-data local-family and numerical inputs for the proposed
W05 downstream consumer. This module does NOT import or certify the named
VarianceHeatFamily adapter or the production mixing consumer. -/
noncomputable section
open MeasureTheory Set
namespace AcceleratedLogConcave.Gibbs
open Kinetic.Reheating Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The original Gibbs law is a probability measure, derived rather than
assumed in the proposed downstream consumer. -/
theorem originalGibbs_probability_of_hessian_lower {F : E → ℝ} {κ : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v) :
    IsProbabilityMeasure (volume.tilted (fun x => -F x)) :=
  isProbabilityMeasure_tilted (integrable_exp_neg_of_hessian_lower hF (inv_pos.mpr hκ) hlo)

/-- The actual already-compiled local heat family at A = 2h². No residual
analytic record is an input; the separate named variance family is not used. -/
def originalStepLocal {F : E → ℝ} {κ h R : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hh0 : 0 < h) (hR : 2 * h ^ 2 < R)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ‖v‖ ^ 2) :
    LocalReferencePoissonFamily E (3 * (2 * h ^ 2) / 4) R :=
  (originalHeatEvolutionData_of_hessian_lower hF (inv_pos.mpr hκ)
    (by positivity : 0 < 2 * h ^ 2) hlo).toLocal hF hκ (by positivity) hR hlo hup

/-- Exact common lower witness on the executed interval, not the larger R-envelope. -/
theorem originalStepLocal_lower_eq {F : E → ℝ} {κ h R : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hh0 : 0 < h) (hR : 2 * h ^ 2 < R)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ‖v‖ ^ 2)
    (v : ℝ) (hv : v ∈ Icc (3 * (2 * h ^ 2) / 4) (2 * h ^ 2)) :
    (originalStepLocal hF hκ hh0 hR hlo hup).lower v = (κ + 2 * h ^ 2)⁻¹ :=
  OriginalHeatEvolutionData.toLocal_lower_eq _ hF hκ (by positivity) hR hlo hup v hv

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E] in
/-- Reverse-clock variances stay in the actual executed interval. -/
theorem original_step_clock_variance_mem {h ρ : ℝ} (hh0 : 0 < h)
    (hρ : ρ ∈ Icc (0 : ℝ) (1/2)) :
    (2 * h ^ 2) * (1 - ρ ^ 2) ∈ Icc (3 * (2 * h ^ 2) / 4) (2 * h ^ 2) := by
  have hsq : ρ ^ 2 ≤ 1/4 := by nlinarith [hρ.1, hρ.2]
  have hA : 0 ≤ 2 * h ^ 2 := by positivity
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hsq hA]
  · nlinarith [mul_nonneg hA (sq_nonneg ρ)]

/-- The actual local family has the same original-data curvature at every
executed reverse clock, including both clock endpoints. -/
theorem originalStepLocal_clock_lower_eq {F : E → ℝ} {κ h R : ℝ}
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hh0 : 0 < h) (hR : 2 * h ^ 2 < R)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ‖v‖ ^ 2)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) (1/2)) :
    (originalStepLocal hF hκ hh0 hR hlo hup).lower ((2 * h ^ 2) * (1 - ρ ^ 2)) =
      (κ + 2 * h ^ 2)⁻¹ :=
  originalStepLocal_lower_eq hF hκ hh0 hR hlo hup _ (original_step_clock_variance_mem hh0 hρ)

end AcceleratedLogConcave.Gibbs

namespace AcceleratedLogConcave.Gibbs
/-- Positivity of the exact source curvature; no upper admissibility is inferred. -/
theorem original_step_curvature_pos {κ h : ℝ} (hκ : 0 < κ) :
    0 < (κ + 2 * h ^ 2)⁻¹ := by positivity

/-- The consumer's existing m ≤ 1 gate is precisely this scalar condition.
Positive κ alone does not discharge it, so it remains explicit downstream. -/
theorem original_step_curvature_le_one_iff {κ h : ℝ} (hκ : 0 < κ) :
    (κ + 2 * h ^ 2)⁻¹ ≤ 1 ↔ 1 ≤ κ + 2 * h ^ 2 := by
  exact inv_le_one₀ (by positivity)

/-- Gamma remains sqrt(m)h, exactly the manuscript's h/sqrt(κ+2h²). -/
theorem original_step_gamma_eq (κ h : ℝ) :
    Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h = h / Real.sqrt (κ + 2 * h ^ 2) := by
  rw [Real.sqrt_inv]
  ring
end AcceleratedLogConcave.Gibbs
