import AcceleratedLogConcave.Conditional.JointLaw
import AcceleratedLogConcave.Gibbs.PrimitiveMoments
import AcceleratedLogConcave.Kinetic.ReferenceFlow
import AcceleratedLogConcave.Analysis.PolynomialLp

/-! Polynomial moments of the actual stationary phase.
All position moments are derived from the Gaussian-regularized primitive law;
only the original C² convexity hypotheses occur at this supplier boundary. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The actual base law has every finite position moment. -/
theorem baseLaw_integrable_norm_pow {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r : ℝ) (n : ℕ) :
    Integrable (fun z : E => ‖z‖ ^ n) (baseLaw F x r) :=
  Gibbs.primitive_integrable_norm_pow hF hlo x r n

/-- Moments are transferred through the literal Gaussian-product interpolation
map, at every real probability parameter. No independently specified law is used. -/
theorem interpolationLaw_integrable_norm_pow {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (n : ℕ) :
    Integrable (fun z : E => ‖z‖ ^ n) (interpolationLaw F x r ρ) := by
  let := baseLaw_isProbabilityMeasure hF hlo x r
  have hg : Integrable (fun z : E => ‖z‖ ^ n) (stdGaussian E) := by
    simpa only [id_eq] using
      (IsGaussian.memLp_id (stdGaussian E) n (by simp)).integrable_norm_pow'
  exact Analysis.PolynomialLp.integrable_norm_pow_map_smul_add n ρ
    (Real.sqrt (conditionalVariance ρ)) (baseLaw_integrable_norm_pow hF hlo x r n) hg

/-- Polynomial position growth times Gaussian momentum is genuinely in L²
under the exact coupled stationary phase law. -/
theorem coupledInterpolation_polynomial_momentum_memLp
    {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (N : ℕ) (C : ℝ) :
    MemLp (fun z : Kinetic.CoupledPhase E => C * (1 + ‖z.fst‖) ^ N * ‖z.snd‖)
      2 (Kinetic.coupledPhaseMeasure (interpolationLaw F x r ρ)) := by
  let := interpolationLaw_isProbabilityMeasure hF hlo x r ρ
  unfold Kinetic.coupledPhaseMeasure
  apply (memLp_map_measure_iff (by fun_prop) (by fun_prop)).mpr
  exact Analysis.PolynomialLp.memLp_two_polynomial_momentum N C
    (interpolationLaw_integrable_norm_pow hF hlo x r ρ (2 * N))
    (IsGaussian.memLp_two_id (μ := stdGaussian E)).norm

end AcceleratedLogConcave.Conditional
