import AcceleratedLogConcave.Conditional.Tilt.GaussianCenterDerivative
import AcceleratedLogConcave.Conditional.TiltCalculus

/-! Specialization of the reviewed center-derivative adapter.
The fixed observable is the original gradient at x+r z, not the gradient
of the pulled-back potential. Probability time is never inverted. -/
noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem norm_primitiveObservable_le_polynomial {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (x : E) (r : ℝ) (z : E) :
    ‖primitiveObservable F x r z‖ ≤
      (‖gradient F 0‖ + |L| * ‖x‖ + |L| * |r|) * (1 + ‖z‖) ^ 1 := by
  have hb := norm_primitiveObservable_le_affine hF hlo hhi x r z
  rw [pow_one]
  nlinarith [norm_nonneg (gradient F 0), abs_nonneg L, norm_nonneg x,
    abs_nonneg r, norm_nonneg z,
    mul_nonneg (norm_nonneg (gradient F 0)) (norm_nonneg z),
    mul_nonneg (mul_nonneg (abs_nonneg L) (norm_nonneg x)) (norm_nonneg z)]

/-- Exact identification of the literal division-free first scaled jet on the
whole positive-variance time interval, including time zero. -/
theorem firstScaledJet_eq_naturalDerivative {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (x : E) (r : ℝ) {t : ℝ} (htlo : -1 < t) (hthi : t < 1) (y : E) :
    firstScaledJet F x r t y =
      (conditionalVariance t)⁻¹ •
        (fderiv ℝ (Tilt.normalizedGaussianIntegral (primitivePotential F x r)
          (primitiveObservable F x r))
          ((2 * conditionalVariance t)⁻¹, (t / conditionalVariance t) • y)).comp
          (ContinuousLinearMap.inr ℝ ℝ E) := by
  rw [← fderiv_centerMean_eq_firstScaledJet hF hlo hhi x r htlo hthi y]
  have hd := Tilt.fderiv_heatPosterior_center_eq_natural
    (contDiff_primitivePotential hF x r)
    (primitivePotential_hessian_nonneg hF hlo x r)
    (continuous_primitiveObservable hF x r)
    (show 0 ≤ ‖gradient F 0‖ + |L| * ‖x‖ + |L| * |r| by positivity) 1
    (norm_primitiveObservable_le_polynomial hF hlo hhi x r)
    (conditionalVariance_pos htlo hthi) (t • y)
  simpa only [Tilt.posteriorParameters, div_eq_mul_inv, smul_smul, mul_comm] using hd

end AcceleratedLogConcave.Conditional
