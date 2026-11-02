import AcceleratedLogConcave.Conditional.Tilt.PosteriorLinearTilt
import AcceleratedLogConcave.Conditional.Flow.ExtendedState

/-! All actual scaled jets as derivatives of the normalized linear-tilt
expectation under the fixed actual conditional law. Probability time zero is
included: only the strictly positive conditional variance is inverted. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (d : PositiveVarianceFlowData E)

def conditionalTiltMean (t : ℝ) (y θ : E) : E :=
  (Appell.laplace (conditionalLaw d.F d.x d.r t y) (fun _ => (1 : ℝ)) θ)⁻¹ •
    Appell.laplace (conditionalLaw d.F d.x d.r t y)
      (primitiveObservable d.F d.x d.r) θ

theorem conditionalTiltMean_eq_shift {t : ℝ} (ht : -1 < t ∧ t < 1) (y θ : E) :
    d.conditionalTiltMean t y θ =
      ∫ z, primitiveObservable d.F d.x d.r z ∂Gibbs.heatPosterior
        (primitivePotential d.F d.x d.r) (conditionalVariance t)
        (t • y + conditionalVariance t • θ) := by
  exact (Tilt.integral_heatPosterior_shift_eq_laplace_ratio
    (contDiff_primitivePotential d.hF d.x d.r) (le_refl 0)
    (conditionalVariance_pos ht.1 ht.2)
    (by simpa using primitivePotential_hessian_nonneg d.hF d.hlo d.x d.r)
    (primitiveObservable d.F d.x d.r) (t • y) θ).symm

/-- Exact all-order bridge to the fixed-law Laplace ratio. The only inverse
is variance^-q; there is no inverse probability time. -/
theorem scaledJet_eq_inv_variance_smul_tiltMeanJet (q : ℕ)
    {t : ℝ} (ht : -1 < t ∧ t < 1) (y : E) :
    scaledJet q d.F d.x d.r t y =
      (conditionalVariance t ^ q)⁻¹ •
        iteratedFDeriv ℝ q (d.conditionalTiltMean t y) 0 := by
  let N : E → E := fun c => ∫ z, primitiveObservable d.F d.x d.r z
    ∂Gibbs.heatPosterior (primitivePotential d.F d.x d.r) (conditionalVariance t) c
  have hN : ContDiff ℝ ∞ N :=
    Tilt.contDiff_integral_heatPosterior (contDiff_primitivePotential d.hF d.x d.r)
      (le_refl 0) (conditionalVariance_pos ht.1 ht.2)
      (by simpa using primitivePotential_hessian_nonneg d.hF d.hlo d.x d.r)
      (continuous_primitiveObservable d.hF d.x d.r)
      (‖gradient d.F 0‖ + |d.ell| * ‖d.x‖) (|d.ell| * |d.r|) 1
      (by simpa only [pow_one] using
        norm_primitiveObservable_le_affine d.hF d.hlo d.hhi d.x d.r)
  have he : d.conditionalTiltMean t y =
      fun θ => N (t • y + conditionalVariance t • θ) := by
    funext θ
    exact d.conditionalTiltMean_eq_shift ht y θ
  rw [he]
  have hc : ContDiff ℝ q (fun u => N (t • y+u)) :=
    (hN.comp (contDiff_const.add contDiff_id)).of_le (by simp)
  have hh := congrFun (iteratedFDeriv_comp_const_smul (conditionalVariance t) hc) 0
  simp only [smul_zero, iteratedFDeriv_comp_add_left, add_zero] at hh
  rw [hh,inv_smul_smul₀ (pow_ne_zero q (conditionalVariance_pos ht.1 ht.2).ne')]
  rfl

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
