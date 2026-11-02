import AcceleratedLogConcave.Conditional.Tilt.HeatIntegral
import AcceleratedLogConcave.Conditional.Cumulants

/-! The exact posterior linear-tilt quotient underlying the actual scaled-jet
mixed-cumulant identity. Normalizers are discharged, not assumed. -/
noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.Tilt
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem gaussianIntegral_linearTilt (B : E → ℝ) (g : E → G) (p : ℝ × E) (θ : E) :
    gaussianIntegral B (fun z => Real.exp (inner ℝ θ z) • g z) p =
      gaussianIntegral B g (p.1,p.2+θ) := by
  unfold gaussianIntegral
  congr 1
  funext z
  rw [smul_smul, ← Real.exp_add]
  congr 2
  simp only [gaussianStatistic_apply, inner_add_right, real_inner_comm θ z]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem posteriorParameters_add_center {t : ℝ} (ht : t ≠ 0) (c θ : E) :
    posteriorParameters (t,c+t • θ) =
      ((posteriorParameters (t,c)).1,(posteriorParameters (t,c)).2+θ) := by
  simp [posteriorParameters, smul_add, smul_smul, inv_mul_cancel₀ ht]

/-- A center displacement t θ is exactly the normalized linear tilt θ of the
original posterior, for arbitrary Bochner observable g. -/
theorem integral_heatPosterior_shift_eq_laplace_ratio {B : E → ℝ} {m t : ℝ}
    (hB : ContDiff ℝ 2 B) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z v v)
    (g : E → G) (c θ : E) :
    (∫ z, g z ∂Gibbs.heatPosterior B t (c+t • θ)) =
      (Appell.laplace (Gibbs.heatPosterior B t c) (fun _ => (1 : ℝ)) θ)⁻¹ •
        Appell.laplace (Gibbs.heatPosterior B t c) g θ := by
  let p := posteriorParameters (t,c)
  have hz : gaussianIntegral B (fun _ => (1 : ℝ)) p ≠ 0 := by
    let := Gibbs.heatPosterior_isProbabilityMeasure hB hm ht hlo c
    have hh := integral_heatPosterior_eq_normalizedGaussianIntegral hB hm ht hlo
      (fun _ => (1 : ℝ)) c
    intro h
    simp [normalizedGaussianIntegral, p, h] at hh
  have hg := integral_heatPosterior_eq_normalizedGaussianIntegral hB hm ht hlo
    (fun z => Real.exp (inner ℝ θ z) • g z) c
  have h1 := integral_heatPosterior_eq_normalizedGaussianIntegral hB hm ht hlo
    (fun z => Real.exp (inner ℝ θ z) • (1 : ℝ)) c
  rw [integral_heatPosterior_eq_normalizedGaussianIntegral hB hm ht hlo,
    posteriorParameters_add_center ht.ne']
  change _ = (∫ z, Real.exp (inner ℝ θ z) • (1 : ℝ) ∂Gibbs.heatPosterior B t c)⁻¹ •
    (∫ z, Real.exp (inner ℝ θ z) • g z ∂Gibbs.heatPosterior B t c)
  rw [hg,h1]
  simp only [normalizedGaussianIntegral]
  rw [gaussianIntegral_linearTilt,gaussianIntegral_linearTilt]
  simp only [smul_eq_mul,mul_inv_rev,inv_inv,smul_smul]
  rw [mul_assoc, mul_inv_cancel₀ hz, mul_one]

end AcceleratedLogConcave.Conditional.Tilt
