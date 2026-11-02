import AcceleratedLogConcave.Conditional.PrimitivePullback

/-! The actual conditional position mean and probability velocity, derived by
posterior integration by parts under the original C² Hessian assumptions. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace AcceleratedLogConcave.Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Conditional integration by parts, including probability time zero. -/
theorem conditionalPositionMean_eq {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    conditionalPositionMean F x r ρ y = ρ • y -
      (conditionalVariance ρ * r) • conditionalMean F x r ρ y := by
  have ht := conditionalVariance_pos hρlo hρhi
  have hB := contDiff_primitivePotential hF x r
  have hBlo := primitivePotential_hessian_nonneg hF hlo x r
  have hBup (z a : E) : fderiv ℝ (fderiv ℝ (primitivePotential F x r)) z a a ≤
      (r ^ 2 * ell) * ‖a‖ ^ 2 := by
    rw [hessian_primitivePotential hF]
    calc
      _ ≤ r ^ 2 * (ell * ‖a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hup _ _) (sq_nonneg r)
      _ = _ := by ring
  have h := Gibbs.integral_gradient_normalizedPosteriorKernel_eq hB
    (m := 0) (by norm_num) ht (by simpa using hBlo) hBup (ρ • y)
  change (∫ z, gradient (primitivePotential F x r) z ∂conditionalLaw F x r ρ y) =
    (conditionalVariance ρ)⁻¹ •
      (ρ • y - conditionalPositionMean F x r ρ y) at h
  simp_rw [gradient_primitivePotential] at h
  rw [integral_smul] at h
  change r • conditionalMean F x r ρ y = _ at h
  have hs := congrArg (fun z : E => conditionalVariance ρ • z) h
  simp only [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at hs
  apply eq_sub_iff_add_eq.mpr
  rw [hs]
  abel

/-- The conditional velocity of `ρ Z + √(1-ρ²) N` equals the actual mean
drift, without dividing by probability time. -/
theorem conditionalVelocity_eq_probabilityVelocity
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    (conditionalVariance ρ)⁻¹ • (conditionalPositionMean F x r ρ y - ρ • y) =
      probabilityVelocity F x r ρ y := by
  have ht := conditionalVariance_pos hρlo hρhi
  rw [conditionalPositionMean_eq hF hlo hup x r hρlo hρhi]
  have hsub (A B : E) : A - B - A = -B := by abel
  rw [hsub, smul_neg, smul_smul]
  simp only [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul,
    probabilityVelocity, neg_smul]

/-- Averaging a space-time linear test against the actual posterior replaces
the interpolation velocity by its conditional mean. -/
theorem integral_conditional_spaceTime_velocity
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1)
    (y : E) (A : (ℝ × E) →L[ℝ] ℝ) :
    (∫ z, A (1, (conditionalVariance ρ)⁻¹ • (z - ρ • y))
      ∂conditionalLaw F x r ρ y) = A (1, probabilityVelocity F x r ρ y) := by
  let := conditionalLaw_isProbabilityMeasure hF hlo x r hρlo hρhi y
  have hz : Integrable (fun z : E => z) (conditionalLaw F x r ρ y) :=
    Gibbs.integrable_id_heatPosterior (contDiff_primitivePotential hF x r)
      (m := 0) le_rfl (conditionalVariance_pos hρlo hρhi)
      (by simpa using primitivePotential_hessian_nonneg hF hlo x r) (ρ • y)
  have hv : Integrable (fun z : E => (conditionalVariance ρ)⁻¹ • (z - ρ • y))
      (conditionalLaw F x r ρ y) :=
    (hz.sub (integrable_const (ρ • y))).smul (conditionalVariance ρ)⁻¹
  rw [A.integral_comp_comm ((integrable_const (1 : ℝ)).prodMk hv),
    integral_pair (integrable_const (1 : ℝ)) hv, integral_const,
    integral_smul, integral_sub hz (integrable_const (ρ • y)), integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul, one_smul]
  change A (1, (conditionalVariance ρ)⁻¹ •
    (conditionalPositionMean F x r ρ y - ρ • y)) = _
  rw [conditionalVelocity_eq_probabilityVelocity hF hlo hup x r hρlo hρhi]

end AcceleratedLogConcave.Conditional
