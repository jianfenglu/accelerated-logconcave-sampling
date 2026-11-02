import AcceleratedLogConcave.Conditional.SourcePosteriorAffine
import AcceleratedLogConcave.Conditional.TiltCalculus

/-!
# Physical posterior expectations and joint source coefficient regularity

The observable is the fixed original gradient. Gaussian smoothing therefore
gives all parameter derivatives from the original C² hypotheses. The affine
posterior identity is differentiated in its unrestricted Gaussian center, so
the first scaled jet identity includes probability time zero without division.
-/

noncomputable section
namespace AcceleratedLogConcave.Conditional

open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The physical posterior expectation, with variance `v` and physical center `a`. -/
def physicalHeatMean (F : E → ℝ) (v : ℝ) (a : E) : E :=
  ∫ u, gradient F u ∂Gibbs.heatPosterior F v a

/-- Its actual derivative in the physical center. -/
def physicalHeatMeanCenterDerivative (F : E → ℝ) (v : ℝ) (a : E) : E →L[ℝ] E :=
  fderiv ℝ (physicalHeatMean F v) a

omit [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_originalGradient {F : E → ℝ} (hF : ContDiff ℝ 2 F) :
    Continuous (gradient F) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (hF.continuous_fderiv (by norm_num))

omit [MeasurableSpace E] [BorelSpace E] in
private theorem originalGradient_affine_bound {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2) (u : E) :
    ‖gradient F u‖ ≤ ‖gradient F 0‖ + |L| * ‖u‖ := by
  simpa only [abs_zero, max_eq_right (abs_nonneg L)] using
    Gibbs.norm_gradient_le_affine_of_hessian_bounds hF (m := 0)
      (by simpa using hlo) hhi u

/-- The physical gradient expectation is a genuine Bochner integral. -/
theorem integrable_gradient_heatPosterior {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L v : ℝ} (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hv : 0 < v) (a : E) : Integrable (gradient F) (Gibbs.heatPosterior F v a) := by
  let := Gibbs.heatPosterior_isProbabilityMeasure hF (m := 0) (le_refl 0) hv
    (by simpa using hlo) a
  exact (Gibbs.memLp_two_heatPosterior_of_affine_bound hF (m := 0) (le_refl 0) hv
    (by simpa using hlo) a (continuous_originalGradient hF) ‖gradient F 0‖ |L|
    (originalGradient_affine_bound hF hlo hhi)).integrable (by norm_num)

/-- Actual joint smoothness in positive variance and physical center. -/
theorem contDiffOn_physicalHeatMean {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ physicalHeatMean F p.1 p.2)
      Tilt.gaussianDomain := by
  exact Tilt.contDiffOn_integral_heatPosterior hF (m := 0) (le_refl 0)
    (by simpa using hlo) (continuous_originalGradient hF) ‖gradient F 0‖ |L| 1
    (by simpa only [pow_one] using originalGradient_affine_bound hF hlo hhi)

/-- For a fixed positive variance the physical mean is smooth on all centers. -/
theorem contDiff_physicalHeatMean {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L v : ℝ} (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2) (hv : 0 < v) :
    ContDiff ℝ ∞ (physicalHeatMean F v) := by
  exact Tilt.contDiff_integral_heatPosterior hF (m := 0) (le_refl 0) hv
    (by simpa using hlo) (continuous_originalGradient hF) ‖gradient F 0‖ |L| 1
    (by simpa only [pow_one] using originalGradient_affine_bound hF hlo hhi)

/-- Partial differentiation in the center preserves joint smoothness. -/
theorem contDiffOn_physicalHeatMeanCenterDerivative {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {L : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ physicalHeatMeanCenterDerivative F p.1 p.2)
      Tilt.gaussianDomain := by
  have hs := Tilt.contDiffOn_centerJet_integral_heatPosterior hF
    (m := 0) (le_refl 0) (by simpa using hlo) (continuous_originalGradient hF)
    ‖gradient F 0‖ |L| 1 1
    (by simpa only [pow_one] using originalGradient_affine_bound hF hlo hhi)
  have hc := (continuousMultilinearCurryFin1 ℝ E E).contDiff.comp_contDiffOn hs
  apply hc.congr
  intro p hp
  ext w
  simp [physicalHeatMeanCenterDerivative]
  rfl

/-- The covariance orientation is position functional, gradient output. -/
theorem physicalHeatMeanCenterDerivative_eq_covariance {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {L v : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hv : 0 < v) (a : E) :
    physicalHeatMeanCenterDerivative F v a = v⁻¹ • ∫ u,
      (innerSL ℝ (u - ∫ u, u ∂Gibbs.heatPosterior F v a)).smulRight
        (gradient F u - physicalHeatMean F v a) ∂Gibbs.heatPosterior F v a := by
  exact Tilt.fderiv_integral_heatPosterior_eq_vectorCovariance hF
    (m := 0) (le_refl 0) hv (by simpa using hlo) (continuous_originalGradient hF)
    ‖gradient F 0‖ |L| (originalGradient_affine_bound hF hlo hhi) a

/-- The operator covariance in the derivative formula is Bochner integrable. -/
theorem integrable_physicalHeatMean_covariance {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {L v : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hv : 0 < v) (a : E) :
    Integrable (fun u ↦
      (innerSL ℝ (u - ∫ u, u ∂Gibbs.heatPosterior F v a)).smulRight
        (gradient F u - physicalHeatMean F v a)) (Gibbs.heatPosterior F v a) := by
  exact Tilt.integrable_centered_covariance hF (m := 0) (le_refl 0) hv
    (by simpa using hlo) (continuous_originalGradient hF) ‖gradient F 0‖ |L|
    (originalGradient_affine_bound hF hlo hhi) a _ _

/-- The source conditional mean is the physical mean at the exact affine parameters. -/
theorem conditionalMean_eq_physicalHeatMean {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {r ρ : ℝ} (hr : 0 < r) (hρlo : -1 < ρ) (hρhi : ρ < 1) (c y : E) :
    conditionalMean F c r ρ y =
      physicalHeatMean F (r ^ 2 * conditionalVariance ρ) (c + (r * ρ) • y) :=
  conditionalMean_eq_integral_heatPosterior hF hr hρlo hρhi c y

/-- The first actual scaled jet is `r` times the physical center derivative.
The proof differentiates the affine identity at an arbitrary Gaussian center,
and consequently applies unchanged at `ρ = 0`. -/
theorem firstScaledJet_eq_physicalHeatMeanCenterDerivative {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {L r ρ : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hr : 0 < r) (hρlo : -1 < ρ) (hρhi : ρ < 1) (c y : E) :
    firstScaledJet F c r ρ y =
      r • physicalHeatMeanCenterDerivative F (r ^ 2 * conditionalVariance ρ)
        (c + (r * ρ) • y) := by
  have ht := conditionalVariance_pos hρlo hρhi
  have heq : (fun a ↦ ∫ z, primitiveObservable F c r z ∂
      Gibbs.heatPosterior (primitivePotential F c r) (conditionalVariance ρ) a) =
      fun a ↦ physicalHeatMean F (r ^ 2 * conditionalVariance ρ) (c + r • a) := by
    funext a
    exact integral_primitive_heatPosterior_affine hF.continuous.measurable
      (continuous_originalGradient hF) hr.ne' ht.ne' c a
  have hd := (contDiff_physicalHeatMean hF hlo hhi
    (mul_pos (sq_pos_of_pos hr) ht)).differentiable (by simp)
  have hcomp := (hd (c + r • (ρ • y))).hasFDerivAt.comp (ρ • y)
    (((hasFDerivAt_id (ρ • y)).const_smul r).const_add c)
  rw [← fderiv_centerMean_eq_firstScaledJet hF hlo hhi c r hρlo hρhi y, heq]
  calc
    _ = (fderiv ℝ (physicalHeatMean F (r ^ 2 * conditionalVariance ρ))
        (c + r • (ρ • y))).comp (r • ContinuousLinearMap.id ℝ E) := hcomp.fderiv
    _ = _ := by
      ext w
      simp [physicalHeatMeanCenterDerivative, smul_smul]

/-- The open source posterior parameter domain; no small-radius band is needed. -/
def sourcePosteriorParameterDomain : Set (E × ℝ × ℝ × E) :=
  {p | 0 < p.2.1 ∧ -1 < p.2.2.1 ∧ p.2.2.1 < 1}

/-- All source centers, positive radii, probability times and spatial points
vary jointly in the actual conditional mean. -/
theorem contDiffOn_conditionalMean_parameters {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ × ℝ × E ↦
      conditionalMean F p.1 p.2.1 p.2.2.1 p.2.2.2) sourcePosteriorParameterDomain := by
  have hp : ContDiff ℝ ∞ (fun p : E × ℝ × ℝ × E ↦
      (p.2.1 ^ 2 * conditionalVariance p.2.2.1,
        p.1 + (p.2.1 * p.2.2.1) • p.2.2.2)) := by
    unfold conditionalVariance
    fun_prop
  have hmap : MapsTo (fun p : E × ℝ × ℝ × E ↦
      (p.2.1 ^ 2 * conditionalVariance p.2.2.1,
        p.1 + (p.2.1 * p.2.2.1) • p.2.2.2))
      sourcePosteriorParameterDomain Tilt.gaussianDomain := by
    intro p hp
    exact mul_pos (sq_pos_of_pos hp.1) (conditionalVariance_pos hp.2.1 hp.2.2)
  have hs := (contDiffOn_physicalHeatMean hF hlo hhi).comp hp.contDiffOn hmap
  exact hs.congr fun p hp ↦
    conditionalMean_eq_physicalHeatMean hF hp.1 hp.2.1 hp.2.2 p.1 p.2.2.2

/-- The literal covariance operator is jointly smooth in every source parameter,
including probability time zero. -/
theorem contDiffOn_firstScaledJet_parameters {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ × ℝ × E ↦
      firstScaledJet F p.1 p.2.1 p.2.2.1 p.2.2.2) sourcePosteriorParameterDomain := by
  have hp : ContDiff ℝ ∞ (fun p : E × ℝ × ℝ × E ↦
      (p.2.1 ^ 2 * conditionalVariance p.2.2.1,
        p.1 + (p.2.1 * p.2.2.1) • p.2.2.2)) := by
    unfold conditionalVariance
    fun_prop
  have hmap : MapsTo (fun p : E × ℝ × ℝ × E ↦
      (p.2.1 ^ 2 * conditionalVariance p.2.2.1,
        p.1 + (p.2.1 * p.2.2.1) • p.2.2.2))
      sourcePosteriorParameterDomain Tilt.gaussianDomain := by
    intro p hp
    exact mul_pos (sq_pos_of_pos hp.1) (conditionalVariance_pos hp.2.1 hp.2.2)
  have hs := (contDiffOn_physicalHeatMeanCenterDerivative hF hlo hhi).comp hp.contDiffOn hmap
  have hr : ContDiffOn ℝ ∞ (fun p : E × ℝ × ℝ × E ↦ p.2.1)
      sourcePosteriorParameterDomain := by fun_prop
  exact (hr.smul hs).congr fun p hp ↦
    firstScaledJet_eq_physicalHeatMeanCenterDerivative hF hlo hhi
      hp.1 hp.2.1 hp.2.2 p.1 p.2.2.2

end AcceleratedLogConcave.Conditional
