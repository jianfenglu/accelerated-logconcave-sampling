import AcceleratedLogConcave.Gibbs.PrimitiveMoments
import AcceleratedLogConcave.Conditional.PrimitivePullback

/-!
# Exact affine posterior identities for the actual conditional law

The constant inverse Jacobian cancels in the ENNReal normalization. The
change of variables therefore needs no normalizability of `exp (-F)` and
includes zero-dimensional spaces. No identity divides by probability time.
-/

noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Physical affine image of the primitive posterior at an arbitrary center.
The proof uses the actual normalized density, including its partition. -/
theorem heatPosterior_primitive_map_affine {F : E → ℝ} (hF : Measurable F)
    {r t : ℝ} (hr : r ≠ 0) (ht : t ≠ 0) (c a : E) :
    Measure.map (fun z : E ↦ c + r • z)
      (Gibbs.heatPosterior (primitivePotential F c r) t a) =
      Gibbs.heatPosterior F (r ^ 2 * t) (c + r • a) := by
  let T : E → E := fun z ↦ c + r • z
  let w : E → ℝ≥0∞ := fun u ↦ ENNReal.ofReal
    (Real.exp (-(F u + ‖u - (c + r • a)‖ ^ 2 / (2 * (r ^ 2 * t)))))
  have hT : Measurable T := by fun_prop
  have hw : Measurable w := by fun_prop
  have hc : 0 < abs (r ^ Module.finrank ℝ E)⁻¹ :=
    abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hr))
  have hnorm (z : E) :
      ‖c + r • z - (c + r • a)‖ ^ 2 / (2 * (r ^ 2 * t)) =
        ‖z - a‖ ^ 2 / (2 * t) := by
    rw [add_sub_add_left_eq_sub, ← smul_sub]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
  have hcomp (z : E) : w (T z) = ENNReal.ofReal
      (Real.exp (-(primitivePotential F c r z + ‖z - a‖ ^ 2 / (2 * t)))) := by
    dsimp [w, T, primitivePotential]
    rw [hnorm]
  have h := Gibbs.map_normalized_withDensity_comp
    (volume : Measure E) volume hT hw
    (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top
    (Gibbs.map_volume_primitive_affine c hr)
  simpa only [hcomp, Gibbs.heatPosterior, w, T] using h

/-- Actual conditional posterior, including `ρ = 0`, in physical coordinates. -/
theorem conditionalLaw_map_affine {F : E → ℝ} (hF : Measurable F)
    {r ρ : ℝ} (hr : 0 < r) (hρlo : -1 < ρ) (hρhi : ρ < 1) (c y : E) :
    Measure.map (fun z : E ↦ c + r • z) (conditionalLaw F c r ρ y) =
      Gibbs.heatPosterior F (r ^ 2 * conditionalVariance ρ) (c + (r * ρ) • y) := by
  simpa only [conditionalLaw, smul_smul] using
    heatPosterior_primitive_map_affine hF hr.ne'
      (conditionalVariance_pos hρlo hρhi).ne' c (ρ • y)

/-- Bochner change of variables for every continuous physical observable. -/
theorem integral_primitive_heatPosterior_affine
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → ℝ} (hF : Measurable F) {g : E → G} (hg : Continuous g)
    {r t : ℝ} (hr : r ≠ 0) (ht : t ≠ 0) (c a : E) :
    (∫ z, g (c + r • z) ∂Gibbs.heatPosterior (primitivePotential F c r) t a) =
      ∫ u, g u ∂Gibbs.heatPosterior F (r ^ 2 * t) (c + r • a) := by
  have h := integral_map_of_stronglyMeasurable
    (μ := Gibbs.heatPosterior (primitivePotential F c r) t a)
    (show Measurable (fun z : E ↦ c + r • z) by fun_prop) hg.stronglyMeasurable
  rw [heatPosterior_primitive_map_affine hF hr ht c a] at h
  exact h.symm

/-- The actual conditional mean is exactly the physical posterior expectation. -/
theorem conditionalMean_eq_integral_heatPosterior {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {r ρ : ℝ} (hr : 0 < r)
    (hρlo : -1 < ρ) (hρhi : ρ < 1) (c y : E) :
    conditionalMean F c r ρ y =
      ∫ u, gradient F u ∂Gibbs.heatPosterior F
        (r ^ 2 * conditionalVariance ρ) (c + (r * ρ) • y) := by
  have hg : Continuous (gradient F) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hF.continuous_fderiv (by norm_num))
  simpa only [conditionalMean, conditionalLaw, primitiveObservable, smul_smul] using
    integral_primitive_heatPosterior_affine hF.continuous.measurable hg hr.ne'
      (conditionalVariance_pos hρlo hρhi).ne' c (ρ • y)

/-- The physical gradient expectation is a genuine integrable Bochner integral.
Only the original C² lower and upper Hessian bounds are used. -/
theorem integrable_gradient_physical_conditionalPosterior {F : E → ℝ} {L : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hlo : ∀ u v, 0 ≤ fderiv ℝ (fderiv ℝ F) u v v)
    (hup : ∀ u v, fderiv ℝ (fderiv ℝ F) u v v ≤ L * ‖v‖ ^ 2)
    {r ρ : ℝ} (hr : 0 < r) (hρlo : -1 < ρ) (hρhi : ρ < 1) (c y : E) :
    Integrable (gradient F) (Gibbs.heatPosterior F
      (r ^ 2 * conditionalVariance ρ) (c + (r * ρ) • y)) := by
  exact Gibbs.integrable_gradient_heatPosterior hF (m := 0) le_rfl
    (mul_pos (sq_pos_of_pos hr) (conditionalVariance_pos hρlo hρhi))
    (by simpa using hlo) hup _

/-- Integrability of the literal primitive observable under the actual law,
obtained by the exact affine pushforward, with no division by `ρ`. -/
theorem integrable_primitiveObservable_conditionalLaw {F : E → ℝ} {L : ℝ}
    (hF : ContDiff ℝ 2 F)
    (hlo : ∀ u v, 0 ≤ fderiv ℝ (fderiv ℝ F) u v v)
    (hup : ∀ u v, fderiv ℝ (fderiv ℝ F) u v v ≤ L * ‖v‖ ^ 2)
    {r ρ : ℝ} (hr : 0 < r) (hρlo : -1 < ρ) (hρhi : ρ < 1) (c y : E) :
    Integrable (primitiveObservable F c r) (conditionalLaw F c r ρ y) := by
  have h := integrable_gradient_physical_conditionalPosterior hF hlo hup
    hr hρlo hρhi c y
  rw [← conditionalLaw_map_affine hF.continuous.measurable hr hρlo hρhi c y] at h
  exact h.comp_measurable (by fun_prop)

/-- Regression at the nonsingular probability endpoint `ρ = 0`. -/
theorem baseLaw_map_affine {F : E → ℝ} (hF : Measurable F)
    {r : ℝ} (hr : 0 < r) (c : E) :
    Measure.map (fun z : E ↦ c + r • z) (baseLaw F c r) =
      Gibbs.heatPosterior F (r ^ 2) c := by
  simpa using conditionalLaw_map_affine hF hr (ρ := 0) (by norm_num)
    (by norm_num) c (0 : E)

/-- The physical posterior formula at `ρ = 0` is independent of the input. -/
theorem conditionalMean_zero_eq_integral_heatPosterior {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {r : ℝ} (hr : 0 < r) (c y : E) :
    conditionalMean F c r 0 y =
      ∫ u, gradient F u ∂Gibbs.heatPosterior F (r ^ 2) c := by
  simpa using conditionalMean_eq_integral_heatPosterior hF hr (ρ := 0)
    (by norm_num) (by norm_num) c y

end AcceleratedLogConcave.Conditional
