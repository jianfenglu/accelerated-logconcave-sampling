import AcceleratedLogConcave.Conditional.JointLaw

/-! # Explicit interpolation density

Square completion expresses the interpolation density through a positive-width
posterior normalizer. This form does not involve division by probability time.
-/

noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory ProbabilityTheory Gibbs Channels
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The Lebesgue density of the interpolation, written using real normalizers. -/
def interpolationDensity (F : E → ℝ) (x : E) (r ρ : ℝ) (y : E) : ℝ :=
  Real.exp (-‖y‖ ^ 2 / 2) *
    (∫ z : E, Real.exp (-(primitivePotential F x r z +
      ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ)))) /
    ((∫ z : E, Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2))) *
      (∫ n : E, Real.exp (-‖n‖ ^ 2 / (2 * conditionalVariance ρ))))

omit [DecidableEq ι] in
/-- The averaged likelihood equals the explicit normalizer formula pointwise. -/
lemma interpolationLikelihood_lintegral {F : E → ℝ} (x : E) (r ρ : ℝ)
    (hB : Measurable (primitivePotential F x r)) (hv : 0 < conditionalVariance ρ)
    (hI : Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2))))
    (y : E)
    (hP : Integrable (fun z ↦ Real.exp (-(primitivePotential F x r z +
      ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ))))) :
    (∫⁻ z, interpolationLikelihood ρ z y ∂baseLaw F x r) =
      ENNReal.ofReal (interpolationDensity F x r ρ y) := by
  let Z : ℝ := ∫ z : E, Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2))
  let C : ℝ := ∫ n : E, Real.exp (-‖n‖ ^ 2 / (2 * conditionalVariance ρ))
  have hZ : 0 < Z := integral_exp_pos hI
  have hC : 0 < C := by
    simpa only [C, Real.coe_toNNReal _ hv.le] using
      gaussian_normalizer_pos (ι := ι) (conditionalVariance ρ).toNNReal
        (Real.toNNReal_pos.mpr hv)
  rw [baseLaw_eq_tilted_of_integrable x r hI, lintegral_tilted]
  calc
    _ = ∫⁻ z : E, ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / 2) / (Z * C)) *
        ENNReal.ofReal (Real.exp (-(primitivePotential F x r z +
          ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ)))) := by
      apply lintegral_congr
      intro z
      dsimp only [interpolationLikelihood]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have he := congrArg Real.exp
        (conditional_exponent_completion (primitivePotential F x r) ρ hv.ne' z y)
      rw [Real.exp_add, Real.exp_add] at he
      calc
        _ = (Real.exp (-(primitivePotential F x r z + ‖z‖ ^ 2 / 2)) *
            Real.exp (-‖y - ρ • z‖ ^ 2 / (2 * conditionalVariance ρ))) / (Z * C) := by
          dsimp only [Z, C]
          ring
        _ = _ := by rw [he]; ring
    _ = ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / 2) / (Z * C)) *
        (∫⁻ z : E, ENNReal.ofReal (Real.exp (-(primitivePotential F x r z +
          ‖z - ρ • y‖ ^ 2 / (2 * conditionalVariance ρ))))) := by
      rw [lintegral_const_mul _ (by fun_prop)]
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hP (Filter.Eventually.of_forall
        (fun z ↦ (Real.exp_pos _).le)), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp only [interpolationDensity, Z, C]
      ring

/-- The actual interpolation law has this explicitly normalized Lebesgue density. -/
theorem interpolationLaw_eq_explicitDensity {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r ρ : ℝ) (hv : 0 < conditionalVariance ρ) :
    interpolationLaw F x r ρ = volume.withDensity
      (fun y ↦ ENNReal.ofReal (interpolationDensity F x r ρ y)) := by
  rw [interpolationLaw_eq_withDensity x r ρ hv (base_posterior_integrable hF hlo x r)]
  congr 1
  ext y
  exact interpolationLikelihood_lintegral x r ρ
    (contDiff_primitivePotential hF x r).continuous.measurable hv
    (base_posterior_integrable hF hlo x r) y
    (conditional_posterior_integrable hF hlo x r ρ hv y)

end AcceleratedLogConcave.Conditional
