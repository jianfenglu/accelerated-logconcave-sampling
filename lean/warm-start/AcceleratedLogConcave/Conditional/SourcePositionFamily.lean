import AcceleratedLogConcave.Conditional.JointLaw

/-!
# Actual source position laws with varying center and radius

The kernel below is exactly `baseLaw`, not a supplied family. Its normalized
ENNReal density is measurable jointly in all measurable center/radius inputs.
The interpolation kernel is then the literal independent-Gaussian pushforward
in `interpolationLaw`. This file does not prove parameter regularity of the
transported Stein centering flow, compiler tape laws, or W12.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff
set_option autoImplicit false
set_option maxHeartbeats 500000

namespace AcceleratedLogConcave.Conditional.SourcePositionFamily
variable {A : Type*} [MeasurableSpace A]
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem measurable_baseLaw {F : E → ℝ} (hF : Measurable F)
    {center : A → E} {radius : A → ℝ}
    (hc : Measurable center) (hr : Measurable radius) :
    Measurable (fun a => baseLaw F (center a) (radius a)) := by
  let density : A × E → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (-(F (center p.1 + radius p.1 • p.2) + ‖p.2‖ ^ 2 / 2)))
  have hd : Measurable density := by
    dsimp [density]
    fun_prop
  have hn : Measurable (fun a => ∫⁻ z : E, density (a,z)) := hd.lintegral_prod_right'
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [baseLaw, Gibbs.heatPosterior, primitivePotential, sub_zero, mul_one,
    Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
  exact hn.inv.mul (hd.lintegral_prod_right' (ν := volume.restrict s))

/-- Source-normalized base law, with no externally supplied kernel. -/
def baseKernel (F : E → ℝ) (center : A → E) (radius : A → ℝ)
    (hF : Measurable F) (hc : Measurable center) (hr : Measurable radius) : Kernel A E where
  toFun a := baseLaw F (center a) (radius a)
  measurable' := measurable_baseLaw hF hc hr

@[simp] theorem baseKernel_apply (F : E → ℝ) (center : A → E) (radius : A → ℝ)
    (hF : Measurable F) (hc : Measurable center) (hr : Measurable radius) (a : A) :
    baseKernel F center radius hF hc hr a = baseLaw F (center a) (radius a) := rfl

theorem baseKernel_markov {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {center : A → E} {radius : A → ℝ}
    (hc : Measurable center) (hr : Measurable radius) :
    IsMarkovKernel (baseKernel F center radius hF.continuous.measurable hc hr) := by
  constructor
  intro a
  exact baseLaw_isProbabilityMeasure hF hlo (center a) (radius a)

/-- The literal source interpolation pushforward, at any fixed probability time. -/
def positionKernel {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {center : A → E} {radius : A → ℝ} (b : ℝ)
    (hc : Measurable center) (hr : Measurable radius) : Kernel A E := by
  let := baseKernel_markov hF hlo hc hr
  exact ((baseKernel F center radius hF.continuous.measurable hc hr) ×ₖ
    Kernel.const A (stdGaussian E)).map (interpolationMap b)

theorem positionKernel_apply {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {center : A → E} {radius : A → ℝ} (b : ℝ)
    (hc : Measurable center) (hr : Measurable radius) (a : A) :
    positionKernel hF hlo b hc hr a = interpolationLaw F (center a) (radius a) b := by
  let := baseKernel_markov hF hlo hc hr
  rw [positionKernel, Kernel.map_apply _ (by unfold interpolationMap; fun_prop),
    Kernel.prod_apply, baseKernel_apply, Kernel.const_apply]
  rfl

theorem positionKernel_markov {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {center : A → E} {radius : A → ℝ} (b : ℝ)
    (hc : Measurable center) (hr : Measurable radius) :
    IsMarkovKernel (positionKernel hF hlo b hc hr) := by
  let := baseKernel_markov hF hlo hc hr
  exact Kernel.IsMarkovKernel.map _ (by unfold interpolationMap; fun_prop)

theorem measurable_interpolationLaw {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    {center : A → E} {radius : A → ℝ} (b : ℝ)
    (hc : Measurable center) (hr : Measurable radius) :
    Measurable (fun a => interpolationLaw F (center a) (radius a) b) := by
  convert (positionKernel hF hlo b hc hr).measurable using 1
  funext a
  exact (positionKernel_apply hF hlo b hc hr a).symm

end AcceleratedLogConcave.Conditional.SourcePositionFamily
