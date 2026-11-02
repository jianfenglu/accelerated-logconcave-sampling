import AcceleratedLogConcave.Conditional.Centering.SteinBridge
import AcceleratedLogConcave.Conditional.Stein.Identity
import AcceleratedLogConcave.Conditional.Centering.MeanMoments

/-! Source density, Stein sign, and second-moment inputs for centering.
The spatial C1 lemma below is an intermediate implication; the final source
flow must discharge that input by the actual transported-kernel regularity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional.Centering
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

omit [DecidableEq ι] in
/-- Spatial C1 regularity of the actual positive interpolation density. -/
theorem sourceDensity_contDiff_one {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : E) (r : ℝ) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) :
    ContDiff ℝ 1 (interpolationDensity F x r b) := by
  have hh := (contDiffOn_interpolationDensity hF hlo x r).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn
    (s := Set.univ) (fun _ _ => ⟨by linarith, hb1⟩)
  exact (contDiffOn_univ.mp hh).of_le (by simp)

/-- The actual transported compact-test identity has precisely the pointwise
weighted-divergence sign needed by the centering field. -/
theorem source_pointwise_stein_of_contDiff
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1/2)
    (hK : ContDiff ℝ 1 (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1)) :
    ∀ y g, fderiv ℝ (interpolationDensity F x r b) y
        (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 y g) +
      interpolationDensity F x r b y * Analysis.Poisson.fluxDivergence
        (fun w => transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 w g) y =
      -interpolationDensity F x r b y * inner ℝ
        (conditionalMean F x r b y - conditionalMean F x r 0 0) g := by
  let p := interpolationDensity F x r b
  let M := conditionalMean F x r b
  let score := fun y => y + (r*b) • M y
  have hblo : -1 < b := by linarith
  have hp := sourceDensity_contDiff_one hF hlo x r hb hb1
  have hp0 (y : E) : 0 < p y :=
    interpolationDensity_pos hF hlo x r b (conditionalVariance_pos hblo hb1) y
  have hM : Continuous M := (contDiff_one_conditionalMean hF hlo hup x r hblo hb1).continuous
  have hscore : Continuous score := continuous_id.add (hM.const_smul (r*b))
  have hconvert (g : E → ℝ) :
      (∫ y, g y ∂interpolationLaw F x r b) = ∫ y, p y * g y := by
    rw [interpolationLaw_eq_explicitDensity hF hlo x r b (conditionalVariance_pos hblo hb1)]
    rw [integral_withDensity_eq_integral_toReal_smul (μ := volume) (hp.continuous.measurable.ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      change (ENNReal.ofReal (p y)).toReal • g y = p y * g y
      rw [ENNReal.toReal_ofReal (hp0 y).le, smul_eq_mul]
  apply pointwise_stein_of_compact_test (conditionalMean F x r 0 0) hp hp0 hscore hM hK
    (fun y => hasFDerivAt_interpolationDensity hF hlo hup x r hblo hb1 y)
  intro g φ hφ hφK
  have hh := transportedSteinKernelTranspose_compact_test hF hell hlo hup x hr hb hb1 hsmall g φ hφ hφK
  rw [hconvert, hconvert] at hh
  simpa only [real_inner_comm, mul_assoc] using hh

end AcceleratedLogConcave.Conditional.Centering
