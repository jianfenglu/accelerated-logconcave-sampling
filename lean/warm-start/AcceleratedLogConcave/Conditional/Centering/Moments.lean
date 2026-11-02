import AcceleratedLogConcave.Conditional.Centering.Invariant
import AcceleratedLogConcave.Conditional.Centering.Displacement
import AcceleratedLogConcave.Gibbs.PrimitiveMoments

/-! Stationary speed and displacement moments of the centering flow. Only
second moments enter; the Gaussian factor is the actual independent factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional.Centering
open Kinetic Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem phase_fst_preserving (ξ : Measure E) [IsProbabilityMeasure ξ] :
    MeasurePreserving (fun z : Phase E => z.fst) (coupledPhaseMeasure ξ) ξ := by
  refine ⟨(WithLp.prod_continuous_ofLp 2 E E).fst.measurable, ?_⟩
  rw [coupledPhaseMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map Prod.fst (ξ.prod (stdGaussian E)) = ξ
  simp

private theorem phase_snd_preserving (ξ : Measure E) [IsProbabilityMeasure ξ] :
    MeasurePreserving (fun z : Phase E => z.snd) (coupledPhaseMeasure ξ) (stdGaussian E) := by
  refine ⟨(WithLp.prod_continuous_ofLp 2 E E).snd.measurable, ?_⟩
  rw [coupledPhaseMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map Prod.snd (ξ.prod (stdGaussian E)) = stdGaussian E
  simp

/-- A kernel operator bound controls its Gaussian contraction with the physical
dimension, without any dimension factor beyond the Gaussian second moment. -/
theorem integral_speed_sq_le {Kt : E → E →L[ℝ] E} {M : E → E}
    (hKt : Continuous Kt) (hM : Continuous M)
    {A : ℝ} (_hA : 0 ≤ A) (hbound : ∀ y, ‖Kt y‖ ≤ A) (u : E) (s : ℝ)
    {ξ : Measure E} [IsProbabilityMeasure ξ]
    (hmean : Integrable (fun y => ‖M y-u‖ ^ 2) ξ) :
    Integrable (fun z => ‖velocity Kt M u s z‖ ^ 2) (coupledPhaseMeasure ξ) ∧
      (∫ z, ‖velocity Kt M u s z‖ ^ 2 ∂coupledPhaseMeasure ξ) ≤
        s⁻¹ ^ 2 * (A ^ 2 * Module.finrank ℝ E + ∫ y, ‖M y-u‖ ^ 2 ∂ξ) := by
  let μ := coupledPhaseMeasure ξ
  have hsnd := phase_snd_preserving ξ
  have hfst := phase_fst_preserving ξ
  have hgauss : Integrable (fun g : E => ‖g‖ ^ 2) (stdGaussian E) :=
    (memLp_two_iff_integrable_sq_norm (IsGaussian.memLp_two_id (μ := stdGaussian E)).aestronglyMeasurable).mp
      (IsGaussian.memLp_two_id (μ := stdGaussian E))
  have hsndint : Integrable (fun z : Phase E => ‖z.snd‖ ^ 2) μ :=
    hsnd.integrable_comp_of_integrable hgauss
  have hmeanint : Integrable (fun z : Phase E => ‖M z.fst-u‖ ^ 2) μ :=
    hfst.integrable_comp_of_integrable hmean
  have hKbound (z : Phase E) : ‖Kt z.fst z.snd‖ ^ 2 ≤ A ^ 2 * ‖z.snd‖ ^ 2 := by
    have h := (Kt z.fst).le_opNorm z.snd |>.trans
      (mul_le_mul_of_nonneg_right (hbound z.fst) (norm_nonneg _))
    nlinarith [norm_nonneg (Kt z.fst z.snd), norm_nonneg z.snd]
  have hKcont : Continuous (fun z : Phase E => ‖Kt z.fst z.snd‖ ^ 2) :=
    ((hKt.comp (WithLp.prod_continuous_ofLp 2 E E).fst).clm_apply
      (WithLp.prod_continuous_ofLp 2 E E).snd).norm.pow 2
  have hKint : Integrable (fun z : Phase E => ‖Kt z.fst z.snd‖ ^ 2) μ :=
    (hsndint.const_mul (A^2)).mono' hKcont.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hKbound z)
  have hspeed : Integrable (fun z => ‖velocity Kt M u s z‖ ^ 2) μ := by
    simpa only [norm_velocity_sq, Pi.add_apply] using (hKint.add hmeanint).const_mul (s⁻¹ ^ 2)
  refine ⟨hspeed, ?_⟩
  have hsndval : (∫ z : Phase E, ‖z.snd‖ ^ 2 ∂μ) = (Module.finrank ℝ E : ℝ) := by
    have hi := Gibbs.integral_norm_sq_stdGaussian (E := E)
    rw [← hsnd.map_eq, integral_map hsnd.measurable.aemeasurable (by fun_prop)] at hi
    exact hi
  have hmeanval : (∫ z : Phase E, ‖M z.fst-u‖ ^ 2 ∂μ) = ∫ y, ‖M y-u‖ ^ 2 ∂ξ := by
    rw [← hfst.map_eq, integral_map hfst.measurable.aemeasurable (by fun_prop)]
  calc
    _ = s⁻¹ ^ 2 * ((∫ z : Phase E, ‖Kt z.fst z.snd‖ ^ 2 ∂μ) +
        ∫ z : Phase E, ‖M z.fst-u‖ ^ 2 ∂μ) := by
      simp_rw [norm_velocity_sq]
      rw [integral_const_mul, integral_add hKint hmeanint]
    _ ≤ s⁻¹ ^ 2 * (A^2 * Module.finrank ℝ E + ∫ y, ‖M y-u‖ ^ 2 ∂ξ) := by
      gcongr
      · exact (integral_mono hKint (hsndint.const_mul (A^2)) hKbound).trans_eq
          (by rw [integral_const_mul, hsndval])
      · exact hmeanval.le

/-- The stationary centering displacement uses exactly the Gaussian
contraction moment and the centered conditional-mean second moment. -/
theorem centeringFlow_displacement_sq_le_of_stein
    {Kt : E → E →L[ℝ] E} {M : E → E}
    (hKt : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y, ‖Kt y‖ ≤ A)
    {B : ℝ≥0} (hlip : LipschitzWith B M) (u : E) {s : ℝ} (hs : 0 < s)
    {ξ : Measure E} [IsProbabilityMeasure ξ]
    {p : E → ℝ} (hp : ContDiff ℝ 1 p) (hp0 : ∀ y, 0 ≤ p y)
    (hξ : ξ = volume.withDensity (fun y => ENNReal.ofReal (p y)))
    (hstein : ∀ y g, fderiv ℝ p y (Kt y g) + p y * fluxDivergence (fun w => Kt w g) y =
      -p y * inner ℝ (M y - u) g)
    (hmean : Integrable (fun y => ‖M y-u‖ ^ 2) ξ)
    {Q : ℝ} (hQ : (∫ y, ‖M y-u‖ ^ 2 ∂ξ) ≤ Q)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, ‖centeringFlow hKt hM hA hbound hlip u hs z t - z‖ ^ 2 ∂coupledPhaseMeasure ξ) ≤
      t ^ 2 * s⁻¹ ^ 2 * (A ^ 2 * Module.finrank ℝ E + Q) := by
  obtain ⟨hspeed, hspeedbound⟩ := integral_speed_sq_le hKt.continuous hM.continuous hA hbound u s hmean
  have hpath : (∫ z, ‖centeringFlow hKt hM hA hbound hlip u hs z t-z‖ ^ 2 ∂coupledPhaseMeasure ξ) ≤
      t ^ 2 * ∫ z, ‖velocity Kt M u s z‖ ^ 2 ∂coupledPhaseMeasure ξ := by
    unfold centeringFlow
    apply integral_completeCurve_displacement_sq_le
    · intro τ
      exact centeringFlowHomeomorph_measurePreserving_of_stein hKt hM hA hbound hlip u hs hp hp0 hξ hstein τ
    · exact hspeed
    · exact ht
  calc
    _ ≤ t^2 * ∫ z, ‖velocity Kt M u s z‖ ^ 2 ∂coupledPhaseMeasure ξ := hpath
    _ ≤ t^2 * (s⁻¹ ^ 2 * (A ^ 2 * Module.finrank ℝ E + Q)) := by
      gcongr
      exact hspeedbound.trans (by gcongr)
    _ = _ := by ring

/-- The root-mean-square displacement has the source's linear dependence on
time and inverse Gaussian scale. -/
theorem centeringFlow_displacement_rms_le_of_stein
    {Kt : E → E →L[ℝ] E} {M : E → E}
    (hKt : ContDiff ℝ 1 Kt) (hM : ContDiff ℝ 1 M)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y, ‖Kt y‖ ≤ A)
    {B : ℝ≥0} (hlip : LipschitzWith B M) (u : E) {s : ℝ} (hs : 0 < s)
    {ξ : Measure E} [IsProbabilityMeasure ξ]
    {p : E → ℝ} (hp : ContDiff ℝ 1 p) (hp0 : ∀ y, 0 ≤ p y)
    (hξ : ξ = volume.withDensity (fun y => ENNReal.ofReal (p y)))
    (hstein : ∀ y g, fderiv ℝ p y (Kt y g) + p y * fluxDivergence (fun w => Kt w g) y =
      -p y * inner ℝ (M y - u) g)
    (hmean : Integrable (fun y => ‖M y-u‖ ^ 2) ξ)
    {Q : ℝ} (hQ : (∫ y, ‖M y-u‖ ^ 2 ∂ξ) ≤ Q)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (∫ z, ‖centeringFlow hKt hM hA hbound hlip u hs z t - z‖ ^ 2 ∂coupledPhaseMeasure ξ) ≤
      (t / s) * Real.sqrt (A ^ 2 * Module.finrank ℝ E + Q) := by
  have hh := centeringFlow_displacement_sq_le_of_stein hKt hM hA hbound hlip u hs hp hp0 hξ hstein hmean hQ ht
  apply (Real.sqrt_le_sqrt hh).trans_eq
  rw [Real.sqrt_mul (mul_nonneg (sq_nonneg t) (sq_nonneg s⁻¹)),
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg ht, abs_of_nonneg (inv_nonneg.mpr hs.le)]
  rw [div_eq_mul_inv]

end AcceleratedLogConcave.Conditional.Centering
