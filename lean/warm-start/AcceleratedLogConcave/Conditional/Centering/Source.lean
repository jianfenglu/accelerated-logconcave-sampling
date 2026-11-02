import AcceleratedLogConcave.Conditional.Centering.Moments
import AcceleratedLogConcave.Conditional.Centering.SourceData
import AcceleratedLogConcave.Conditional.Centering.SourceRegularity
import AcceleratedLogConcave.Conditional.Stein.MeanIntegrability

/-! The actual transported Stein kernel supplies every analytic input to the
complete stationary centering construction. No field, flow, or invariance
certificate is assumed in these source-facing definitions and theorems. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff

namespace AcceleratedLogConcave.Conditional.Centering
open Kinetic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The source centering trajectory, using the constructed transported kernel
and actual terminal conditional mean, at every positive or negative time. -/
def sourceCenteringFlow {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1/2) {s : ℝ} (hs : 0 < s) (z : Phase E) : ℝ → Phase E :=
  centeringFlow
    (Kt := transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1)
    (M := conditionalMean F x r b) (B := ⟨r*ell, by positivity⟩) (s := s)
    (sourceKernel_contDiff_one hF hell hlo hup x hr hb hb1 hsmall)
    (contDiff_one_conditionalMean hF hlo hup x r (by linarith) hb1)
    (A := 2 * Real.exp 1 * (r*ell)) (by positivity)
    (norm_transportedSteinKernelTranspose_le hF hell hlo hup x hr hb hb1 hsmall)
    (lipschitzWith_conditionalMean hF hell hlo hup x hr (by linarith) hb1)
    (conditionalMean F x r 0 0) hs z

/-- Spatial C1 homeomorphism supplied by the actual complete source ODE. -/
def sourceCenteringHomeomorph {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1/2) {s : ℝ} (hs : 0 < s) (t : ℝ) : Phase E ≃ₜ Phase E :=
  centeringFlowHomeomorph
    (Kt := transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1)
    (M := conditionalMean F x r b) (B := ⟨r*ell, by positivity⟩) (s := s)
    (sourceKernel_contDiff_one hF hell hlo hup x hr hb hb1 hsmall)
    (contDiff_one_conditionalMean hF hlo hup x r (by linarith) hb1)
    (A := 2 * Real.exp 1 * (r*ell)) (by positivity)
    (norm_transportedSteinKernelTranspose_le hF hell hlo hup x hr hb hb1 hsmall)
    (lipschitzWith_conditionalMean hF hell hlo hup x hr (by linarith) hb1)
    (conditionalMean F x r 0 0) hs t

omit [DecidableEq ι] in
theorem sourceCenteringFlow_initial {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1/2) {s : ℝ} (hs : 0 < s) (z : Phase E) :
    sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z 0 = z :=
  centeringFlow_initial _ _ _ _ _ _ _ z

omit [DecidableEq ι] in
/-- Both original centering equations hold at every real time. -/
theorem sourceCenteringFlow_deriv {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1/2) {s : ℝ} (hs : 0 < s) (z : Phase E) (t : ℝ) :
    HasDerivAt (sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z)
      (velocity (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1)
        (conditionalMean F x r b) (conditionalMean F x r 0 0) s
        (sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z t)) t :=
  centeringFlow_deriv _ _ _ _ _ _ _ z t

/-- The actual complete source flow preserves the independent terminal
interpolation/Gaussian law in both time directions. -/
theorem sourceCenteringHomeomorph_measurePreserving {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1/2) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    MeasurePreserving (sourceCenteringHomeomorph hF hell hlo hup x hr hb hb1 hsmall hs t)
      (coupledPhaseMeasure (interpolationLaw F x r b))
      (coupledPhaseMeasure (interpolationLaw F x r b)) := by
  let := interpolationLaw_isProbabilityMeasure hF hlo x r b
  unfold sourceCenteringHomeomorph
  apply centeringFlowHomeomorph_measurePreserving_of_stein
    (hp := sourceDensity_contDiff_one hF hlo x r hb hb1)
  · intro y
    exact (interpolationDensity_pos hF hlo x r b (conditionalVariance_pos (by linarith) hb1) y).le
  · exact interpolationLaw_eq_explicitDensity hF hlo x r b (conditionalVariance_pos (by linarith) hb1)
  · exact source_pointwise_stein_of_contDiff hF hell hlo hup x hr hb hb1 hsmall
      (sourceKernel_contDiff_one hF hell hlo hup x hr hb hb1 hsmall)

omit [DecidableEq ι] in
/-- Exact integrated source output, retaining the originally supplied momentum. -/
theorem sourceCenteringFlow_output_identity {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1/2) {s : ℝ} (hs : 0 < s) (z : Phase E) :
    s • z.snd + ∫ t in (0 : ℝ)..1,
      conditionalMean F x r b (sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z t).fst =
      conditionalMean F x r 0 0 +
        s • (sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z 1).snd :=
  centeringFlow_integrated_output _ _ _ _ _ _ _ z

/-- The actual literal integrated output has the shifted Gaussian law. -/
theorem sourceCenteringFlow_output_law {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1/2) {s : ℝ} (hs : 0 < s) :
    (coupledPhaseMeasure (interpolationLaw F x r b)).map (fun z => s • z.snd +
      ∫ t in (0 : ℝ)..1,
        conditionalMean F x r b (sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z t).fst) =
      (stdGaussian E).map (fun g => conditionalMean F x r 0 0 + s • g) := by
  let := interpolationLaw_isProbabilityMeasure hF hlo x r b
  unfold sourceCenteringFlow
  apply centeringFlow_output_law_of_stein (hp := sourceDensity_contDiff_one hF hlo x r hb hb1)
  · intro y
    exact (interpolationDensity_pos hF hlo x r b (conditionalVariance_pos (by linarith) hb1) y).le
  · exact interpolationLaw_eq_explicitDensity hF hlo x r b (conditionalVariance_pos (by linarith) hb1)
  · exact source_pointwise_stein_of_contDiff hF hell hlo hup x hr hb hb1 hsmall
      (sourceKernel_contDiff_one hF hell hlo hup x hr hb hb1 hsmall)

/-- Actual source displacement with a universal constant, obtained from its
stationary second moments. This holds for every nonnegative time, hence on the
source interval `0 ≤ t ≤ 1`. -/
theorem sourceCenteringFlow_displacement_rms_le {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1/2) {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (∫ z, ‖sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z t-z‖ ^ 2
      ∂coupledPhaseMeasure (interpolationLaw F x r b)) ≤
      (Real.sqrt 5 * Real.exp 1) * t * ((r*ell)/s) * Real.sqrt (Module.finrank ℝ E) := by
  let := interpolationLaw_isProbabilityMeasure hF hlo x r b
  have hmean := integrable_conditionalMean_sub_norm_sq hF hell hlo hup x hr hb hb1 hsmall
    (conditionalMean F x r 0 0)
  have hQ : (∫ y, ‖conditionalMean F x r b y - conditionalMean F x r 0 0‖ ^ 2
      ∂interpolationLaw F x r b) ≤ (Real.exp 1 * (r*ell)) ^ 2 * (Module.finrank ℝ E : ℝ) := by
    simpa only [conditionalMean_zero] using
      integral_conditionalMean_centered_norm_sq_le hF hell hlo hup x hr hb hb1 hsmall
  have hh := centeringFlow_displacement_rms_le_of_stein
    (sourceKernel_contDiff_one hF hell hlo hup x hr hb hb1 hsmall)
    (contDiff_one_conditionalMean hF hlo hup x r (by linarith) hb1)
    (A := 2 * Real.exp 1 * (r*ell)) (by positivity)
    (norm_transportedSteinKernelTranspose_le hF hell hlo hup x hr hb hb1 hsmall)
    (lipschitzWith_conditionalMean hF hell hlo hup x hr (by linarith) hb1)
    (conditionalMean F x r 0 0) hs (sourceDensity_contDiff_one hF hlo x r hb hb1)
    (fun y => (interpolationDensity_pos hF hlo x r b
      (conditionalVariance_pos (by linarith) hb1) y).le)
    (interpolationLaw_eq_explicitDensity hF hlo x r b (conditionalVariance_pos (by linarith) hb1))
    (source_pointwise_stein_of_contDiff hF hell hlo hup x hr hb hb1 hsmall
      (sourceKernel_contDiff_one hF hell hlo hup x hr hb hb1 hsmall)) hmean hQ ht
  apply hh.trans_eq
  have halg : (2 * Real.exp 1 * (r*ell))^2 * (Module.finrank ℝ E : ℝ) +
      (Real.exp 1 * (r*ell))^2 * (Module.finrank ℝ E : ℝ) =
      5 * (Real.exp 1 * (r*ell))^2 * (Module.finrank ℝ E : ℝ) := by ring
  rw [halg, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 5 * (Real.exp 1 * (r*ell))^2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.exp 1 * (r*ell))]
  simp only [div_eq_mul_inv]
  ring

end AcceleratedLogConcave.Conditional.Centering
