import AcceleratedLogConcave.Conditional.SteinKernel
import AcceleratedLogConcave.Conditional.Stein.TransportedCurrent
import AcceleratedLogConcave.Conditional.Stein.TransportLaw
import AcceleratedLogConcave.Conditional.Stein.BoundedIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! # The weak transported Stein identity -/
noncomputable section
set_option maxHeartbeats 1600000
open Set Function MeasureTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Rewriting the actual transported-current derivative under the terminal
law produces exactly the nonsingular Stein-kernel integrand. -/
theorem hasDerivAt_conditionalMean_transportedTest_terminal
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (u : E) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 b)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hφK : HasCompactSupport φ) :
    HasDerivAt
      (fun t => ∫ y, inner ℝ u (conditionalMean F x r t y) *
        transportedSteinTest hF hell hlo hup x hr hb hb1 φ (t, y)
        ∂interpolationLaw F x r t)
      (∫ y, fderiv ℝ φ y
        (transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y u)
          ∂interpolationLaw F x r b) ρ := by
  have hd := hasDerivAt_conditionalMean_transportedTest hF hell hlo hup x hr hb hb1 u hρ φ hφ hφK
  let T := forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ
  have heq (y : E) :
      fderiv ℝ (transportedSteinTest hF hell hlo hup x hr hb hb1 φ) (ρ, y)
        (0, firstScaledJetRow F x u r ρ y) =
      fderiv ℝ φ (T y)
        (transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ (T y) u) := by
    rw [fderiv_transportedSteinTest_spatial hF hell hlo hup x hr hb hb1 φ hφ hρ]
    dsimp only [transportedSteinIntegrand, transportedJacobian, ContinuousLinearMap.comp_apply, T]
    rw [backward_forwardProbabilityTransport]
    congr 1
    congr 1
    exact congrArg (fun A : E →L[ℝ] E => A u)
      (firstScaledJet_symmetric hF hlo hup x hr.ne'
        (by linarith [hρ.1]) (hρ.2.trans hb1) y).clm_adjoint_eq
  have hmp := forwardProbabilityTransport_measurePreserving hF hell hlo hup x hr hb hb1
    ⟨hρ.1.le, hρ.2.le⟩
  have hint := hmp.integral_comp T.measurableEmbedding
    (fun y => fderiv ℝ φ y
      (transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y u))
  have hi : (∫ y, fderiv ℝ (transportedSteinTest hF hell hlo hup x hr hb hb1 φ) (ρ, y)
        (0, firstScaledJetRow F x u r ρ y) ∂interpolationLaw F x r ρ) =
      ∫ y, fderiv ℝ φ y
        (transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y u)
          ∂interpolationLaw F x r b := by
    rw [← hint]
    exact integral_congr_ae (Filter.Eventually.of_forall heq)
  rwa [hi] at hd

/-- The actual transported Stein kernel has the source weighted adjoint
`M_b - M_0`. No transport, current, Jacobian ODE, or Stein identity is an
assumption: each is derived from the original C² convex-potential hypotheses. -/
theorem transportedSteinKernelTranspose_compact_test
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1 / 2)
    (v : E) (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hφK : HasCompactSupport φ) :
    (∫ y, inner ℝ v (conditionalMean F x r b y - conditionalMean F x r 0 0) * φ y
        ∂interpolationLaw F x r b) =
      ∫ y, fderiv ℝ φ y (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 y v)
        ∂interpolationLaw F x r b := by
  let μ := interpolationLaw F x r b
  let : IsProbabilityMeasure μ := interpolationLaw_isProbabilityMeasure hF hlo x r b
  let A := transportedSteinIntegrand hF hell hlo hup x hr hb hb1
  let J (t : ℝ) (y : E) := fderiv ℝ φ y (A t y v)
  let Q (t : ℝ) := ∫ y, inner ℝ v (conditionalMean F x r t y) *
    transportedSteinTest hF hell hlo hup x hr hb hb1 φ (t, y) ∂interpolationLaw F x r t
  have hJ : Continuous (fun p : E × Icc 0 b => J p.2 p.1) :=
    ((hφ.continuous_fderiv (by norm_num)).comp continuous_fst).clm_apply
      ((continuous_transportedSteinIntegrand_joint hF hell hlo hup x hr hb hb1).clm_apply
        continuous_const)
  obtain ⟨C, hC⟩ := (hφ.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hφK.fderiv ℝ)
  have hCpos : 0 ≤ C := (norm_nonneg (fderiv ℝ φ 0)).trans (hC 0)
  have hbound (t : ℝ) (ht : t ∈ Icc 0 b) (y : E) :
      ‖J t y‖ ≤ C * (Real.exp 1 * (r * ell) * ‖v‖) := by
    apply ((fderiv ℝ φ y).le_opNorm _).trans
    apply mul_le_mul (hC y) _ (norm_nonneg _) hCpos
    exact ((A t y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right
        (norm_transportedSteinIntegrand_le hF hell hlo hup x hr hb hb1 hsmall ht y)
        (norm_nonneg v))
  have hJcont : ContinuousOn (fun t => ∫ y, J t y ∂μ) (Icc 0 b) :=
    Stein.continuousOn_integral_bounded_current hb J hJ hbound
  have hQcont : ContinuousOn Q (Icc 0 b) :=
    continuousOn_conditionalMean_transportedTest hF hell hlo hup x hr hb hb1 v φ hφ.continuous hφK
  have hQd (t : ℝ) (ht : t ∈ Ioo 0 b) : HasDerivAt Q (∫ y, J t y ∂μ) t :=
    hasDerivAt_conditionalMean_transportedTest_terminal hF hell hlo hup x hr hb hb1 v ht φ hφ hφK
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb hQcont hQd
    (hJcont.intervalIntegrable_of_Icc hb)
  have hswap := Stein.intervalIntegral_integral_swap_bounded_current (μ := μ) hb J hJ hbound
  have hkernel (y : E) : (∫ t in 0..b, J t y) =
      fderiv ℝ φ y (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 y v) := by
    have hi := intervalIntegrable_transportedSteinIntegrand hF hell hlo hup x hr hb hb1 y
    let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
      (fderiv ℝ φ y).comp (ContinuousLinearMap.apply ℝ E v)
    exact L.intervalIntegral_comp_comm hi
  have hR : (∫ y, fderiv ℝ φ y
        (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 y v) ∂μ) = Q b - Q 0 := by
    rw [← hFTC, hswap]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hkernel y).symm)
  have hbQ : Q b = ∫ y, inner ℝ v (conditionalMean F x r b y) * φ y ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [transportedSteinTest, forwardProbabilityTransport_terminal]
  have h0Q : Q 0 = inner ℝ v (conditionalMean F x r 0 0) * ∫ y, φ y ∂μ := by
    have hmp := forwardProbabilityTransport_measurePreserving hF hell hlo hup x hr hb hb1
      (ρ := 0) ⟨le_rfl, hb⟩
    have hi := hmp.integral_comp
      (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 0).measurableEmbedding φ
    change (∫ y, inner ℝ v (conditionalMean F x r 0 y) *
      φ (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 0 y)
        ∂interpolationLaw F x r 0) = _
    simp only [conditionalMean_zero, integral_const_mul, hi]
    rfl
  have hmi : Integrable (fun y => inner ℝ v (conditionalMean F x r b y) * φ y) μ :=
    (((innerSL ℝ v).continuous.comp
      (contDiff_one_conditionalMean hF hlo hup x r (by linarith) hb1).continuous).mul
        hφ.continuous).integrable_of_hasCompactSupport hφK.mul_left
  have hφi : Integrable φ μ := hφ.continuous.integrable_of_hasCompactSupport hφK
  rw [hR, hbQ, h0Q, ← integral_const_mul, ← integral_sub hmi
    (hφi.const_mul (inner ℝ v (conditionalMean F x r 0 0)))]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [inner_sub_right, sub_mul]

end AcceleratedLogConcave.Conditional
