import AcceleratedLogConcave.Conditional.Centering.Source
import AcceleratedLogConcave.Analysis.ODEObservableJet
import AcceleratedLogConcave.Analysis.FiniteDerivativeLadder

/-! Isolated repair of the 2026-10-20 12:22 draft; unverified until the compiler gate. Source-facing stationary
specialization of the EXISTING ODEJet.observableJet ladder. No new generic
recursion, tensor representation, integrability or quantitative moment premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Conditional.Centering
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => Phase E
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [DecidableEq ι] in
theorem contDiff_infty_sourceVelocity {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖^2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2) (s : ℝ) :
    ContDiff ℝ ∞ (velocity
      (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1)
      (conditionalMean F x r b) (conditionalMean F x r 0 0) s) := by
  have hK : ContDiff ℝ ∞
      (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1) :=
    Transport.contDiff_infty_transportedSteinKernelTranspose
      hF hell hlo hup x hr hb hb1 hsmall
  have hpair : ContDiff ℝ ∞ (fun y : E => (b, y)) :=
    contDiff_const.prodMk contDiff_id
  have hM0 := (contDiffOn_conditionalMean hF hlo hup x r).comp
    (s := Set.univ) hpair.contDiffOn (fun y _ => ⟨by linarith, hb1⟩)
  have hM : ContDiffOn ℝ ∞ (conditionalMean F x r b) Set.univ := by
    simpa only [Function.comp_def] using hM0
  exact contDiff_velocity hK (contDiffOn_univ.mp hM) (conditionalMean F x r 0 0) s

/-- The inherited time-space observable ladder specialized to the actual field. -/
def sourceObservableJet {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖^2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (s : ℝ) (φ : P → W) : ℕ → ℝ × P → W :=
  Analysis.ODEJet.observableJet Set.univ (fun p => velocity (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1) (conditionalMean F x r b) (conditionalMean F x r 0 0) s p.2)
    (fun p => φ p.2)


omit [DecidableEq ι] in
theorem hasDerivAt_sourceObservableJet_along {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖^2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2)
    {s : ℝ} (hs : 0 < s) {φ : P → W} (hφ : ContDiff ℝ ∞ φ)
    (k : ℕ) (t : ℝ) (z : P) :
    HasDerivAt (fun q => (sourceObservableJet hF hell hlo hup x hr hb hb1) s φ k (q, sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z q))
      ((sourceObservableJet hF hell hlo hup x hr hb hb1) s φ (k+1) (t, sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z t)) t := by
  exact Analysis.ODEJet.hasDerivAt_observableJet_along isOpen_univ
    ((contDiff_infty_sourceVelocity hF hell hlo hup x hr hb hb1 hsmall s).comp contDiff_snd).contDiffOn
    (hφ.comp contDiff_snd).contDiffOn (mem_univ _)
    (sourceCenteringFlow_deriv hF hell hlo hup x hr hb hb1 hsmall hs z t) k

omit [DecidableEq ι] in
theorem iteratedDeriv_sourceObservable_along {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖^2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2)
    {s : ℝ} (hs : 0 < s) {φ : P → W} (hφ : ContDiff ℝ ∞ φ)
    (k : ℕ) (t : ℝ) (z : P) :
    iteratedDeriv k (fun q => φ (sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z q)) t =
      (sourceObservableJet hF hell hlo hup x hr hb hb1) s φ k (t, sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z t) := by
  exact Analysis.iteratedDeriv_eq_of_finite_ladder k
    (fun k q => (sourceObservableJet hF hell hlo hup x hr hb hb1) s φ k (q, sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z q))
    isOpen_univ
    (fun k _ q _ => hasDerivAt_sourceObservableJet_along hF hell hlo hup x hr hb hb1 hsmall hs hφ k q z)
    (mem_univ t)

/-- Exact stationarity identity only; no finiteness or moment bound is asserted. -/
theorem integral_sourceObservable_derivative_sq {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖^2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2)
    {s : ℝ} (hs : 0 < s) {φ : P → W} (hφ : ContDiff ℝ ∞ φ) (k : ℕ) (t : ℝ) :
    (∫ z, ‖iteratedDeriv k (fun q => φ (sourceCenteringFlow hF hell hlo hup x hr hb hb1 hsmall hs z q)) t‖^2
      ∂Kinetic.coupledPhaseMeasure (interpolationLaw F x r b)) =
    ∫ z, ‖(sourceObservableJet hF hell hlo hup x hr hb hb1) s φ k (t,z)‖^2 ∂Kinetic.coupledPhaseMeasure (interpolationLaw F x r b) := by
  simp_rw [iteratedDeriv_sourceObservable_along hF hell hlo hup x hr hb hb1 hsmall hs hφ k t]
  have hc := Analysis.ODEJet.contDiffOn_observableJet uniqueDiffOn_univ
    ((contDiff_infty_sourceVelocity hF hell hlo hup x hr hb hb1 hsmall s).comp contDiff_snd).contDiffOn
    (hφ.comp contDiff_snd).contDiffOn k
  have hj : Continuous (fun z => (sourceObservableJet hF hell hlo hup x hr hb hb1) s φ k (t,z)) :=
    (contDiffOn_univ.mp hc).continuous.comp (continuous_const.prodMk continuous_id)
  have hp := sourceCenteringHomeomorph_measurePreserving hF hell hlo hup x hr hb hb1 hsmall hs t
  have hi := MeasureTheory.integral_map
    (μ := Kinetic.coupledPhaseMeasure (interpolationLaw F x r b)) hp.measurable.aemeasurable
    (hj.norm.pow 2).aestronglyMeasurable
  rw [hp.map_eq] at hi
  exact hi.symm

end AcceleratedLogConcave.Conditional.Centering
