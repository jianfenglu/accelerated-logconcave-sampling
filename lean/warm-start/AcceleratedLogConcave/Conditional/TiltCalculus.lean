import AcceleratedLogConcave.Gibbs.HeatHessian
import AcceleratedLogConcave.Conditional.Tilt.HeatIntegral
import AcceleratedLogConcave.Conditional.PrimitivePullback
import AcceleratedLogConcave.Conditional.Tilt.VectorCovariance

/-!
# Differentiation of the actual Gaussian conditional tilt

The base potential and observable are fixed functions of the integrated variable.
Consequently differentiating the Gaussian center never differentiates the base
observable. In particular the original potential only needs its C² hypotheses.
-/

noncomputable section

namespace AcceleratedLogConcave.Conditional

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The expectation of any continuous affine-growth observable is C¹ in the
conditional center, including a zero interpolation coefficient. The local
integrable Gaussian derivative envelope is proved in `Gibbs.HeatHessian`. -/
theorem contDiff_one_integral_center_tilt
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {B : E → ℝ} {m t : ℝ} (hB : ContDiff ℝ 2 B) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z v v)
    {g : E → G} (hg : Continuous g) (A C ρ : ℝ)
    (hbound : ∀ z, ‖g z‖ ≤ A + C * ‖z‖) :
    ContDiff ℝ 1 (fun y ↦ ∫ z, g z ∂Gibbs.heatPosterior B t (ρ • y)) := by
  exact (Gibbs.contDiff_one_integral_heatPosterior hB hm ht hlo hg A C hbound).comp
    (contDiff_const.smul contDiff_id)

/-- Linear-tilt differentiation of a scalar observable. This is a covariance
under the normalized posterior, with the interpolation factor retained. -/
theorem fderiv_integral_center_tilt_eq_covariance
    {B : E → ℝ} {m t : ℝ} (hB : ContDiff ℝ 2 B) (hm : 0 ≤ m) (ht : 0 < t)
    (hlo : ∀ z v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z v v)
    {g : E → ℝ} (hg : Continuous g) (A C ρ : ℝ)
    (hbound : ∀ z, ‖g z‖ ≤ A + C * ‖z‖) (y v : E) :
    fderiv ℝ (fun y ↦ ∫ z, g z ∂Gibbs.heatPosterior B t (ρ • y)) y v =
      (ρ / t) * cov[g, fun z ↦ inner ℝ z v; Gibbs.heatPosterior B t (ρ • y)] := by
  change fderiv ℝ ((fun c ↦ ∫ z, g z ∂Gibbs.heatPosterior B t c) ∘
    (fun y : E ↦ ρ • y)) y v = _
  rw [fderiv_comp y
    (Gibbs.hasFDerivAt_integral_heatPosterior hB hm ht hlo hg A C hbound
      (ρ • y)).differentiableAt
    ((hasFDerivAt_id y).const_smul ρ).differentiableAt]
  have hs : fderiv ℝ (HSMul.hSMul ρ : E → E) y =
      ρ • ContinuousLinearMap.id ℝ E := by
    exact ((hasFDerivAt_id y).const_smul ρ).fderiv
  rw [hs]
  change (fderiv ℝ (fun c ↦ ∫ z, g z ∂Gibbs.heatPosterior B t c) (ρ • y))
      (ρ • v) = _
  rw [map_smul, smul_eq_mul,
    Gibbs.fderiv_integral_heatPosterior_eq_covariance hB hm ht hlo hg A C hbound]
  rw [div_eq_mul_inv]
  ring

set_option maxHeartbeats 1000000 in
/-- Joint smoothness through probability time zero for the actual conditional
mean. Gaussian differentiation uses no derivatives of the observable. -/
theorem contDiffOn_conditionalMean {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ conditionalMean F x r p.1 p.2)
      {p | -1 < p.1 ∧ p.1 < 1} := by
  have hs := Tilt.contDiffOn_integral_heatPosterior (contDiff_primitivePotential hF x r)
    (m := 0) (le_refl 0)
    (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
    (continuous_primitiveObservable hF x r) (‖gradient F 0‖ + |L| * ‖x‖)
    (|L| * |r|) 1 (by simpa only [pow_one] using
      norm_primitiveObservable_le_affine hF hlo hup x r)
  have hp : ContDiff ℝ ∞ (fun p : ℝ × E ↦ (conditionalVariance p.1, p.1 • p.2)) := by
    unfold conditionalVariance
    fun_prop
  simpa only [conditionalMean, conditionalLaw, Function.comp_def] using
    hs.comp hp.contDiffOn (fun p hpt ↦ conditionalVariance_pos hpt.1 hpt.2)

set_option maxHeartbeats 1000000 in
/-- All scaled jets, defined without division by probability time, are jointly
smooth on the open interval `(-1,1)`, including its interior point zero. -/
theorem contDiffOn_scaledJet (q : ℕ) {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ scaledJet q F x r p.1 p.2)
      {p | -1 < p.1 ∧ p.1 < 1} := by
  have hs := Tilt.contDiffOn_centerJet_integral_heatPosterior
    (contDiff_primitivePotential hF x r) (m := 0) (le_refl 0)
    (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
    (continuous_primitiveObservable hF x r) (‖gradient F 0‖ + |L| * ‖x‖)
    (|L| * |r|) 1 q (by simpa only [pow_one] using
      norm_primitiveObservable_le_affine hF hlo hup x r)
  have hp : ContDiff ℝ ∞ (fun p : ℝ × E ↦ (conditionalVariance p.1, p.1 • p.2)) := by
    unfold conditionalVariance
    fun_prop
  simpa only [scaledJet, Function.comp_def] using
    hs.comp hp.contDiffOn (fun p hpt ↦ conditionalVariance_pos hpt.1 hpt.2)

/-- The first division-free scaled jet is the derivative in the Gaussian
posterior center, including at probability time zero. -/
theorem fderiv_centerMean_eq_firstScaledJet {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    fderiv ℝ (fun c ↦ ∫ z, primitiveObservable F x r z ∂
      Gibbs.heatPosterior (primitivePotential F x r) (conditionalVariance ρ) c) (ρ • y) =
      firstScaledJet F x r ρ y := by
  simpa only [firstScaledJet, conditionalPositionMean, conditionalMean, conditionalLaw] using
    Tilt.fderiv_integral_heatPosterior_eq_vectorCovariance
      (contDiff_primitivePotential hF x r) (m := 0) (le_refl 0)
      (conditionalVariance_pos hρlo hρhi)
      (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
      (continuous_primitiveObservable hF x r) (‖gradient F 0‖ + |L| * ‖x‖)
      (|L| * |r|) (norm_primitiveObservable_le_affine hF hlo hup x r) (ρ • y)

/-- Spatial differentiation of the actual conditional mean equals probability
time times the first scaled jet. -/
theorem fderiv_conditionalMean_eq_smul_firstScaledJet {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    fderiv ℝ (conditionalMean F x r ρ) y = ρ • firstScaledJet F x r ρ y := by
  let N : E → E := fun c ↦ ∫ z, primitiveObservable F x r z ∂
    Gibbs.heatPosterior (primitivePotential F x r) (conditionalVariance ρ) c
  have hN := Gibbs.contDiff_one_integral_heatPosterior
    (contDiff_primitivePotential hF x r) (m := 0) (le_refl 0)
    (conditionalVariance_pos hρlo hρhi)
    (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
    (continuous_primitiveObservable hF x r) (‖gradient F 0‖ + |L| * ‖x‖)
    (|L| * |r|) (norm_primitiveObservable_le_affine hF hlo hup x r)
  have heq : conditionalMean F x r ρ = N ∘ (ρ • id) := rfl
  have hNd : DifferentiableAt ℝ N (ρ • y) := hN.differentiable (by norm_num) (ρ • y)
  have hsd : HasFDerivAt (ρ • id : E → E) (ρ • ContinuousLinearMap.id ℝ E) y :=
    (hasFDerivAt_id y).const_smul ρ
  have hcomp : fderiv ℝ (N ∘ (ρ • id)) y =
      (fderiv ℝ N (ρ • y)).comp (ρ • ContinuousLinearMap.id ℝ E) :=
    (hNd.hasFDerivAt.comp y hsd).fderiv
  rw [heq, hcomp]
  change (fderiv ℝ N (ρ • y)).comp (ρ • ContinuousLinearMap.id ℝ E) = _
  have hh : fderiv ℝ N (ρ • y) = firstScaledJet F x r ρ y :=
    fderiv_centerMean_eq_firstScaledJet hF hlo hup x r hρlo hρhi y
  rw [hh]
  ext v
  simp

end AcceleratedLogConcave.Conditional
