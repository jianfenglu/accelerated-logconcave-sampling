import AcceleratedLogConcave.Conditional.JetBasics
import AcceleratedLogConcave.Analysis.Poisson.ReferenceFlow

/-! # Symmetry and operator bound of the first scaled jet, including zero time -/
noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory Analysis.Poisson
open scoped ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem hessian_heatPotential_eq_smul_firstScaledJet {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    hessianOperator (Gibbs.heatPotential (primitivePotential F x r) (conditionalVariance ρ))
      (ρ • y) = r • firstScaledJet F x r ρ y := by
  let B := primitivePotential F x r
  let t := conditionalVariance ρ
  let N : E → E := fun c ↦ ∫ z, primitiveObservable F x r z ∂Gibbs.heatPosterior B t c
  have hB := contDiff_primitivePotential hF x r
  have hb : ∀ z a, (0 : ℝ) * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z a a := by
    simpa [B] using primitivePotential_hessian_nonneg hF hlo x r
  have hu := primitivePotential_hessian_upper hF hup x r
  have ht := conditionalVariance_pos hρlo hρhi
  have heq : gradient (Gibbs.heatPotential B t) = fun c ↦ r • N c := by
    funext c
    have h := (Gibbs.heat_score_dictionary hB (le_refl 0) ht hb hu c).1
    change _ = ∫ z, gradient B z ∂Gibbs.heatPosterior B t c at h
    dsimp only [B] at h
    simp_rw [gradient_primitivePotential] at h
    simpa only [integral_smul] using h
  have hN : DifferentiableAt ℝ N (ρ • y) :=
    (Gibbs.contDiff_one_integral_heatPosterior hB (le_refl 0) ht hb
      (continuous_primitiveObservable hF x r) (‖gradient F 0‖ + |L| * ‖x‖)
      (|L| * |r|) (norm_primitiveObservable_le_affine hF hlo hup x r)).differentiable
        (by norm_num) (ρ • y)
  have hgrad := (gradient_hasFDerivAt_hessian
    (Gibbs.contDiff_two_heatPotential hB (le_refl 0) ht hb) (ρ • y)).fderiv
  rw [heq] at hgrad
  rw [← hgrad, fderiv_fun_const_smul hN r,
    fderiv_centerMean_eq_firstScaledJet hF hlo hup x r hρlo hρhi y]

/-- The first covariance jet is symmetric even at zero probability time. -/
theorem firstScaledJet_symmetric {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : r ≠ 0) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    (firstScaledJet F x r ρ y).IsSymmetric := by
  have hh := hessianOperator_symmetric
    (Gibbs.contDiff_two_heatPotential (contDiff_primitivePotential hF x r)
      (m := 0) (le_refl 0) (conditionalVariance_pos hρlo hρhi)
      (by simpa using primitivePotential_hessian_nonneg hF hlo x r)) (ρ • y)
  rw [hessian_heatPotential_eq_smul_firstScaledJet hF hlo hup x r hρlo hρhi y] at hh
  intro v w
  have h := hh v w
  change inner ℝ (r • firstScaledJet F x r ρ y v) w =
    inner ℝ v (r • firstScaledJet F x r ρ y w) at h
  simp only [inner_smul_left, inner_smul_right, conj_trivial] at h
  exact mul_left_cancel₀ hr h

/-- The sharp operator bound has no singularity at zero probability time. -/
theorem norm_firstScaledJet_le {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hL : 0 ≤ L) (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    ‖firstScaledJet F x r ρ y‖ ≤ r * L := by
  have hB := contDiff_primitivePotential hF x r
  have hb : ∀ z a, (0 : ℝ) * ‖a‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (primitivePotential F x r)) z a a := by
    simpa using primitivePotential_hessian_nonneg hF hlo x r
  have ht := conditionalVariance_pos hρlo hρhi
  have hH := Gibbs.contDiff_two_heatPotential hB (le_refl 0) ht hb
  have hbounds := Gibbs.heat_hessian_curvature hB (le_refl 0) ht hb
    (primitivePotential_hessian_upper hF hup x r)
  have hl : ∀ z a, (0 : ℝ) * ‖a‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (Gibbs.heatPotential (primitivePotential F x r)
        (conditionalVariance ρ))) z a a := by
    intro z a
    simpa using (hbounds z a).1
  have hn := hessianOperator_norm_le hH hl (fun z a ↦ (hbounds z a).2) (ρ • y)
  rw [hessian_heatPotential_eq_smul_firstScaledJet hF hlo hup x r hρlo hρhi y,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hn
  have hnonneg : 0 ≤ r ^ 2 * L := mul_nonneg (sq_nonneg r) hL
  simp only [abs_zero, abs_of_nonneg hnonneg, max_eq_right hnonneg] at hn
  apply (mul_le_mul_iff_right₀ hr).mp
  nlinarith [hn]

/-- The actual covariance operator is jointly smooth, including zero time. -/
theorem contDiffOn_firstScaledJet {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ firstScaledJet F x r p.1 p.2)
      {p | -1 < p.1 ∧ p.1 < 1} := by
  have hs := (continuousMultilinearCurryFin1 ℝ E E).contDiff.comp_contDiffOn
    (contDiffOn_scaledJet 1 hF hlo hup x r)
  apply hs.congr
  intro p hp
  ext v
  simp only [Function.comp_def, continuousMultilinearCurryFin1_apply,
    scaledJet, iteratedFDeriv_one_apply]
  exact (congrArg (fun T : E →L[ℝ] E ↦ T v)
    (fderiv_centerMean_eq_firstScaledJet hF hlo hup x r hp.1 hp.2 p.2)).symm

end AcceleratedLogConcave.Conditional
