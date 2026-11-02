import AcceleratedLogConcave.Conditional.PrimitivePullback
import AcceleratedLogConcave.Conditional.TiltCalculus

/-!
# Conditional jets: actual posterior mean and spatial estimates

The estimates below use the original C² potential and the proved heat
Hessian theorem. The public `Conditional.Jets` module also exports the
mixed-cumulant split bounds and smooth extension at probability time zero.
-/
noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem contDiff_one_conditionalMean {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) :
    ContDiff ℝ 1 (conditionalMean F x r ρ) := by
  exact contDiff_one_integral_center_tilt (contDiff_primitivePotential hF x r)
    (m := 0) (le_refl 0) (conditionalVariance_pos hρlo hρhi)
    (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
    (continuous_primitiveObservable hF x r) (‖gradient F 0‖ + |L| * ‖x‖)
    (|L| * |r|) ρ (norm_primitiveObservable_le_affine hF hlo hup x r)

theorem heatGradient_eq_smul_conditionalMean {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    gradient (Gibbs.heatPotential (primitivePotential F x r) (conditionalVariance ρ))
      (ρ • y) = r • conditionalMean F x r ρ y := by
  have h := (Gibbs.heat_score_dictionary (contDiff_primitivePotential hF x r)
    (m := 0) (le_refl 0) (conditionalVariance_pos hρlo hρhi)
    (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
    (primitivePotential_hessian_upper hF hup x r) (ρ • y)).1
  change _ = ∫ z, gradient (primitivePotential F x r) z ∂conditionalLaw F x r ρ y at h
  simp_rw [gradient_primitivePotential] at h
  simpa only [integral_smul, conditionalMean] using h

/-- A dimension-free spatial bound, sharper than the factor-two source bound. -/
theorem norm_conditionalMean_sub_le {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hL : 0 ≤ L) (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1)
    (y w : E) :
    ‖conditionalMean F x r ρ y - conditionalMean F x r ρ w‖ ≤
      (|ρ| * r * L) * ‖y - w‖ := by
  let B := primitivePotential F x r
  let H := Gibbs.heatPotential B (conditionalVariance ρ)
  have hB := contDiff_primitivePotential hF x r
  have hb : ∀ z a, (0 : ℝ) * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ B) z a a := by
    simpa [B] using primitivePotential_hessian_nonneg hF hlo x r
  have hu := primitivePotential_hessian_upper hF hup x r
  have ht := conditionalVariance_pos hρlo hρhi
  have hH : ContDiff ℝ 2 H := Gibbs.contDiff_two_heatPotential hB (le_refl 0) ht hb
  have hbounds := Gibbs.heat_hessian_curvature hB (le_refl 0) ht hb hu
  have hHlo : ∀ z a, (0 : ℝ) * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ H) z a a := by
    intro z a
    simpa [H] using (hbounds z a).1
  obtain ⟨_, heq, _, _, hnorm⟩ :=
    AutoSamplingTheory.TechnicalLemmas.Analysis.HessianSecantOperator.hessian_secant_operator
      hH hHlo (fun z a ↦ (hbounds z a).2) (ρ • y) (ρ • w)
  have hnonneg : 0 ≤ r ^ 2 * L := mul_nonneg (sq_nonneg r) hL
  have hd : ‖gradient H (ρ • y) - gradient H (ρ • w)‖ ≤
      (r ^ 2 * L) * (|ρ| * ‖y - w‖) := by
    rw [heq]
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    simpa only [abs_zero, abs_of_nonneg hnonneg, max_eq_right hnonneg,
      ← smul_sub, norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg (ρ • y - ρ • w))
  rw [heatGradient_eq_smul_conditionalMean hF hlo hup x r hρlo hρhi y,
    heatGradient_eq_smul_conditionalMean hF hlo hup x r hρlo hρhi w,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hd
  apply (mul_le_mul_iff_right₀ hr).mp
  nlinarith [hd]

/-- A common Lipschitz coefficient on every compact probability-time interval. -/
theorem lipschitzWith_conditionalMean {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hL : 0 ≤ L) (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) :
    LipschitzWith ⟨r * L, mul_nonneg hr.le hL⟩ (conditionalMean F x r ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro y w
  simp only [dist_eq_norm]
  apply (norm_conditionalMean_sub_le hF hL hlo hup x hr hρlo hρhi y w).trans
  have ha : |ρ| ≤ 1 := abs_le.mpr ⟨hρlo.le, hρhi.le⟩
  have hc : |ρ| * r * L ≤ r * L := by
    nlinarith [mul_nonneg hr.le hL, mul_le_mul_of_nonneg_right ha (mul_nonneg hr.le hL)]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

/-- Pure scaling identity. The analytic center regularity premise is supplied
by the positive-variance tilt theorem; the identity itself includes `ρ = 0`. -/
theorem iteratedFDeriv_conditionalMean_eq_scaledJet (q : ℕ) (F : E → ℝ)
    (x : E) (r ρ : ℝ)
    (hc : ContDiff ℝ q (fun c : E ↦ ∫ z, primitiveObservable F x r z ∂
      Gibbs.heatPosterior (primitivePotential F x r) (conditionalVariance ρ) c)) (y : E) :
    iteratedFDeriv ℝ q (conditionalMean F x r ρ) y = ρ ^ q • scaledJet q F x r ρ y := by
  exact congrFun (iteratedFDeriv_comp_const_smul ρ hc) y

/-- Source-facing scaling, with center regularity discharged from the original
C² hypotheses. Together with `contDiffOn_scaledJet` this realizes the smooth
extension of `ρ⁻q D_y^q M` rather than postulating it. -/
theorem iteratedFDeriv_conditionalMean_eq_scaledJet_of_curvature (q : ℕ)
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : E) :
    iteratedFDeriv ℝ q (conditionalMean F x r ρ) y = ρ ^ q • scaledJet q F x r ρ y := by
  apply iteratedFDeriv_conditionalMean_eq_scaledJet
  have hs := Tilt.contDiffOn_integral_heatPosterior (contDiff_primitivePotential hF x r)
    (m := 0) (le_refl 0)
    (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
    (continuous_primitiveObservable hF x r) (‖gradient F 0‖ + |L| * ‖x‖)
    (|L| * |r|) 1 (by simpa only [pow_one] using
      norm_primitiveObservable_le_affine hF hlo hup x r)
  have hc : ContDiff ℝ ∞ (fun c : E ↦ ∫ z, primitiveObservable F x r z ∂
      Gibbs.heatPosterior (primitivePotential F x r) (conditionalVariance ρ) c) := by
    apply contDiff_iff_contDiffAt.mpr
    intro c
    have hp := hs.contDiffAt (x := (conditionalVariance ρ, c))
      (Tilt.isOpen_gaussianDomain.mem_nhds (conditionalVariance_pos hρlo hρhi))
    have hm : ContDiffAt ℝ ∞ (fun z : E ↦ (conditionalVariance ρ, z)) c :=
      contDiffAt_const.prodMk contDiffAt_id
    have hh := hp.comp c hm
    simpa only [Function.comp_def] using hh
  exact hc.of_le (by simp)

/-- Away from probability time zero the smooth jet is exactly the inverse-scaled
spatial derivative. The definition and its smoothness also cover zero. -/
theorem scaledJet_eq_inv_smul_iteratedFDeriv (q : ℕ)
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1)
    (hρ : ρ ≠ 0) (y : E) :
    scaledJet q F x r ρ y = (ρ ^ q)⁻¹ •
      iteratedFDeriv ℝ q (conditionalMean F x r ρ) y := by
  rw [iteratedFDeriv_conditionalMean_eq_scaledJet_of_curvature q hF hlo hup x r
    hρlo hρhi y, inv_smul_smul₀ (pow_ne_zero q hρ)]

end AcceleratedLogConcave.Conditional
