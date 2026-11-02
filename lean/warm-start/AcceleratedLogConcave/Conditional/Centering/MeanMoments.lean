import AcceleratedLogConcave.Conditional.Centering.GaussianVariance
import AcceleratedLogConcave.Conditional.Stein.TransportLaw

/-! Actual conditional means retain their primitive mean under the interpolation
law. Gaussian transport then gives a dimension-explicit centered second moment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace AcceleratedLogConcave.Conditional
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Integrating the actual posterior mean recovers the primitive mean. -/
theorem integral_conditionalMean_eq_base_mean {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖^2)
    (x : E) (r : ℝ) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) :
    (∫ y, conditionalMean F x r ρ y ∂interpolationLaw F x r ρ) =
      ∫ z, primitiveObservable F x r z ∂baseLaw F x r := by
  let :=  baseLaw_isProbabilityMeasure hF hlo x r
  have hm : MemLp (primitiveObservable F x r) 2 (baseLaw F x r) :=
    Gibbs.memLp_two_heatPosterior_of_affine_bound (contDiff_primitivePotential hF x r)
      (m := 0) le_rfl (by norm_num) (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
      0 (continuous_primitiveObservable hF x r)
      (‖gradient F 0‖ + |ell| * ‖x‖) (|ell| * |r|)
      (norm_primitiveObservable_le_affine hF hlo hup x r)
  have hi := hm.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hd := conditional_disintegration_integral hF hlo x r ρ
    (conditionalVariance_pos hρlo hρhi)
    (fun q : E × E => primitiveObservable F x r q.2)
    ((continuous_primitiveObservable hF x r).comp continuous_snd).stronglyMeasurable
    (hi.comp_fst (stdGaussian E))
  change (∫ y, conditionalMean F x r ρ y ∂interpolationLaw F x r ρ) = _ at hd
  rw [hd]
  simp only [integral_fun_fst, probReal_univ, one_smul]

/-- The actual terminal mean has a centered second moment controlled through
its proved Gaussian probability transport. -/
theorem integral_conditionalMean_centered_norm_sq_le {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖^2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2) :
    (∫ y, ‖conditionalMean F x r b y -
      ∫ z, primitiveObservable F x r z ∂baseLaw F x r‖^2
      ∂interpolationLaw F x r b) ≤
      (Real.exp 1 * (r*ell))^2 * (Module.finrank ℝ E : ℝ) := by
  let T := forwardProbabilityTransport hF hell hlo hup x hr hb hb1 0
  let M := conditionalMean F x r b
  have hT : LipschitzWith ⟨Real.exp 1, (Real.exp_pos _).le⟩ T := by
    change LipschitzWith _ (fun y => convexProbabilityFlow hF hell hlo hup x hr hb
      (by norm_num) hb1 (projIcc 0 b hb 0) y b)
    exact lipschitzWith_convexProbabilityFlow_exp_one hF hell hlo hup x hr hb hb1 hsmall
      _ ⟨b,hb,le_rfl⟩
  have hM := lipschitzWith_conditionalMean hF hell hlo hup x hr
    (show -1 < b by linarith) hb1
  have hm := forwardProbabilityTransport_measurePreserving hF hell hlo hup x hr hb hb1
    (show 0 ∈ Icc 0 b from ⟨le_rfl,hb⟩)
  rw [interpolationLaw_zero hF hlo x r] at hm
  have hmean : (∫ w, M (T w) ∂stdGaussian E) =
      ∫ z, primitiveObservable F x r z ∂baseLaw F x r := by
    rw [hm.integral_comp T.measurableEmbedding]
    exact integral_conditionalMean_eq_base_mean hF hlo hup x r (by linarith) hb1
  have h := Centering.gaussian_centered_norm_sq_le (hM.comp hT)
  change (∫ z, ‖M (T z) - ∫ w, M (T w) ∂stdGaussian E‖^2 ∂stdGaussian E) ≤ _ at h
  rw [hmean] at h
  change (∫ z, ‖M (T z) - ∫ z, primitiveObservable F x r z ∂baseLaw F x r‖^2
    ∂stdGaussian E) ≤ (r*ell*Real.exp 1)^2 * (Module.finrank ℝ E : ℝ) at h
  have heq := hm.integral_comp T.measurableEmbedding
    (g := fun y => ‖M y - ∫ z, primitiveObservable F x r z ∂baseLaw F x r‖^2)
  rw [heq] at h
  simpa only [mul_comm (r*ell)] using h

end AcceleratedLogConcave.Conditional