import AcceleratedLogConcave.Oracle.PrivateSamplingOriginalBounds

/-! Actual benchmark-center scale moments needed to average the lower-depth
retained error. The Gaussian source path is the same conditional sampling flow. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
namespace AcceleratedLogConcave.Oracle.PrivateBenchmarkMoments
open Numerics SamplingGaussianJetLp PrivateSamplingOriginalBounds
open Analysis.PositiveVarianceSlab
variable {D : ℕ} (d : SamplingCenterLp.Data (Fin D)) (x : EuclideanSpace ℝ (Fin D))
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "γ" => stdGaussian E

theorem initial_path_norm : ‖jetLp d x 0 0‖ = Real.sqrt (Module.finrank ℝ E) := by
  have hh : ‖jetLp d x 0 0‖^2 = (Module.finrank ℝ E : ℝ) := by
    rw [jetLp,Analysis.DominatedLp.norm_sq_toLp]
    simp only [seedJet_zero_initial]
    exact Gibbs.integral_norm_sq_stdGaussian
  have hs := Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℝ E))
  nlinarith [norm_nonneg (jetLp d x 0 0),Real.sqrt_nonneg (Module.finrank ℝ E)]

/-- Explicit path norm from the actual Gaussian initial state and its signed
strong flow equation, retaining the original center gradient in replyBudget. -/
theorem path_norm (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖jetLp d x 0 t‖ ≤ Real.sqrt (Module.finrank ℝ E) + d.r*t*replyBudget d x := by
  have hint : IntervalIntegrable (jetLp d x 1) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1
      ((jetLp_contDiffOn d x 1 0).continuousOn.mono (fun u hu =>
        source_subset d.hb d.hb1 ⟨hu.1,hu.2.trans ht.2⟩))
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => jetLp_deriv d x 0 (source_subset d.hb d.hb1 (by
      rw [uIcc_of_le ht.1] at hu
      exact ⟨hu.1,hu.2.trans ht.2⟩))) hint
  have hjet (s : ℝ) : jetLp d x 1 s = (-d.r) • meanLp d x s := by
    simp only [meanLp,smul_smul,mul_inv_cancel₀ (neg_ne_zero.mpr d.hr.ne'),one_smul]
  simp_rw [hjet,intervalIntegral.integral_smul] at H
  have hi : ‖∫ s in 0..t, meanLp d x s‖ ≤ t*replyBudget d x := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := t) (f := meanLp d x) (fun s hs =>
      meanLp_norm_le d x hsmall (by rw [uIoc_of_le ht.1] at hs; exact ⟨hs.1.le,hs.2.trans ht.2⟩))
    simpa only [sub_zero,abs_of_nonneg ht.1,mul_comm] using hh
  have he : jetLp d x 0 t = jetLp d x 0 0 + (-d.r) • (∫ s in 0..t,meanLp d x s) := by
    rw [H]; abel
  rw [he]
  calc
    _ ≤ ‖jetLp d x 0 0‖ + ‖(-d.r) • (∫ s in 0..t,meanLp d x s)‖ := norm_add_le _ _
    _ = Real.sqrt (Module.finrank ℝ E) + d.r*‖∫ s in 0..t,meanLp d x s‖ := by
      rw [initial_path_norm,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos d.hr]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hi d.hr.le]

def scale (t : ℝ) (z : E) : ℝ := Gibbs.primitiveScale d.F (x+(d.r*t) • seedJet d x 0 t z)

theorem scale_le {t : ℝ} (ht : t ∈ Icc 0 d.b) (z : E) :
    scale d x t z ≤ Gibbs.primitiveScale d.F x + (d.ell*d.r*t)*‖seedJet d x 0 t z‖ := by
  have hh := Gibbs.norm_primitive_score_sub_gradient_le d.hF d.hell d.hlo d.hup
    (mul_nonneg d.hr.le ht.1) x (seedJet d x 0 t z)
  have hn := norm_add_le (gradient d.F (x+(d.r*t) • seedJet d x 0 t z)-gradient d.F x)
    (gradient d.F x)
  rw [sub_add_cancel] at hn
  unfold scale Gibbs.primitiveScale
  nlinarith

theorem scale_memLp {t : ℝ} (ht : t ∈ Icc 0 d.b) : MemLp (scale d x t) 2 γ := by
  have hn : MemLp (fun z : E => ‖seedJet d x 0 t z‖) 2 γ :=
    (seedJet_memLp d x 0 t).norm
  have hc : MemLp (fun _ : E => Gibbs.primitiveScale d.F x) 2 γ := memLp_const _
  have hmul : MemLp (fun z : E => (d.ell*d.r*t)*‖seedJet d x 0 t z‖) 2 γ :=
    hn.const_mul (d.ell*d.r*t)
  have hb : MemLp (fun z : E => Gibbs.primitiveScale d.F x +
      (d.ell*d.r*t)*‖seedJet d x 0 t z‖) 2 γ :=
    hc.add hmul
  refine hb.mono' ?_ ?_
  · have hg := (Gibbs.gradient_lipschitz_of_hessian_bounds d.hF d.hell d.hlo d.hup).continuous
    have hpath : Continuous (fun z : E => seedJet d x 0 t z) :=
      (continuous_seedJet d x 0).comp (continuous_const.prodMk continuous_id)
    have hcenter : Continuous (fun z : E => x+(d.r*t) • seedJet d x 0 t z) :=
      continuous_const.add (hpath.const_smul (d.r*t))
    exact (continuous_const.add (hg.comp hcenter).norm).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ scale d x t z from Gibbs.primitiveScale_nonneg _ _)]
    exact scale_le d x ht z

/-- Integrability of the actual center-dependent squared lower-child payment.
This discharges the averaging requirement; fibrewise L2 alone would not. -/
theorem scale_square_integrable {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    Integrable (fun z => scale d x t z ^ 2) γ := (scale_memLp d x ht).integrable_sq

/-- Explicit scalar payment for the actual benchmark-center primitive scale.
All dimension, curvature, radius and source-time dependence is visible. -/
def squareBudget (t : ℝ) : ℝ :=
  2*(Gibbs.primitiveScale d.F x)^2 + 2*(d.ell*d.r*t)^2 *
    (Real.sqrt (Module.finrank ℝ E)+d.r*t*replyBudget d x)^2

theorem scale_square_integral_le (hsmall : d.r^2*d.ell ≤ 1/2)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    (∫ z, scale d x t z ^ 2 ∂γ) ≤ squareBudget d x t := by
  let B := Gibbs.primitiveScale d.F x
  let a := d.ell*d.r*t
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg d.hell d.hr.le) ht.1
  have hB : 0 ≤ B := Gibbs.primitiveScale_nonneg _ _
  have hy : Integrable (fun z : E => ‖seedJet d x 0 t z‖^2) γ :=
    (seedJet_memLp d x 0 t).norm.integrable_sq
  have hh : (∫ z, scale d x t z ^ 2 ∂γ) ≤
      ∫ z : E, 2*B^2+2*a^2*‖seedJet d x 0 t z‖^2 ∂γ := by
    apply integral_mono (scale_square_integrable d x ht)
      ((integrable_const _).add (hy.const_mul _))
    intro z
    have hs := scale_le d x ht z
    have hs0 : 0 ≤ scale d x t z := Gibbs.primitiveScale_nonneg _ _
    have hnn := norm_nonneg (seedJet d x 0 t z)
    change scale d x t z ≤ B+a*‖seedJet d x 0 t z‖ at hs
    have hsq := (sq_le_sq₀ hs0 (add_nonneg hB (mul_nonneg ha hnn))).2 hs
    change scale d x t z ^ 2 ≤ 2*B^2+2*a^2*‖seedJet d x 0 t z‖^2
    nlinarith [sq_nonneg (B-a*‖seedJet d x 0 t z‖)]
  rw [integral_add (integrable_const _) (hy.const_mul _)] at hh
  simp only [integral_const,probReal_univ,one_smul,integral_const_mul] at hh
  have hp : (∫ z, ‖seedJet d x 0 t z‖^2 ∂γ) = ‖jetLp d x 0 t‖^2 :=
    (Analysis.DominatedLp.norm_sq_toLp (seedJet_memLp d x 0 t)).symm
  rw [hp] at hh
  have hpath := path_norm d x hsmall ht
  have hsquare : ‖jetLp d x 0 t‖^2 ≤
      (Real.sqrt (Module.finrank ℝ E)+d.r*t*replyBudget d x)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity [d.hr.le,ht.1,replyBudget_nonneg d x])).2 hpath
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 2*a^2 by positivity)) _)


section Actual
open Numerics.AffineGraph
variable {m n : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  {F : EuclideanSpace ℝ (Fin D) → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  {r : ℝ} (hr : 0 < r)

theorem scale_eq_node (i : Fin n) (z : EuclideanSpace ℝ (Fin D)) :
    scale (PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr) x (S.mesh.location m (e i)) z =
      Gibbs.primitiveScale F (PrivateConditionalFlowConsumer.nodePhi S e hF hell hlo hup x hr i z) := by
  have hi := S.mesh.location_mem_interval m (e i)
  unfold scale
  rw [seedJet_zero_source _ x ⟨hi.1.le,hi.2.le⟩]
  rfl

/-- Concrete integrable child-scale payment on the actual benchmark nodes. -/
theorem node_scale_square_integrable (i : Fin n) :
    Integrable (fun z : EuclideanSpace ℝ (Fin D) => (Gibbs.primitiveScale F
      (PrivateConditionalFlowConsumer.nodePhi S e hF hell hlo hup x hr i z))^2) γ := by
  have hi := S.mesh.location_mem_interval m (e i)
  simpa only [scale_eq_node x S e hF hell hlo hup hr] using
    scale_square_integrable (PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr) x ⟨hi.1.le,hi.2.le⟩

theorem node_scale_square_integral_le (hsmall : r^2*ell ≤ 1/2) (i : Fin n) :
    (∫ z : EuclideanSpace ℝ (Fin D), (Gibbs.primitiveScale F
      (PrivateConditionalFlowConsumer.nodePhi S e hF hell hlo hup x hr i z))^2 ∂γ) ≤
      squareBudget (PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr) x (S.mesh.location m (e i)) := by
  have hi := S.mesh.location_mem_interval m (e i)
  simpa only [scale_eq_node x S e hF hell hlo hup hr] using
    scale_square_integral_le (PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr) x hsmall ⟨hi.1.le,hi.2.le⟩
end Actual

end AcceleratedLogConcave.Oracle.PrivateBenchmarkMoments
