import AcceleratedLogConcave.Conditional.Stein.Transport
import Mathlib.Analysis.Calculus.MeanValue

/-

-/
noncomputable section
open Set
namespace AcceleratedLogConcave.Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)

/-- Original curvature factor retained, including both time endpoints. -/
theorem norm_transportedJacobian_sub_id_le (hsmall : r ^ 2 * ell ≤ 1 / 2)
    {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) (y : E) :
    ‖transportedJacobian hF hell hlo hup x hr hb hb1 ρ y -
      ContinuousLinearMap.id ℝ E‖ ≤ Real.exp 1 * (r ^ 2 * ell) * (b - ρ) := by
  have hbound (t : ℝ) (ht : t ∈ Icc 0 b) :
      ‖(r * t) • (transportedJacobian hF hell hlo hup x hr hb hb1 t y).comp
        (firstScaledJet F x r t
          (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y))‖ ≤
        Real.exp 1 * (r ^ 2 * ell) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr.le ht.1)]
    calc
      _ ≤ (r * t) * (Real.exp 1 * (r * ell)) :=
        mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul (norm_transportedJacobian_le hF hell hlo hup x hr hb hb1 hsmall t y)
              (norm_firstScaledJet_le hF hell hlo hup x hr (by linarith [ht.1])
                (ht.2.trans_lt hb1) _) (norm_nonneg _) (Real.exp_pos _).le))
          (mul_nonneg hr.le ht.1)
      _ ≤ r * (Real.exp 1 * (r * ell)) :=
        mul_le_mul_of_nonneg_right (by nlinarith [ht.2])
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg hr.le hell))
      _ = _ := by ring
  have h := (convex_Icc (0 : ℝ) b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => transportedJacobian_deriv hF hell hlo hup x hr hb hb1 ht y)
    hbound ⟨hb, le_rfl⟩ hρ
  simpa only [transportedJacobian_terminal, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hρ.2), neg_sub] using h

theorem norm_fderiv_forwardProbabilityTransport_sub_id_le
    (hsmall : r ^ 2 * ell ≤ 1 / 2) {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) (y : E) :
    ‖fderiv ℝ (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ) y -
      ContinuousLinearMap.id ℝ E‖ ≤ Real.exp 1 * (r ^ 2 * ell) * (b - ρ) := by
  simpa only [transportedJacobian, backward_forwardProbabilityTransport] using
    norm_transportedJacobian_sub_id_le hF hell hlo hup x hr hb hb1 hsmall hρ
      (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y)

/-- The inverse orientation retains the same curvature factor. -/
theorem norm_fderiv_backwardProbabilityTransport_sub_id_le
    (hsmall : r ^ 2 * ell ≤ 1 / 2) {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) (y : E) :
    ‖fderiv ℝ (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ) y -
      ContinuousLinearMap.id ℝ E‖ ≤ Real.exp 2 * (r ^ 2 * ell) * (b - ρ) := by
  have hbρ : 0 ≤ b - ρ := sub_nonneg.mpr hρ.2
  let T := forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ
  let Y := backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ
  have hT := (contDiff_one_forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ).differentiable (by norm_num)
  have hY := (contDiff_one_backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ).differentiable (by norm_num)
  have hinv : (fderiv ℝ T (Y y)).comp (fderiv ℝ Y y) = ContinuousLinearMap.id ℝ E := by
    have h := (hT (Y y)).hasFDerivAt.comp y (hY y).hasFDerivAt
    have he : (fun z => T (Y z)) = id := by
      funext z
      exact forward_backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ z
    change HasFDerivAt (fun z => T (Y z))
      ((fderiv ℝ T (Y y)).comp (fderiv ℝ Y y)) y at h
    rw [he] at h
    exact h.unique (hasFDerivAt_id y)
  have hn : ‖fderiv ℝ Y y‖ ≤ Real.exp 1 := by
    exact norm_fderiv_le_of_lipschitz ℝ
      (lipschitzWith_convexProbabilityFlow_exp_one hF hell hlo hup x hr hb hb1 hsmall
        ⟨b, hb, le_rfl⟩ (projIcc 0 b hb ρ))
  have halg : fderiv ℝ Y y - ContinuousLinearMap.id ℝ E =
      (ContinuousLinearMap.id ℝ E - fderiv ℝ T (Y y)).comp (fderiv ℝ Y y) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp, hinv]
  rw [halg]
  calc
    _ ≤ ‖ContinuousLinearMap.id ℝ E - fderiv ℝ T (Y y)‖ * ‖fderiv ℝ Y y‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (Real.exp 1 * (r^2*ell) * (b-ρ)) * Real.exp 1 := by
      rw [norm_sub_rev]
      exact mul_le_mul
        (norm_fderiv_forwardProbabilityTransport_sub_id_le hF hell hlo hup x hr hb hb1 hsmall hρ (Y y))
        hn (norm_nonneg _) (by positivity)
    _ = _ := by rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]; ring
end AcceleratedLogConcave.Conditional
