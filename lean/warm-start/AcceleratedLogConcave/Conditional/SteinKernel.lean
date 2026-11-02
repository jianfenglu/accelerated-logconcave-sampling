import AcceleratedLogConcave.Conditional.Stein.TimeRegularity
import AcceleratedLogConcave.Conditional.Stein.LogarithmicIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The actual transported Stein integral

The transpose convention agrees with equation (oa:eq:stein-kernel): the
integrand is `Bρ ∘ U₁(ρ,Yρ)`. Its value at zero is given by this first
integral, so no singular division is part of the definition.
-/

noncomputable section
set_option maxHeartbeats 1600000
open Set Function MeasureTheory
open scoped Topology NNReal ContDiff

namespace AcceleratedLogConcave.Conditional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)

/-- The nonsingular operator-valued integrand of the transported Stein kernel. -/
def transportedSteinIntegrand (ρ : ℝ) (y : E) : E →L[ℝ] E :=
  (transportedJacobian hF hell hlo hup x hr hb hb1 ρ y).comp
    (firstScaledJet F x r ρ
      (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y))

/-- The source's `Kᵀ`, constructed from the actual probability transport. -/
def transportedSteinKernelTranspose (y : E) : E →L[ℝ] E :=
  ∫ ρ in 0..b, transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y

theorem continuousOn_transportedSteinIntegrand (y : E) :
    ContinuousOn (fun ρ => transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y)
      (Icc 0 b) := by
  have hU : ContinuousOn (fun p : ℝ × E => firstScaledJet F x r p.1 p.2)
      {p | -1 < p.1 ∧ p.1 < 1} :=
    (contDiffOn_firstScaledJet hF hlo hup x r).continuousOn
  have hY : ContinuousOn (fun t =>
      (t, backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)) (Icc 0 b) :=
    continuousOn_id.prodMk
      (continuous_backwardProbabilityTransport hF hell hlo hup x hr hb hb1 y).continuousOn
  exact (continuousOn_transportedJacobian hF hell hlo hup x hr hb hb1 y).clm_comp
    (hU.comp hY (fun t ht => ⟨by change -1 < t; linarith [ht.1], ht.2.trans_lt hb1⟩))

/-- The defining first integral is an honest Bochner integral on the full
closed probability-time interval, including its nonsingular zero endpoint. -/
theorem intervalIntegrable_transportedSteinIntegrand (y : E) :
    IntervalIntegrable (fun ρ => transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y)
      volume 0 b :=
  (continuousOn_transportedSteinIntegrand hF hell hlo hup x hr hb hb1 y).intervalIntegrable_of_Icc hb

theorem continuous_transportedSteinIntegrand_joint :
    Continuous (fun p : E × Icc 0 b =>
      transportedSteinIntegrand hF hell hlo hup x hr hb hb1 p.2 p.1) := by
  have hp : Continuous (fun p : E × Icc 0 b =>
      ((p.2 : ℝ), backwardProbabilityTransport hF hell hlo hup x hr hb hb1 p.2 p.1)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_backwardProbabilityTransport_joint hF hell hlo hup x hr hb hb1)
  have hU : Continuous (fun p : E × Icc 0 b => firstScaledJet F x r p.2
      (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 p.2 p.1)) :=
    (contDiffOn_firstScaledJet hF hlo hup x r).continuousOn.comp_continuous hp
      (fun p => ⟨by change -1 < (p.2 : ℝ); linarith [p.2.2.1], p.2.2.2.trans_lt hb1⟩)
  exact (continuous_transportedJacobian_joint hF hell hlo hup x hr hb hb1).clm_comp hU

/-- The genuine first derivative in probability time, in a form with no
division at zero. -/
def transportedJacobianTimeDerivative (ρ : ℝ) (y : E) : E →L[ℝ] E :=
  (r * ρ) • transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y

/-- The genuine second derivative within the closed probability interval. -/
def transportedJacobianSecondTimeDerivative (ρ : ℝ) (y : E) : E →L[ℝ] E :=
  derivWithin (fun t => transportedJacobianTimeDerivative hF hell hlo hup x hr hb hb1 t y)
    (Icc 0 b) ρ

theorem contDiffOn_transportedSteinIntegrand (hbpos : 0 < b) (y : E) :
    ContDiffOn ℝ ∞ (fun ρ => transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y)
      (Icc 0 b) :=
  (contDiffOn_transportedJacobian hF hell hlo hup x hr hb hb1 hbpos y).clm_comp
    ((contDiffOn_firstScaledJet hF hlo hup x r).comp
      (contDiffOn_id.prodMk
        (contDiffOn_backwardProbabilityTransport hF hell hlo hup x hr hb hb1 hbpos y))
      (fun t ht => ⟨by change -1 < t; linarith [ht.1], ht.2.trans_lt hb1⟩))

theorem contDiffOn_transportedJacobianTimeDerivative (hbpos : 0 < b) (y : E) :
    ContDiffOn ℝ ∞ (fun ρ => transportedJacobianTimeDerivative hF hell hlo hup x hr hb hb1 ρ y)
      (Icc 0 b) :=
  (contDiffOn_const.mul contDiffOn_id).smul
    (contDiffOn_transportedSteinIntegrand hF hell hlo hup x hr hb hb1 hbpos y)

/-- The second displayed Stein integral, with its zero endpoint justified by
the nonsingular first integral. -/
theorem transportedSteinKernelTranspose_eq_divided_derivative (y : E) :
    transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 y =
      r⁻¹ • ∫ ρ in 0..b, ρ⁻¹ •
        transportedJacobianTimeDerivative hF hell hlo hup x hr hb hb1 ρ y := by
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr_uIoo
  intro ρ hρ
  have hρ' : ρ ∈ Ioo 0 b := by simpa only [uIoo_of_le hb] using hρ
  simp only [transportedJacobianTimeDerivative, smul_smul]
  have he : r⁻¹ * (ρ⁻¹ * (r * ρ)) = 1 := by field_simp [hr.ne', hρ'.1.ne']
  rw [he, one_smul]

/-- The logarithmic characterization uses the actual second derivative of
the transported Jacobian, with the zero boundary term proved analytically. -/
theorem transportedSteinKernelTranspose_eq_logarithmic (hbpos : 0 < b) (y : E) :
    transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 y =
      r⁻¹ • ∫ ρ in 0..b, Real.log (b / ρ) •
        transportedJacobianSecondTimeDerivative hF hell hlo hup x hr hb hb1 ρ y := by
  rw [transportedSteinKernelTranspose_eq_divided_derivative]
  congr 1
  have hC := contDiffOn_transportedJacobianTimeDerivative hF hell hlo hup x hr hb hb1 hbpos y
  apply Stein.integral_inv_smul_eq_log_smul_deriv hbpos hC.continuousOn
    (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hbpos) (by norm_num))
    (fun t ht => (hC.differentiableOn (by norm_num) t ht).hasDerivWithinAt)
  simp only [transportedJacobianTimeDerivative, mul_zero, zero_smul]

theorem norm_transportedSteinIntegrand_le (hsmall : r ^ 2 * ell ≤ 1 / 2)
    {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) (y : E) :
    ‖transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y‖ ≤
      Real.exp 1 * (r * ell) := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact mul_le_mul
    (norm_transportedJacobian_le hF hell hlo hup x hr hb hb1 hsmall ρ y)
    (norm_firstScaledJet_le hF hell hlo hup x hr
      (by linarith [hρ.1]) (hρ.2.trans_lt hb1) _)
    (norm_nonneg _) (Real.exp_pos _).le

/-- A slightly sharper version of the source bound, with smoothing terminal
time retained explicitly. -/
theorem norm_transportedSteinKernelTranspose_le_terminal
    (hsmall : r ^ 2 * ell ≤ 1 / 2) (y : E) :
    ‖transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 y‖ ≤
      Real.exp 1 * (r * ell) * b := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := b) (C := Real.exp 1 * (r * ell))
    (f := fun ρ => transportedSteinIntegrand hF hell hlo hup x hr hb hb1 ρ y)
    (fun ρ hρ => norm_transportedSteinIntegrand_le hF hell hlo hup x hr hb hb1
      hsmall (by rw [uIoc_of_le hb] at hρ; exact ⟨hρ.1.le, hρ.2⟩) y)
  simpa only [transportedSteinKernelTranspose, sub_zero, abs_of_nonneg hb] using h

/-- The manuscript's dimension-free `2 e L` bound for `L = r ell`. -/
theorem norm_transportedSteinKernelTranspose_le (hsmall : r ^ 2 * ell ≤ 1 / 2)
    (y : E) :
    ‖transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 y‖ ≤
      2 * Real.exp 1 * (r * ell) := by
  apply (norm_transportedSteinKernelTranspose_le_terminal hF hell hlo hup x hr hb hb1
    hsmall y).trans
  have hp : 0 ≤ Real.exp 1 * (r * ell) :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg hr.le hell)
  nlinarith

end AcceleratedLogConcave.Conditional
