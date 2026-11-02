import AcceleratedLogConcave.Conditional.ProbabilityFlow
import AcceleratedLogConcave.Conditional.FirstJet
import AcceleratedLogConcave.Conditional.Stein.JacobianODE

/-! # Actual transports used by the transported Stein kernel

All maps in this file are the complete ODE flow of the conditional mean.
The two orientations are inverse maps, with their spatial differentiability
derived from the constructed ODE rather than assumed.
-/

noncomputable section
open Set Function MeasureTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional
open OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)

/-- The actual transport from probability time `ρ` to the fixed terminal time.
Clipping gives a harmless total definition outside the construction interval. -/
def forwardProbabilityTransport (ρ : ℝ) : E ≃ₜ E :=
  convexProbabilityFlowHomeomorph hF hell hlo hup x hr hb (by norm_num) hb1
    (projIcc 0 b hb ρ) ⟨b, hb, le_rfl⟩

/-- The inverse transport from the terminal interpolation law. -/
def backwardProbabilityTransport (ρ : ℝ) : E ≃ₜ E :=
  (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ).symm

@[simp] theorem forward_backwardProbabilityTransport (ρ : ℝ) (y : E) :
    forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ
      (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y) = y :=
  (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ).apply_symm_apply y

@[simp] theorem backward_forwardProbabilityTransport (ρ : ℝ) (y : E) :
    backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ
      (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y) = y :=
  (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ).symm_apply_apply y

/-- The backward map is the actual trajectory started at the terminal point. -/
theorem backwardProbabilityTransport_eq_flow (ρ : ℝ) (y : E) :
    backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y =
      convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
        ⟨b, hb, le_rfl⟩ y (projIcc 0 b hb ρ) := rfl

@[simp] theorem forwardProbabilityTransport_terminal (y : E) :
    forwardProbabilityTransport hF hell hlo hup x hr hb hb1 b y = y := by
  change convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
    (projIcc 0 b hb b) y b = y
  rw [projIcc_of_mem hb ⟨hb, le_rfl⟩]
  exact convexProbabilityFlow_initial hF hell hlo hup x hr hb (by norm_num) hb1 _ y

/-- Spatial derivative of the clipped source velocity. -/
def clippedConditionalVelocityDerivative (t : ℝ) (y : E) : E →L[ℝ] E :=
  (-r) • conditionalMeanSpatialDerivative F x r (projIcc 0 b hb t) y

include hF hlo hup hb1 in
theorem continuous_clippedConditionalVelocityDerivative :
    Continuous (uncurry (clippedConditionalVelocityDerivative (F := F) x (r := r) hb)) := by
  have hp : Continuous (fun q : ℝ × E => ((projIcc 0 b hb q.1 : ℝ), q.2)) :=
    (continuous_subtype_val.comp ((continuous_projIcc (h := hb)).comp
      continuous_fst)).prodMk continuous_snd
  exact (continuous_const : Continuous (fun _ : ℝ × E => (-r : ℝ))).smul
    ((continuousOn_conditionalMeanSpatialDerivative hF hlo hup x r
      (by norm_num : (-1 : ℝ) < 0) hb1).comp_continuous hp
      (fun q => ⟨(projIcc 0 b hb q.1).2, mem_univ q.2⟩))

include hF hlo hup hb1 in
theorem hasFDerivAt_clippedConditionalVelocity (t : ℝ) (y : E) :
    HasFDerivAt (clippedProbabilityVelocity hb r (conditionalMean F x r) t)
      (clippedConditionalVelocityDerivative (F := F) x (r := r) hb t y) y :=
  (hasFDerivAt_conditionalMeanSpatialDerivative hF hlo hup x r
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (projIcc 0 b hb t).2.1)
    ((projIcc 0 b hb t).2.2.trans_lt hb1) y).const_smul (-r)

theorem contDiff_one_forwardProbabilityTransport (ρ : ℝ) :
    ContDiff ℝ 1 (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ : E → E) := by
  exact flow_contDiff_one hb
    (clippedProbabilityVelocity_continuous hb r
      (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1))
    (fun t _ => clippedProbabilityVelocity_lipschitz hb r
      (fun u hu => lipschitzWith_conditionalMean hF hell hlo hup x hr
        (by linarith [hu.1]) (hu.2.trans_lt hb1)) t)
    (continuous_clippedConditionalVelocityDerivative hF hlo hup x hb hb1)
    (hasFDerivAt_clippedConditionalVelocity hF hlo hup x hb hb1)
    (projIcc 0 b hb ρ) ⟨b, hb, le_rfl⟩

theorem contDiff_one_backwardProbabilityTransport (ρ : ℝ) :
    ContDiff ℝ 1 (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ : E → E) := by
  exact flow_contDiff_one hb
    (clippedProbabilityVelocity_continuous hb r
      (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1))
    (fun t _ => clippedProbabilityVelocity_lipschitz hb r
      (fun u hu => lipschitzWith_conditionalMean hF hell hlo hup x hr
        (by linarith [hu.1]) (hu.2.trans_lt hb1)) t)
    (continuous_clippedConditionalVelocityDerivative hF hlo hup x hb hb1)
    (hasFDerivAt_clippedConditionalVelocity hF hlo hup x hb hb1)
    ⟨b, hb, le_rfl⟩ (projIcc 0 b hb ρ)

/-- The source small-scale condition gives a common `e` Lipschitz bound in
both time orientations. -/
theorem lipschitzWith_convexProbabilityFlow_exp_one (hsmall : r ^ 2 * ell ≤ 1 / 2)
    (s t : Icc 0 b) :
    LipschitzWith ⟨Real.exp 1, (Real.exp_pos _).le⟩
      (fun y => convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1 s y t) := by
  apply (flow_lipschitz
    (fun u _ => clippedProbabilityVelocity_lipschitz hb r
      (fun v hv => lipschitzWith_conditionalMean hF hell hlo hup x hr
        (by linarith [hv.1]) (hv.2.trans_lt hb1)) u)
    (clippedProbabilityVelocity_continuous hb r
      (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1)) s t).weaken
  change Real.exp _ ≤ Real.exp 1
  apply Real.exp_le_exp.mpr
  change (‖r‖ * (r * ell)) * |(t : ℝ) - (s : ℝ)| ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos hr]
  have hdist : |(t : ℝ) - (s : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [s.2.1, s.2.2, t.2.1, t.2.2]
  calc
    r * (r * ell) * |(t : ℝ) - (s : ℝ)| ≤ r * (r * ell) * 1 :=
      mul_le_mul_of_nonneg_left hdist (mul_nonneg hr.le (mul_nonneg hr.le hell))
    _ ≤ 1 := by nlinarith

/-- `Bρ = DTρ ∘ Yρ`, with the actual forward and backward transports. -/
def transportedJacobian (ρ : ℝ) (y : E) : E →L[ℝ] E :=
  fderiv ℝ (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ)
    (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y)

/-- The transported derivative satisfies the manuscript's dimension-free
operator bound, derived directly from the actual ODE stability estimate. -/
theorem norm_transportedJacobian_le (hsmall : r ^ 2 * ell ≤ 1 / 2)
    (ρ : ℝ) (y : E) :
    ‖transportedJacobian hF hell hlo hup x hr hb hb1 ρ y‖ ≤ Real.exp 1 := by
  exact norm_fderiv_le_of_lipschitz ℝ
    (lipschitzWith_convexProbabilityFlow_exp_one hF hell hlo hup x hr hb hb1 hsmall
      (projIcc 0 b hb ρ) ⟨b, hb, le_rfl⟩)

theorem continuous_transportedJacobian (ρ : ℝ) :
    Continuous (transportedJacobian hF hell hlo hup x hr hb hb1 ρ) :=
  ((contDiff_one_forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ).continuous_fderiv
    (by norm_num)).comp
    (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ).continuous

/-- At the terminal endpoint the transported derivative is the identity. -/
@[simp] theorem transportedJacobian_terminal (y : E) :
    transportedJacobian hF hell hlo hup x hr hb hb1 b y = ContinuousLinearMap.id ℝ E := by
  have he : (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 b : E → E) = id := by
    funext z
    change convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
      (projIcc 0 b hb b) z b = z
    have hp : projIcc 0 b hb b = ⟨b, hb, le_rfl⟩ := projIcc_of_mem hb ⟨hb, le_rfl⟩
    rw [hp]
    exact convexProbabilityFlow_initial hF hell hlo hup x hr hb (by norm_num) hb1 _ z
  simp only [transportedJacobian, he, fderiv_id]

/-- The source backward-Jacobian ODE, proved for the actual derivative of the
actual probability transport, including the zero endpoint. -/
theorem transportedJacobian_deriv {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) (y : E) :
    HasDerivWithinAt (fun t => transportedJacobian hF hell hlo hup x hr hb hb1 t y)
      ((r * ρ) • (transportedJacobian hF hell hlo hup x hr hb hb1 ρ y).comp
        (firstScaledJet F x r ρ
          (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y))) (Icc 0 b) ρ := by
  have hd := flowBackwardJacobian_deriv hb
    (clippedProbabilityVelocity_continuous hb r
      (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1))
    (fun t _ => clippedProbabilityVelocity_lipschitz hb r
      (fun u hu => lipschitzWith_conditionalMean hF hell hlo hup x hr
        (by linarith [hu.1]) (hu.2.trans_lt hb1)) t)
    (continuous_clippedConditionalVelocityDerivative hF hlo hup x hb hb1)
    (hasFDerivAt_clippedConditionalVelocity hF hlo hup x hb hb1) hρ y
  have hy : convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
        ⟨b, hb, le_rfl⟩ y ρ =
      backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y := by
    rw [backwardProbabilityTransport_eq_flow, projIcc_of_mem hb hρ]
  have hD (z : E) : clippedConditionalVelocityDerivative (F := F) x (r := r) hb ρ z =
      (-r * ρ) • firstScaledJet F x r ρ z := by
    rw [clippedConditionalVelocityDerivative, projIcc_of_mem hb hρ,
      ← (hasFDerivAt_conditionalMeanSpatialDerivative hF hlo hup x r
        (by linarith [hρ.1]) (hρ.2.trans_lt hb1) z).fderiv,
      fderiv_conditionalMean_eq_smul_firstScaledJet hF hlo hup x r
        (by linarith [hρ.1]) (hρ.2.trans_lt hb1), smul_smul]
  change HasDerivWithinAt (fun t => transportedJacobian hF hell hlo hup x hr hb hb1 t y)
    (-(transportedJacobian hF hell hlo hup x hr hb hb1 ρ y).comp
      (clippedConditionalVelocityDerivative (F := F) x (r := r) hb ρ
        (convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
          ⟨b, hb, le_rfl⟩ y ρ))) (Icc 0 b) ρ at hd
  rw [hy, hD, ContinuousLinearMap.comp_smul, ← neg_smul, neg_mul, neg_neg] at hd
  exact hd

/-- The derivative vanishes at probability time zero without a division by
probability time. -/
theorem transportedJacobian_deriv_zero (y : E) :
    HasDerivWithinAt (fun t => transportedJacobian hF hell hlo hup x hr hb hb1 t y)
      0 (Icc 0 b) 0 := by
  simpa only [mul_zero, zero_smul] using
    transportedJacobian_deriv hF hell hlo hup x hr hb hb1 ⟨le_rfl, hb⟩ y

theorem continuousOn_transportedJacobian (y : E) :
    ContinuousOn (fun t => transportedJacobian hF hell hlo hup x hr hb hb1 t y) (Icc 0 b) :=
  fun _ ht => (transportedJacobian_deriv hF hell hlo hup x hr hb hb1 ht y).continuousWithinAt

theorem continuous_transportedJacobian_joint :
    Continuous (fun p : E × Icc 0 b => transportedJacobian hF hell hlo hup x hr hb hb1 p.2 p.1) := by
  exact flowBackwardJacobian_joint_continuous hb
    (clippedProbabilityVelocity_continuous hb r
      (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1))
    (fun t _ => clippedProbabilityVelocity_lipschitz hb r
      (fun u hu => lipschitzWith_conditionalMean hF hell hlo hup x hr
        (by linarith [hu.1]) (hu.2.trans_lt hb1)) t)
    (continuous_clippedConditionalVelocityDerivative hF hlo hup x (r := r) hb hb1)
    (hasFDerivAt_clippedConditionalVelocity hF hlo hup x (r := r) hb hb1)

theorem continuous_backwardProbabilityTransport_joint :
    Continuous (fun p : E × Icc 0 b =>
      backwardProbabilityTransport hF hell hlo hup x hr hb hb1 p.2 p.1) := by
  have hc := flow_joint_continuous
    (fun t (_ : t ∈ Icc 0 b) => clippedProbabilityVelocity_lipschitz hb r
      (fun u hu => lipschitzWith_conditionalMean hF hell hlo hup x hr
        (by linarith [hu.1]) (hu.2.trans_lt hb1)) t)
    (clippedProbabilityVelocity_continuous hb r
      (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1)) ⟨b, hb, le_rfl⟩
  apply hc.congr
  intro p
  change _ = convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
    ⟨b, hb, le_rfl⟩ p.1 (projIcc 0 b hb p.2)
  rw [projIcc_of_mem hb p.2.2]
  rfl

end AcceleratedLogConcave.Conditional
