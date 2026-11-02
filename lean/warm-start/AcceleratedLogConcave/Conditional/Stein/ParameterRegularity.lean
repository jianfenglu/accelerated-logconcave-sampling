import AcceleratedLogConcave.Conditional.SourceParameterDomain
import AcceleratedLogConcave.Conditional.SourcePosteriorParameters
import AcceleratedLogConcave.Conditional.Stein.ParameterODE
import AcceleratedLogConcave.Conditional.SteinKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Joint parameter regularity of the actual transported Stein integral

The parameter domain retains its relative small-radius boundary. The backward
flow is controlled by the source velocity bound. The actual transported
derivative is then controlled separately by its terminal matrix equation,
with positive sign and right composition.
-/

noncomputable section
set_option maxHeartbeats 1600000
open Set Function MeasureTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional
open OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)

include hF hlo hup hb1 in
/-- The actual conditional mean varies jointly in center, radius, probability
time and state. Positive width is present only to share the source domain. -/
theorem continuous_conditionalMean_sourceParameters :
    Continuous (fun p : SourceParameters E ell × Icc 0 b × E =>
      conditionalMean F p.1.center p.1.radius p.2.1 p.2.2) := by
  apply (contDiffOn_conditionalMean_parameters hF hlo hup).continuousOn.comp_continuous
    ((SourceParameters.continuous_center.comp continuous_fst).prodMk
      ((SourceParameters.continuous_radius.comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_snd.fst).prodMk continuous_snd.snd)))
  intro p
  change 0 < p.1.radius ∧ -1 < (p.2.1 : ℝ) ∧ (p.2.1 : ℝ) < 1
  exact ⟨p.1.radius_pos, by linarith [p.2.1.2.1], p.2.1.2.2.trans_lt hb1⟩

include hF hlo hup hb1 in
theorem continuous_firstScaledJet_sourceParameters :
    Continuous (fun p : SourceParameters E ell × Icc 0 b × E =>
      firstScaledJet F p.1.center p.1.radius p.2.1 p.2.2) := by
  apply (contDiffOn_firstScaledJet_parameters hF hlo hup).continuousOn.comp_continuous
    ((SourceParameters.continuous_center.comp continuous_fst).prodMk
      ((SourceParameters.continuous_radius.comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_snd.fst).prodMk continuous_snd.snd)))
  intro p
  change 0 < p.1.radius ∧ -1 < (p.2.1 : ℝ) ∧ (p.2.1 : ℝ) < 1
  exact ⟨p.1.radius_pos, by linarith [p.2.1.2.1], p.2.1.2.2.trans_lt hb1⟩

/-- The literal backward probability transport is jointly continuous in all
source parameters, its terminal state and probability time. -/
theorem continuous_backwardProbabilityTransport_parameters :
    Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b =>
      backwardProbabilityTransport hF hell hlo hup p.1.1.center p.1.1.radius_pos
        hb hb1 p.2 p.1.2) := by
  let f (p : SourceParameters E ell × E) (t : ℝ) (z : E) :=
    probabilityVelocity F p.1.center p.1.radius t z
  let γ (p : SourceParameters E ell × E) (t : ℝ) :=
    backwardProbabilityTransport hF hell hlo hup p.1.center p.1.radius_pos hb hb1 t p.2
  have hL (p : SourceParameters E ell × E) (t : ℝ) (ht : t ∈ Icc 0 b) :
      LipschitzWith (1 / 2 : ℝ≥0) (f p t) := by
    apply (lipschitzWith_probabilityVelocity hF hell hlo hup p.1.center p.1.radius_pos
      (by linarith [ht.1]) (ht.2.trans_lt hb1)).weaken
    exact p.1.small
  have hγ (p : SourceParameters E ell × E) : ContinuousOn (γ p) (Icc 0 b) :=
    (continuous_backwardProbabilityTransport hF hell hlo hup p.1.center p.1.radius_pos
      hb hb1 p.2).continuousOn
  have hdγ (p : SourceParameters E ell × E) (t : ℝ) (ht : t ∈ Icc 0 b) :
      HasDerivWithinAt (γ p) (f p t (γ p t)) (Icc 0 b) t := by
    have hh := convexProbabilityFlow_deriv hF hell hlo hup p.1.center p.1.radius_pos
      hb (by norm_num) hb1 ⟨b, hb, le_rfl⟩ p.2 ht
    have heq (u : ℝ) (hu : u ∈ Icc 0 b) : γ p u =
        convexProbabilityFlow hF hell hlo hup p.1.center p.1.radius_pos
          hb (by norm_num) hb1 ⟨b, hb, le_rfl⟩ p.2 u := by
      dsimp only [γ]
      rw [backwardProbabilityTransport_eq_flow, projIcc_of_mem hb hu]
    rw [← heq t ht] at hh
    exact hh.congr_of_mem heq ht
  have hf : Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b × E =>
      f p.1 p.2.1 p.2.2) := by
    change Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b × E =>
      (-p.1.1.radius) • conditionalMean F p.1.1.center p.1.1.radius p.2.1 p.2.2)
    have hr : Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b × E =>
        -p.1.1.radius) := (SourceParameters.continuous_radius.comp continuous_fst.fst).neg
    have hM : Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b × E =>
        conditionalMean F p.1.1.center p.1.1.radius p.2.1 p.2.2) := by
      have hmap : Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b × E =>
          (p.1.1, p.2)) := continuous_fst.fst.prodMk continuous_snd
      simpa only [Function.comp_def] using
        (continuous_conditionalMean_sourceParameters hF hlo hup hb1).comp hmap
    exact hr.smul hM
  apply continuous_parameter_terminal_trajectory_joint hb hL hγ hdγ hf
  have heq : (fun p : SourceParameters E ell × E => γ p b) = Prod.snd := by
    funext p
    change backwardProbabilityTransport hF hell hlo hup p.1.center p.1.radius_pos hb hb1 b p.2 = p.2
    rw [backwardProbabilityTransport_eq_flow, projIcc_of_mem hb ⟨hb, le_rfl⟩]
    exact convexProbabilityFlow_initial hF hell hlo hup p.1.center p.1.radius_pos hb
      (by norm_num) hb1 _ p.2
  rw [heq]
  exact continuous_snd

/-- Joint continuity of the actual `B`, derived from its genuine terminal
equation `B' = r*rho*(B.comp U1)` and terminal value `I`. -/
theorem continuous_transportedJacobian_parameters :
    Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b =>
      transportedJacobian hF hell hlo hup p.1.1.center p.1.1.radius_pos hb hb1 p.2 p.1.2) := by
  let U (p : SourceParameters E ell × E) (t : ℝ) :=
    firstScaledJet F p.1.center p.1.radius t
      (backwardProbabilityTransport hF hell hlo hup p.1.center p.1.radius_pos hb hb1 t p.2)
  let f (p : SourceParameters E ell × E) (t : ℝ) (B : E →L[ℝ] E) :=
    (p.1.radius * t) • B.comp (U p t)
  let γ (p : SourceParameters E ell × E) (t : ℝ) :=
    transportedJacobian hF hell hlo hup p.1.center p.1.radius_pos hb hb1 t p.2
  have hU : Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b => U p.1 p.2) := by
    have hmap : Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b =>
        (p.1.1, p.2,
          backwardProbabilityTransport hF hell hlo hup p.1.1.center p.1.1.radius_pos hb hb1 p.2 p.1.2)) :=
      continuous_fst.fst.prodMk (continuous_snd.prodMk
        (continuous_backwardProbabilityTransport_parameters hF hell hlo hup hb hb1))
    simpa only [Function.comp_def, U] using
      (continuous_firstScaledJet_sourceParameters hF hlo hup hb1).comp hmap
  have hL (p : SourceParameters E ell × E) (t : ℝ) (ht : t ∈ Icc 0 b) :
      LipschitzWith (1 / 2 : ℝ≥0) (f p t) := by
    apply LipschitzWith.of_dist_le_mul
    intro B C
    have hnorm : ‖U p t‖ ≤ p.1.radius * ell :=
      norm_firstScaledJet_le hF hell hlo hup p.1.center p.1.radius_pos
        (by linarith [ht.1]) (ht.2.trans_lt hb1) _
    have hrt : 0 ≤ p.1.radius * t := mul_nonneg p.1.radius_pos.le ht.1
    have hc : (p.1.radius * t) * (p.1.radius * ell) ≤ 1 / 2 := by
      calc
        _ = (p.1.radius ^ 2 * ell) * t := by ring
        _ ≤ (1 / 2) * t := mul_le_mul_of_nonneg_right p.1.small ht.1
        _ ≤ 1 / 2 := by linarith [ht.2.trans_lt hb1]
    simp only [f, dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    rw [← smul_sub, ← ContinuousLinearMap.sub_comp, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hrt]
    calc
      _ ≤ (p.1.radius * t) * (‖B - C‖ * ‖U p t‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hrt
      _ ≤ (p.1.radius * t) * (‖B - C‖ * (p.1.radius * ell)) := by gcongr
      _ = ((p.1.radius * t) * (p.1.radius * ell)) * ‖B - C‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  change Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b => γ p.1 p.2)
  apply continuous_parameter_terminal_trajectory_joint hb (f := f) hL
    (fun p => continuousOn_transportedJacobian hF hell hlo hup p.1.center p.1.radius_pos hb hb1 p.2)
    (fun p t ht => transportedJacobian_deriv hF hell hlo hup p.1.center p.1.radius_pos hb hb1 ht p.2)
  · change Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b × (E →L[ℝ] E) =>
      (p.1.1.radius * (p.2.1 : ℝ)) • p.2.2.comp (U p.1 p.2.1))
    have hU' : Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b × (E →L[ℝ] E) =>
        U p.1 p.2.1) := by
      simpa only [Function.comp_def] using hU.comp
        (continuous_fst.prodMk continuous_snd.fst : Continuous
          (fun p : (SourceParameters E ell × E) × Icc 0 b × (E →L[ℝ] E) => (p.1, p.2.1)))
    exact ((SourceParameters.continuous_radius.comp continuous_fst.fst).mul
      (continuous_subtype_val.comp continuous_snd.fst)).smul
      (continuous_snd.snd.clm_comp hU')
  · simpa only [γ, transportedJacobian_terminal] using
      (continuous_const : Continuous (fun _ : SourceParameters E ell × E => ContinuousLinearMap.id ℝ E))

/-- The nonsingular literal Stein integrand is jointly continuous, including
probability time zero and the equality boundary of the radius constraint. -/
theorem continuous_transportedSteinIntegrand_parameters :
    Continuous (fun p : (SourceParameters E ell × E) × Icc 0 b =>
      transportedSteinIntegrand hF hell hlo hup p.1.1.center p.1.1.radius_pos hb hb1 p.2 p.1.2) :=
  (continuous_transportedJacobian_parameters hF hell hlo hup hb hb1).clm_comp
    ((continuous_firstScaledJet_sourceParameters hF hlo hup hb1).comp
      (continuous_fst.fst.prodMk (continuous_snd.prodMk
        (continuous_backwardProbabilityTransport_parameters hF hell hlo hup hb hb1))))

/-- Joint continuity of the actual compact Stein integral follows from its
nonsingular source integrand. Its common envelope uses only the original
small-radius condition and remains valid when `ell = 0`. -/
theorem continuous_transportedSteinKernelTranspose_parameters :
    Continuous (fun p : SourceParameters E ell × E =>
      transportedSteinKernelTranspose hF hell hlo hup p.1.center p.1.radius_pos hb hb1 p.2) := by
  apply intervalIntegral.continuous_of_dominated_interval
    (bound := fun _ => Real.exp 1 * (ell + 1))
  · intro p
    rw [uIoc_of_le hb]
    exact (intervalIntegrable_transportedSteinIntegrand hF hell hlo hup p.1.center
      p.1.radius_pos hb hb1 p.2).aestronglyMeasurable
  · intro p
    filter_upwards [] with t ht
    have ht0 : t ∈ Ioc 0 b := by simpa only [uIoc_of_le hb] using ht
    have ht' : t ∈ Icc 0 b := ⟨ht0.1.le, ht0.2⟩
    have hrL : p.1.radius * ell ≤ ell + 1 := by
      have hs := p.1.small
      have hsq := mul_nonneg (sq_nonneg (p.1.radius - 1)) hell
      nlinarith
    have hn := norm_firstScaledJet_le hF hell hlo hup p.1.center p.1.radius_pos
      (by linarith [ht'.1]) (ht'.2.trans_lt hb1)
      (backwardProbabilityTransport hF hell hlo hup p.1.center p.1.radius_pos hb hb1 t p.2)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_transportedJacobian_le hF hell hlo hup p.1.center p.1.radius_pos
        hb hb1 p.1.small t p.2) (hn.trans hrL) (norm_nonneg _) (Real.exp_pos _).le)
  · exact intervalIntegrable_const
  · filter_upwards [] with t ht
    have ht0 : t ∈ Ioc 0 b := by simpa only [uIoc_of_le hb] using ht
    have ht' : t ∈ Icc 0 b := ⟨ht0.1.le, ht0.2⟩
    exact (continuous_transportedSteinIntegrand_parameters hF hell hlo hup hb hb1).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : SourceParameters E ell × E =>
        (⟨t, ht'⟩ : Icc 0 b))))

end AcceleratedLogConcave.Conditional
