import AcceleratedLogConcave.Conditional.Stein.Transport
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Smooth probability-time curves, including the zero endpoint -/
noncomputable section
set_option maxHeartbeats 1600000
open Set Function
open scoped Topology NNReal ContDiff

namespace AcceleratedLogConcave.Conditional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)

theorem continuous_backwardProbabilityTransport (y : E) :
    Continuous (fun t => backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y) := by
  have hc : Continuous (convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
      ⟨b, hb, le_rfl⟩ y) := probabilityFlow_continuous _ _ _ _ _ _ _ _
  exact hc.comp (continuous_subtype_val.comp (continuous_projIcc (h := hb)))

theorem backwardProbabilityTransport_deriv {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) (y : E) :
    HasDerivWithinAt (fun t => backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)
      ((-r) • conditionalMean F x r ρ
        (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ y)) (Icc 0 b) ρ := by
  have hd := convexProbabilityFlow_deriv hF hell hlo hup x hr hb (by norm_num) hb1
    ⟨b, hb, le_rfl⟩ y hρ
  have heq (t : ℝ) (ht : t ∈ Icc 0 b) :
      backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y =
        convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1 ⟨b, hb, le_rfl⟩ y t := by
    rw [backwardProbabilityTransport_eq_flow, projIcc_of_mem hb ht]
  rw [← heq ρ hρ] at hd
  exact hd.congr_of_mem heq hρ

private theorem contDiffOn_succ_of_derivative {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f g : ℝ → V} {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (n : ℕ)
    (hg : ContDiffOn ℝ n g s)
    (hd : ∀ t ∈ s, HasDerivWithinAt f (g t) s t) : ContDiffOn ℝ (n + 1 : ℕ) f s := by
  rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
  apply (contDiffOn_succ_iff_derivWithin hs).mpr
  refine ⟨fun t ht => (hd t ht).differentiableWithinAt, by simp, ?_⟩
  exact hg.congr fun t ht => (hd t ht).derivWithin (hs t ht)

/-- Gaussian smoothing makes the actual backward trajectory smooth in
probability time, on the closed interval and at probability time zero. -/
theorem contDiffOn_backwardProbabilityTransport (hbpos : 0 < b) (y : E) :
    ContDiffOn ℝ ∞ (fun t => backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)
      (Icc 0 b) := by
  apply contDiffOn_infty.mpr
  intro n
  induction n with
  | zero =>
      exact contDiffOn_zero.mpr
        (continuous_backwardProbabilityTransport hF hell hlo hup x hr hb hb1 y).continuousOn
  | succ n ih =>
    apply contDiffOn_succ_of_derivative (uniqueDiffOn_Icc hbpos) n
      (g := fun t => (-r) • conditionalMean F x r t
        (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y))
    · have hm : ContDiffOn ℝ n (fun p : ℝ × E => conditionalMean F x r p.1 p.2)
          {p | -1 < p.1 ∧ p.1 < 1} :=
        (contDiffOn_conditionalMean hF hlo hup x r).of_le (by simp)
      have hp : ContDiffOn ℝ n (fun t =>
          (t, backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)) (Icc 0 b) :=
        contDiffOn_id.prodMk ih
      have hmY := hm.comp hp (fun t ht =>
        ⟨by change -1 < t; linarith [ht.1], ht.2.trans_lt hb1⟩)
      exact hmY.const_smul (-r)
    · exact fun _ ht => backwardProbabilityTransport_deriv hF hell hlo hup x hr hb hb1 ht y

/-- The actual backward Jacobian is smooth in time, so the logarithmic
representation can use its genuine second derivative at the zero endpoint. -/
theorem contDiffOn_transportedJacobian (hbpos : 0 < b) (y : E) :
    ContDiffOn ℝ ∞ (fun t => transportedJacobian hF hell hlo hup x hr hb hb1 t y)
      (Icc 0 b) := by
  have hY := contDiffOn_backwardProbabilityTransport hF hell hlo hup x hr hb hb1 hbpos y
  have hU : ContDiffOn ℝ ∞ (fun t => firstScaledJet F x r t
      (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)) (Icc 0 b) :=
    (contDiffOn_firstScaledJet hF hlo hup x r).comp
      (contDiffOn_id.prodMk hY) (fun t ht => ⟨by change -1 < t; linarith [ht.1], ht.2.trans_lt hb1⟩)
  apply contDiffOn_infty.mpr
  intro n
  induction n with
  | zero =>
      exact contDiffOn_zero.mpr
        (continuousOn_transportedJacobian hF hell hlo hup x hr hb hb1 y)
  | succ n ih =>
    apply contDiffOn_succ_of_derivative (uniqueDiffOn_Icc hbpos) n
      (g := fun t => (r * t) •
        (transportedJacobian hF hell hlo hup x hr hb hb1 t y).comp
          (firstScaledJet F x r t
            (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)))
    · exact (contDiffOn_const.mul contDiffOn_id).smul (ih.clm_comp (hU.of_le (by simp)))
    · exact fun _ ht => transportedJacobian_deriv hF hell hlo hup x hr hb hb1 ht y

end AcceleratedLogConcave.Conditional
