import AcceleratedLogConcave.Conditional.Stein.Transport

/-! Exact intermediate marginals of the fixed-interval Stein transport. -/
noncomputable section
open Set Function MeasureTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional
open Analysis.Poisson OAI.LogConcaveSampling.GlobalODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

theorem forwardProbabilityTransport_measurePreserving
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc 0 b) :
    MeasurePreserving (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ)
      (interpolationLaw F x r ρ) (interpolationLaw F x r b) := by
  rcases hρ.2.eq_or_lt with heq | hlt
  · subst ρ
    have hid : (forwardProbabilityTransport hF hell hlo hup x hr hb hb1 b : E → E) = id := by
      funext y
      change convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
        (projIcc 0 b hb b) y b = y
      rw [projIcc_of_mem hb ⟨hb, le_rfl⟩]
      exact convexProbabilityFlow_initial hF hell hlo hup x hr hb (by norm_num) hb1 _ y
    rw [hid]
    exact MeasurePreserving.id _
  · let hc := clippedProbabilityVelocity_continuous hb r
      (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1)
    let hL := fun t (_ : t ∈ Icc 0 b) => clippedProbabilityVelocity_lipschitz hb r
      (fun s hs => lipschitzWith_conditionalMean hF hell hlo hup x hr
        (by linarith [hs.1]) (hs.2.trans_lt hb1)) t
    have hsub : Icc ρ b ⊆ Icc 0 b := fun _ ht => ⟨hρ.1.trans ht.1, ht.2⟩
    let : ∀ t, IsFiniteMeasure (interpolationLaw F x r t) := fun t => by
      have := interpolationLaw_isProbabilityMeasure hF hlo x r t
      infer_instance
    have hCE := (hasWeakContinuityEquation_interpolation hF hlo hup x r
      (by linarith [hρ.1] : -1 < ρ) hb1).congr_velocity
      (fun t ht y => (clippedProbabilityVelocity_eq hb r (conditionalMean F x r)
        (hsub ⟨ht.1.le, ht.2.le⟩) y).symm)
    have hmp := measurePreserving_flow_of_weak_continuity hlt hc
      (fun t ht => hL t (hsub ht))
      (continuous_clippedConditionalVelocityDerivative hF hlo hup x (r := r) hb hb1)
      (hasFDerivAt_clippedConditionalVelocity hF hlo hup x (r := r) hb hb1)
      (interpolationLaw F x r) hCE
    have he : (flowHomeomorph (fun t ht => hL t (hsub ht)) hc
        ⟨ρ, le_rfl, hlt.le⟩ ⟨b, hlt.le, le_rfl⟩ : E → E) =
        forwardProbabilityTransport hF hell hlo hup x hr hb hb1 ρ := by
      funext y
      change flow (fun t ht => hL t (hsub ht)) hc ⟨ρ, le_rfl, hlt.le⟩ y b = _
      rw [flow_eq_on_subinterval hc hL hsub ⟨ρ, le_rfl, hlt.le⟩ ⟨b, hlt.le, le_rfl⟩ y]
      change flow hL hc ⟨ρ, hsub ⟨le_rfl, hlt.le⟩⟩ y b =
        flow hL hc (projIcc 0 b hb ρ) y b
      rw [projIcc_of_mem hb hρ]
    rwa [he] at hmp

end AcceleratedLogConcave.Conditional
