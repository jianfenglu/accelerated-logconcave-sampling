import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransportLaw

/-!
# Complete probability-time flows on closed subintervals

Time clipping makes the OAI global ODE construction applicable to a conditional
mean whose regularity is only known on a compact interval below one. No flow
or pushforward identity is a premise of this construction.
-/

noncomputable section
open Set Function MeasureTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional
open Analysis.Poisson OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The probability velocity determined by a conditional mean. -/
def meanVelocity (r : ℝ) (M : ℝ → E → E) (t : ℝ) (y : E) : E :=
  (-r) • M t y

/-- Extend only in time, preserving the original velocity on the interval. -/
def clippedProbabilityVelocity {a b : ℝ} (hab : a ≤ b) (r : ℝ)
    (M : ℝ → E → E) (t : ℝ) (y : E) : E :=
  meanVelocity r M (projIcc a b hab t) y

omit [FiniteDimensional ℝ E] in
theorem clippedProbabilityVelocity_eq {a b : ℝ} (hab : a ≤ b) (r : ℝ)
    (M : ℝ → E → E) {t : ℝ} (ht : t ∈ Icc a b) (y : E) :
    clippedProbabilityVelocity hab r M t y = meanVelocity r M t y := by
  simp only [clippedProbabilityVelocity, projIcc_of_mem hab ht]

omit [FiniteDimensional ℝ E] in
theorem clippedProbabilityVelocity_continuous {a b : ℝ} (hab : a ≤ b) (r : ℝ)
    {M : ℝ → E → E}
    (hM : ContinuousOn (uncurry M) (Icc a b ×ˢ (univ : Set E))) :
    Continuous (uncurry (clippedProbabilityVelocity hab r M)) := by
  have hc : Continuous (fun q : ℝ × E => ((projIcc a b hab q.1 : ℝ), q.2)) :=
    (continuous_subtype_val.comp ((continuous_projIcc (h := hab)).comp
      continuous_fst)).prodMk continuous_snd
  exact continuous_const.smul (hM.comp_continuous hc
    (fun q => ⟨(projIcc a b hab q.1).2, mem_univ q.2⟩))

omit [FiniteDimensional ℝ E] in
theorem meanVelocity_lipschitz (r : ℝ) {M : ℝ → E → E}
    {L : ℝ≥0} {t : ℝ} (hM : LipschitzWith L (M t)) :
    LipschitzWith (‖r‖₊ * L) (meanVelocity r M t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [meanVelocity, dist_eq_norm, ← smul_sub, norm_smul,
    norm_neg, NNReal.coe_mul, coe_nnnorm]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (by simpa only [dist_eq_norm] using hM.dist_le_mul x y) (norm_nonneg r)

omit [FiniteDimensional ℝ E] in
theorem clippedProbabilityVelocity_lipschitz {a b : ℝ} (hab : a ≤ b) (r : ℝ)
    {M : ℝ → E → E} {L : ℝ≥0}
    (hM : ∀ t ∈ Icc a b, LipschitzWith L (M t)) (t : ℝ) :
    LipschitzWith (‖r‖₊ * L) (clippedProbabilityVelocity hab r M t) :=
  meanVelocity_lipschitz r (hM _ (projIcc a b hab t).2)

section CompleteFlow
variable {a b : ℝ} (hab : a ≤ b) (r : ℝ) (M : ℝ → E → E)
  (hc : ContinuousOn (uncurry M) (Icc a b ×ˢ (univ : Set E)))
  {L : ℝ≥0} (hL : ∀ t ∈ Icc a b, LipschitzWith L (M t))

/-- The complete, uniquely determined probability-time ODE trajectory. -/
def meanProbabilityFlow (s : Icc a b) (y : E) : ℝ → E :=
  flow (fun t _ => clippedProbabilityVelocity_lipschitz hab r hL t)
    (clippedProbabilityVelocity_continuous hab r hc) s y

theorem meanProbabilityFlow_initial (s : Icc a b) (y : E) :
    meanProbabilityFlow hab r M hc hL s y s = y :=
  flow_initial _ _ _ _

theorem meanProbabilityFlow_continuous (s : Icc a b) (y : E) :
    Continuous (meanProbabilityFlow hab r M hc hL s y) :=
  flow_continuous _ _ _ _

/-- The constructed trajectory solves the original, unclipped equation at
every probability time in the construction interval. -/
theorem meanProbabilityFlow_deriv (s : Icc a b) (y : E) {t : ℝ}
    (ht : t ∈ Icc a b) :
    HasDerivWithinAt (meanProbabilityFlow hab r M hc hL s y)
      ((-r) • M t (meanProbabilityFlow hab r M hc hL s y t)) (Icc a b) t := by
  have h := flow_deriv (fun t _ => clippedProbabilityVelocity_lipschitz hab r hL t)
    (clippedProbabilityVelocity_continuous hab r hc) s y t ht
  simpa only [meanProbabilityFlow, clippedProbabilityVelocity_eq hab r M ht, meanVelocity] using h

/-- Completeness in both directions gives an invertible map. -/
def meanProbabilityFlowHomeomorph (s t : Icc a b) : E ≃ₜ E :=
  flowHomeomorph (fun u _ => clippedProbabilityVelocity_lipschitz hab r hL u)
    (clippedProbabilityVelocity_continuous hab r hc) s t

theorem meanProbabilityFlowHomeomorph_apply (s t : Icc a b) (y : E) :
    meanProbabilityFlowHomeomorph hab r M hc hL s t y =
      meanProbabilityFlow hab r M hc hL s y t := rfl

theorem meanProbabilityFlow_cocycle (s t u : Icc a b) (y : E) :
    meanProbabilityFlow hab r M hc hL t
      (meanProbabilityFlow hab r M hc hL s y t) u =
      meanProbabilityFlow hab r M hc hL s y u :=
  flow_cocycle _ _ _ _ _ _

end CompleteFlow
end AcceleratedLogConcave.Conditional
