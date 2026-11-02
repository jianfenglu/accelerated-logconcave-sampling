import AcceleratedLogConcave.Conditional.Flow.Construction

/-! Exact restriction agreement for the constructed conditional-mean flows.
The two total time-clipped vector fields may differ outside the smaller slab.
The proof compares the actual solutions on that slab, for every spatial input. -/
noncomputable section
open Set Function MeasureTheory
open scoped Topology NNReal
namespace AcceleratedLogConcave.Conditional
open OAI.LogConcaveSampling.GlobalODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Changing to a larger construction slab preserves the actual trajectory on
the original closed slab, for every starting time and spatial point. -/
theorem meanProbabilityFlow_eq_on_subinterval
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hsub : Icc a b ⊆ Icc c d) (r : ℝ) (M : ℝ → E → E)
    (hc : ContinuousOn (uncurry M) (Icc a b ×ˢ (univ : Set E)))
    (hc' : ContinuousOn (uncurry M) (Icc c d ×ˢ (univ : Set E)))
    {L L' : ℝ≥0} (hL : ∀ t ∈ Icc a b, LipschitzWith L (M t))
    (hL' : ∀ t ∈ Icc c d, LipschitzWith L' (M t))
    (s t : Icc a b) (y : E) :
    meanProbabilityFlow hab r M hc hL s y t =
      meanProbabilityFlow hcd r M hc' hL' ⟨s, hsub s.2⟩ y t := by
  have hh := trajectory_dist (fun q hq => meanVelocity_lipschitz r (hL q hq))
    (meanProbabilityFlow_continuous hab r M hc hL s y).continuousOn
    (fun q hq => meanProbabilityFlow_deriv hab r M hc hL s y hq)
    (meanProbabilityFlow_continuous hcd r M hc' hL' ⟨s, hsub s.2⟩ y).continuousOn
    (fun q hq => (meanProbabilityFlow_deriv hcd r M hc' hL'
      ⟨s, hsub s.2⟩ y (hsub hq)).mono hsub) s t
  simpa only [meanProbabilityFlow_initial, dist_self, zero_mul, dist_le_zero] using hh

/-- All-input restriction agreement gives equality of the actual spatial
Fréchet derivatives. No derivative of a time projection is used. -/
theorem meanProbabilityFlow_fderiv_eq_on_subinterval
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hsub : Icc a b ⊆ Icc c d) (r : ℝ) (M : ℝ → E → E)
    (hc : ContinuousOn (uncurry M) (Icc a b ×ˢ (univ : Set E)))
    (hc' : ContinuousOn (uncurry M) (Icc c d ×ˢ (univ : Set E)))
    {L L' : ℝ≥0} (hL : ∀ t ∈ Icc a b, LipschitzWith L (M t))
    (hL' : ∀ t ∈ Icc c d, LipschitzWith L' (M t))
    (s t : Icc a b) :
    fderiv ℝ (fun y => meanProbabilityFlow hab r M hc hL s y t) =
      fderiv ℝ (fun y => meanProbabilityFlow hcd r M hc' hL' ⟨s, hsub s.2⟩ y t) := by
  exact congrArg (fderiv ℝ) (funext
    (meanProbabilityFlow_eq_on_subinterval hab hcd hsub r M hc hc' hL hL' s t))

end AcceleratedLogConcave.Conditional
