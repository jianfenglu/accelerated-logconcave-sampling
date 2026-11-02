import AcceleratedLogConcave.Analysis.CoupledVelocityPolynomial
import AcceleratedLogConcave.Conditional.PolynomialJets

/-! Polynomial state fields for the literal conditional-mean velocity and
division-free first scaled jet. The inverse-Jacobian composition order is
B.comp(U1). This does not introduce a separate coupled flow. -/
noncomputable section
open Set
open scoped ContDiff
namespace AcceleratedLogConcave.Conditional
open Analysis.CoupledVelocityPolynomial Analysis.ODEJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def conditionalCoupledVelocity (F : E → ℝ) (x : E) (r : ℝ) :
    CoupledSpaceTime E → CoupledState E :=
  velocity E r (fun p => conditionalMean F x r p.1 p.2)
    (fun p => firstScaledJet F x r p.1 p.2)

theorem contDiffOn_conditionalCoupledVelocity
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (x : E) (r : ℝ) :
    ContDiffOn ℝ ∞ (conditionalCoupledVelocity F x r) (openDomain (CoupledState E)) :=
  contDiffOn_velocity (contDiffOn_conditionalMean hF hlo hhi x r)
    (contDiffOn_firstScaledJet_natural hF hlo hhi x r)

/-- The triangular n+q≤K bound only requests velocity jets of order <K.
The actual posterior suppliers discharge those requests under original C²
potential assumptions; all state coordinates remain unrestricted. -/
theorem exists_polynomial_conditionalStateJet_bound
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : E) (r : ℝ) (K : ℕ) :
    ∀ n q, n + q ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p ∈ closedSlab (CoupledState E) b,
        ‖iteratedFDerivWithin ℝ q
          (stateJet (openDomain (CoupledState E)) (conditionalCoupledVelocity F x r) n)
          (openDomain (CoupledState E)) p‖ ≤ C * (1 + ‖p‖) ^ N := by
  apply exists_polynomial_stateJet_bound
    (isOpen_openDomain (CoupledState E)).uniqueDiffOn
    (closedSlab_subset_openDomain (CoupledState E) hb0 hb1)
    (contDiffOn_conditionalCoupledVelocity hF hlo hhi x r) K
  exact exists_polynomial_liftedVelocity_bound hb0 hb1
    (contDiffOn_conditionalMean hF hlo hhi x r)
    (contDiffOn_firstScaledJet_natural hF hlo hhi x r) K
    (fun i _ => exists_polynomial_conditionalMean_jet_bound hF hlo hhi hb0 hb1 x r i)
    (fun i _ => exists_polynomial_firstScaledJet_jet_bound hF hlo hhi hb0 hb1 x r i)

end AcceleratedLogConcave.Conditional
