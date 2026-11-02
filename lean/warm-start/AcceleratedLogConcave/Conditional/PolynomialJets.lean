import AcceleratedLogConcave.Conditional.Tilt.GaussianTimePolynomial
import AcceleratedLogConcave.Conditional.Tilt.FirstJetNatural

/-! Specialization to the literal conditional mean and covariance
first scaled jet under the original C² potential assumptions. -/
noncomputable section
open Set Function
open scoped ContDiff
namespace AcceleratedLogConcave.Conditional
open Analysis.PositiveVarianceSlab Tilt.NaturalParameterJets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem firstScaledJet_eq_heatTimeCenterDerivative
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (x : E) (r : ℝ) {p : ℝ × E} (hp : p ∈ domain) :
    firstScaledJet F x r p.1 p.2 =
      Tilt.heatTimeCenterDerivative (primitivePotential F x r) (primitiveObservable F x r) p :=
  (fderiv_centerMean_eq_firstScaledJet hF hlo hhi x r hp.1 hp.2 p.2).symm

theorem contDiffOn_firstScaledJet_natural
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (x : E) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => firstScaledJet F x r p.1 p.2) domain := by
  have hh := Tilt.contDiffOn_heatTimeCenterDerivative
    (contDiff_primitivePotential hF x r) (primitivePotential_hessian_nonneg hF hlo x r)
    (continuous_primitiveObservable hF x r)
    (show 0 ≤ ‖gradient F 0‖ + |L| * ‖x‖ + |L| * |r| by positivity) 1
    (norm_primitiveObservable_le_polynomial hF hlo hhi x r)
  exact hh.congr fun p hp => firstScaledJet_eq_heatTimeCenterDerivative hF hlo hhi x r hp

theorem exists_polynomial_conditionalMean_jet_bound
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : E) (r : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p : ℝ × E, p.1 ∈ Icc (left b) (right b) →
      ‖iteratedFDerivWithin ℝ n (fun q : ℝ × E => conditionalMean F x r q.1 q.2)
        domain p‖ ≤ C * (1 + ‖p‖) ^ N := by
  have hh := Tilt.exists_polynomial_heatTimeMean_jet_bound
    (contDiff_primitivePotential hF x r) (primitivePotential_hessian_nonneg hF hlo x r)
    (primitivePotential_hessian_upper hF hhi x r) hb0 hb1
    (continuous_primitiveObservable hF x r)
    (show 0 ≤ ‖gradient F 0‖ + |L| * ‖x‖ + |L| * |r| by positivity) 1 n
    (norm_primitiveObservable_le_polynomial hF hlo hhi x r)
  exact hh

/-- The literal first scaled jet is controlled through order n by the
normalized natural mean through order n+1, including probability time zero. -/
theorem exists_polynomial_firstScaledJet_jet_bound
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L * ‖w‖ ^ 2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : E) (r : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p : ℝ × E, p.1 ∈ Icc (left b) (right b) →
      ‖iteratedFDerivWithin ℝ n (fun q : ℝ × E => firstScaledJet F x r q.1 q.2)
        domain p‖ ≤ C * (1 + ‖p‖) ^ N := by
  obtain ⟨C, hC, N, hb⟩ := Tilt.exists_polynomial_heatTimeCenterDerivative_jet_bound
    (contDiff_primitivePotential hF x r) (primitivePotential_hessian_nonneg hF hlo x r)
    (primitivePotential_hessian_upper hF hhi x r) hb0 hb1
    (continuous_primitiveObservable hF x r)
    (show 0 ≤ ‖gradient F 0‖ + |L| * ‖x‖ + |L| * |r| by positivity) 1 n
    (norm_primitiveObservable_le_polynomial hF hlo hhi x r)
  refine ⟨C, hC, N, ?_⟩
  intro p hp
  have heq : EqOn (fun q : ℝ × E => firstScaledJet F x r q.1 q.2)
      (Tilt.heatTimeCenterDerivative (primitivePotential F x r) (primitiveObservable F x r))
      domain := fun q hq => firstScaledJet_eq_heatTimeCenterDerivative hF hlo hhi x r hq
  rw [iteratedFDerivWithin_congr heq (construction_subset hb0 hb1 hp) n]
  exact hb p hp

end AcceleratedLogConcave.Conditional
