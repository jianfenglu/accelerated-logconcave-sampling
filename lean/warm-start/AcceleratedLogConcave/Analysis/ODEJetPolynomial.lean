import AcceleratedLogConcave.Analysis.ODEJet
import AcceleratedLogConcave.Analysis.PolynomialRecurrence
import Mathlib.Analysis.Normed.Operator.Prod

/-! finite polynomial closure for the actual-curve state-jet
recurrence. The only velocity bounds assumed have order strictly below K;
all-order smoothness is separately supplied by Gaussian regularization. -/
noncomputable section
open Set
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.ODEJet

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous linear map has a common degree-one envelope for every jet. -/
theorem norm_iteratedFDerivWithin_linear_le
    {U : Set P} (hU : UniqueDiffOn ℝ U) {p : P} (hp : p ∈ U)
    (L : P →L[ℝ] E) (q : ℕ) :
    ‖iteratedFDerivWithin ℝ q L U p‖ ≤ ‖L‖ * (1 + ‖p‖) := by
  cases q with
  | zero =>
    rw [norm_iteratedFDerivWithin_zero]
    exact (L.le_opNorm p).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left zero_le_one) (norm_nonneg L))
  | succ q =>
    have he : EqOn (fderivWithin ℝ L U) (fun _ => L) U :=
      fun x hx => L.fderivWithin (hU x hx)
    rw [← norm_iteratedFDerivWithin_fderivWithin hU hp,
      iteratedFDerivWithin_congr he hp q]
    cases q with
    | zero =>
      rw [norm_iteratedFDerivWithin_zero]
      exact le_mul_of_one_le_right (norm_nonneg L)
        (le_add_of_nonneg_right (norm_nonneg p))
    | succ q =>
      rw [iteratedFDerivWithin_succ_const, Pi.zero_apply, norm_zero]
      positivity

/-- Polynomial bounds in a triangular n+q≤K region. The bound is uniform on
S, while all derivatives use the same fixed unique-differentiation domain U.
In particular the top state field is only bounded, not differentiated again. -/
theorem exists_polynomial_stateJet_bound
    {U S : Set (ℝ × E)} (hU : UniqueDiffOn ℝ U) (hSU : S ⊆ U)
    {V : ℝ × E → E} (hV : ContDiffOn ℝ ∞ V U) (K : ℕ)
    (hvel : ∀ q < K, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p ∈ S,
      ‖iteratedFDerivWithin ℝ q (fun z => ((1 : ℝ), V z)) U p‖ ≤
        C * (1 + ‖p‖) ^ N) :
    ∀ n q, n + q ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p ∈ S,
      ‖iteratedFDerivWithin ℝ q (stateJet U V n) U p‖ ≤
        C * (1 + ‖p‖) ^ N := by
  apply PolynomialEnvelope.exists_polynomial_triangular_bound
    (R := fun p : ℝ × E => 1 + ‖p‖)
    (f := fun n q p => ‖iteratedFDerivWithin ℝ q (stateJet U V n) U p‖)
    (v := fun q p => ‖iteratedFDerivWithin ℝ q (fun z => ((1 : ℝ), V z)) U p‖)
    (fun p _ => le_add_of_nonneg_right (norm_nonneg p)) K
  · intro q _
    refine ⟨1, zero_le_one, 1, ?_⟩
    intro p hp
    have hh := norm_iteratedFDerivWithin_linear_le hU (hSU hp)
      (ContinuousLinearMap.snd ℝ ℝ E) q
    have hc : ‖ContinuousLinearMap.snd ℝ ℝ E‖ ≤ 1 :=
      ContinuousLinearMap.norm_snd_le ℝ ℝ E
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hc (by positivity))
    change ‖iteratedFDerivWithin ℝ q Prod.snd U p‖ ≤ 1 * (1 + ‖p‖) at hh'
    simpa only [stateJet, one_mul, pow_one] using hh'
  · exact hvel
  · intro q p hp
    exact norm_nonneg _
  · intro n q hq p hp
    exact norm_iteratedFDerivWithin_stateJet_succ_le hU hV n q (hSU hp)

end AcceleratedLogConcave.Analysis.ODEJet
