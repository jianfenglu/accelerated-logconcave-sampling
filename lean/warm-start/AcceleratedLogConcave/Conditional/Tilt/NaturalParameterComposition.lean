import AcceleratedLogConcave.Conditional.Tilt.NaturalParameterJets
import AcceleratedLogConcave.Analysis.PolynomialComposition

/-! natural-parameter composition supplier. The natural outer
jets are controlled on a fixed positive precision interval and all tilts.
Only derivatives through n enter the composition bound. -/
noncomputable section
open Set Function
open scoped ContDiff
namespace AcceleratedLogConcave.Conditional.Tilt.NaturalParameterJets
open Analysis.PositiveVarianceSlab Analysis.PolynomialEnvelope

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_polynomial_parameter_comp_bound
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {Q : ℝ × E → G} (hQ : ContDiffOn ℝ ∞ Q gaussianDomain) (n : ℕ)
    (houter : ∀ i ≤ n, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ a ∈ Icc ((2 : ℝ)⁻¹) ((2 * varianceFloor b)⁻¹), ∀ z : E,
      ‖iteratedFDerivWithin ℝ i Q gaussianDomain (a, z)‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p : ℝ × E, p.1 ∈ Icc (left b) (right b) →
      ‖iteratedFDerivWithin ℝ n (Q ∘ parameters) domain p‖ ≤ C * (1 + ‖p‖) ^ N := by
  let S : Set (ℝ × E) := Prod.fst ⁻¹' Icc (left b) (right b)
  have hSU : S ⊆ domain := fun p hp => construction_subset hb0 hb1 hp
  have hR : ∀ p ∈ S, 1 ≤ 1 + ‖p‖ :=
    fun p _ => le_add_of_nonneg_right (norm_nonneg p)
  obtain ⟨B, hB, htilt⟩ := exists_linear_tilt_weight_bound (E := E) hb0 hb1
  apply exists_polynomial_comp_jet_bound isOpen_domain.uniqueDiffOn
    isOpen_gaussianDomain.uniqueDiffOn hSU contDiffOn_parameters hQ
    (fun p hp => parameters_mem_gaussianDomain hp) hR n
  · intro i hi
    obtain ⟨C, hC, N, hb⟩ := houter i hi
    refine ⟨C * B ^ N, mul_nonneg hC (pow_nonneg (zero_le_one.trans hB) _), N, ?_⟩
    intro p hp
    have ha : (parameters p).1 ∈ Icc ((2 : ℝ)⁻¹) ((2 * varianceFloor b)⁻¹) :=
      precision_mem hb0 hb1 hp
    have hh := hb (parameters p).1 ha (parameters p).2
    calc
      _ ≤ C * (1 + ‖(parameters p).2‖) ^ N := hh
      _ ≤ C * (B * (1 + ‖p‖)) ^ N := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (htilt p hp) N) hC
      _ = (C * B ^ N) * (1 + ‖p‖) ^ N := by rw [mul_pow, mul_assoc]
  · intro i _
    obtain ⟨C, hC, hb⟩ := exists_linear_parameter_jet_bound (E := E) hb0 hb1 i
    exact ⟨C, hC, 1, fun p hp => by simpa only [pow_one] using hb p hp⟩

end AcceleratedLogConcave.Conditional.Tilt.NaturalParameterJets
