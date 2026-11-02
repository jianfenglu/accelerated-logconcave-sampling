import DirectW12.OriginalFamilyAdapter
import AcceleratedLogConcave.Gibbs.Normalization
import AcceleratedLogConcave.Gibbs.IntegrationByParts
import AcceleratedLogConcave.Analysis.WeightedGradient.MeasureBridge

/-! Stationary moment consequences of the actual reference-family fields. No tail moment or score budget is assumed. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace AcceleratedLogConcave.Root.OriginalRootStationaryMoments
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Positive curvature of the actual family supplies every polynomial moment. -/
theorem family_position_moment {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ n) (F.law t) := by
  rw [F.gibbs_law t ht]
  rw [← Gibbs.ennreal_smul_withDensity_eq_tilted volume (F.potential t)
    (F.integrable t ht) (∫⁻ x, ENNReal.ofReal (Real.exp (-F.potential t x))) rfl]
  exact Gibbs.integrable_norm_pow_normalized_of_hessian_lower
    (F.potential_C2 t) (F.lower_pos t ht) (F.hessian_lower t ht) n

/-- The stationary score has its genuine dimension-only second-moment bound.
The position moment used by integration by parts is derived above, not input. -/
theorem family_score_calculus {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    Integrable (gradient (F.potential t)) (F.law t) ∧
    Integrable (fun x => ‖gradient (F.potential t) x‖ ^ 2) (F.law t) ∧
    (∫ x, gradient (F.potential t) x ∂F.law t) = 0 ∧
    (∫ x, ‖gradient (F.potential t) x‖ ^ 2 ∂F.law t) ≤ Module.finrank ℝ E := by
  have hup : ∀ x v, fderiv ℝ (fderiv ℝ (F.potential t)) x v v ≤
      (1:ℝ) * ‖v‖ ^ 2 := by
    intro x v
    simpa only [one_mul] using F.hessian_upper t ht x v
  have hc := Gibbs.score_calculus_of_eq_tilted (ν := volume) (F.law t)
    (F.gibbs_law t ht) (F.potential_C2 t) (F.integrable t ht)
    (F.hessian_lower t ht) hup (family_position_moment F ht 2)
  exact ⟨hc.1, hc.2.1, hc.2.2.1, by simpa only [mul_one] using hc.2.2.2.2⟩

end AcceleratedLogConcave.Root.OriginalRootStationaryMoments
