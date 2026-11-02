import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Change of variables for stationary densities. The determinant identity is
an explicit analytic premise, to be supplied by the centering flow. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
namespace AcceleratedLogConcave.Conditional.Centering
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A differentiable measurable equivalence preserving the weighted Jacobian
preserves the measure with that density. -/
theorem measurePreserving_of_density_det (μ : Measure E) [IsAddHaarMeasure μ]
    (T : E ≃ᵐ E) (D : E → E →L[ℝ] E) (p : E → ℝ)
    (hp : Integrable p μ) (hp0 : ∀ x, 0 ≤ p x)
    (hD : ∀ x, HasFDerivAt T (D x) x)
    (hdet : ∀ x, |(D x).det| * p (T x) = p x) :
    MeasurePreserving T (μ.withDensity (fun x => ENNReal.ofReal (p x)))
      (μ.withDensity (fun x => ENNReal.ofReal (p x))) := by
  have hs : MeasurePreserving T.symm (μ.withDensity (fun x => ENNReal.ofReal (p x)))
      (μ.withDensity (fun x => ENNReal.ofReal (p x))) := by
    refine ⟨T.symm.measurable, ?_⟩
    ext s hs
    rw [T.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul μ hs (f' := D)]
    · simp_rw [hdet]
      rw [withDensity_apply _ hs]
      exact ofReal_integral_eq_lintegral_ofReal hp.integrableOn
        (Filter.Eventually.of_forall fun x => hp0 x)
    · exact Filter.Eventually.of_forall fun x _ => hp0 x
    · exact hp.integrableOn
    · intro x _
      exact (hD x).hasFDerivWithinAt
  exact hs.symm
end AcceleratedLogConcave.Conditional.Centering
