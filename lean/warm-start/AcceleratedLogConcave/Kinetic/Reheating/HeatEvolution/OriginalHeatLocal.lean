import AcceleratedLogConcave.Gibbs.LocalizedHeatCurvature
import AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonLocal

/-!
# Explicit remainder for the original heat-potential source family

This is a conditional constructor, not an existence theorem for the remainder.
All pointwise spatial C², curvature, integrability and probability fields are
derived from the original potential. The remaining joint regularity and
classical density/PDE obligations are named here, on the full analytic envelope.
No desired curvature estimate, flow, inverse, or W05 conclusion is record data.

The Gaussian-law identification is deliberately separate, in
`OriginalVarianceFamily`. Neither constructor closes the original-data supplier.
-/

noncomputable section
open MeasureTheory Set Function InnerProductSpace

namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson Gibbs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The fixed, normalized Gibbs density of the actual heat potential. -/
def originalHeatDensity (F : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  Real.exp (-heatPotential F t x) / ∫ y, Real.exp (-heatPotential F t y)

/-- Undischarged analytic obligations for the *actual* heat potential.
In particular, the interval is [3A/4,R], not just [3A/4,A]. -/
structure OriginalHeatEvolutionData (F : E → ℝ) (A R : ℝ) where
  gradient_continuous :
    ContinuousOn (uncurry (fun t => gradient (heatPotential F t)))
      (Icc (3 * A / 4) R ×ˢ (univ : Set E))
  hessian_continuous :
    ContinuousOn (uncurry (fun t => hessianOperator (heatPotential F t)))
      (Icc (3 * A / 4) R ×ˢ (univ : Set E))
  densityVelocity : ℝ → E → ℝ
  density_continuous :
    ContinuousOn (uncurry (originalHeatDensity F))
      (Icc (3 * A / 4) R ×ˢ (univ : Set E))
  densityVelocity_continuous :
    ContinuousOn (uncurry densityVelocity) (Ioo (3 * A / 4) R ×ˢ (univ : Set E))
  density_hasDerivAt : ∀ t ∈ Ioo (3 * A / 4) R, ∀ x,
    HasDerivAt (fun s => originalHeatDensity F s x) (densityVelocity t x) t
  continuity_equation : ∀ t ∈ Ioo (3 * A / 4) R, ∀ x,
    densityVelocity t x +
      fluxDivergence (fun y => originalHeatDensity F t y •
        referenceDrift (heatPotential F) (fun _ => -(1/2 : ℝ)) t y) x = 0

namespace OriginalHeatEvolutionData

/-- Construct all curvature and normalization fields from original C² data.
The explicitly named remainder is not proved to exist by this definition. -/
def toLocal {F : E → ℝ} {κ A R : ℝ}
    (D : OriginalHeatEvolutionData F A R)
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hA : 0 < A) (hR : A < R)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ ‖v‖ ^ 2) :
    LocalReferencePoissonFamily E (3 * A / 4) R where
  ordered := by linarith
  potential := heatPotential F
  scale := fun _ => -(1/2 : ℝ)
  potential_C2 := fun t ht => (heat_potential_envelope_data hF hκ hA hlo hup t ht).1
  gradient_continuous := D.gradient_continuous
  hessian_continuous := D.hessian_continuous
  scale_continuous := continuous_const.continuousOn
  lower := localizedHeatLower κ A
  lower_pos := fun t _ => localizedHeatLower_pos hκ hA.le
  hessian_lower := fun t ht => (heat_potential_envelope_data hF hκ hA hlo hup t ht).2.2.1
  hessian_upper := fun t ht => (heat_potential_envelope_data hF hκ hA hlo hup t ht).2.2.2.1
  law := fun t => volume.tilted (fun x => -heatPotential F t x)
  probability := fun t ht => isProbabilityMeasure_tilted
    (heat_potential_envelope_data hF hκ hA hlo hup t ht).2.2.2.2
  integrable := fun t ht => (heat_potential_envelope_data hF hκ hA hlo hup t ht).2.2.2.2
  gibbs_law := fun _ _ => rfl
  density := originalHeatDensity F
  densityVelocity := D.densityVelocity
  density_continuous := D.density_continuous
  densityVelocity_continuous := D.densityVelocity_continuous
  density_hasDerivAt := D.density_hasDerivAt
  density_C1 := fun t ht => by
    have hC := (heat_potential_envelope_data hF hκ hA hlo hup t
      (Ioo_subset_Icc_self ht)).1
    exact (hC.neg.exp.div_const _).of_le (by norm_num)
  continuity_equation := D.continuity_equation
  density_law := fun _ _ => rfl
  density_nonneg := fun _ _ x => div_nonneg (Real.exp_pos _).le
    (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem toLocal_lower_eq {F : E → ℝ} {κ A R : ℝ}
    (D : OriginalHeatEvolutionData F A R)
    (hF : ContDiff ℝ 2 F) (hκ : 0 < κ) (hA : 0 < A) (hR : A < R)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x v, fderiv ℝ (fderiv ℝ F) x v v ≤ ‖v‖ ^ 2)
    (t : ℝ) (ht : t ∈ Icc (3 * A / 4) A) :
    (D.toLocal hF hκ hA hR hlo hup).lower t = (κ + A)⁻¹ :=
  localizedHeatLower_eq_of_le ht.2

end OriginalHeatEvolutionData
end AcceleratedLogConcave.Kinetic.Reheating
