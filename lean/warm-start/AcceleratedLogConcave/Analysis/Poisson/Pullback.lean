import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Unitary composition on the moving reference spaces

This is the measure-theoretic adapter once a spatial flow has been proved to
transport the reference law. The vector version composes each component and
does not multiply by a spatial Jacobian. Flow existence and transport are
separate obligations, not conclusions of this adapter.
-/

noncomputable section
open MeasureTheory

namespace AcceleratedLogConcave.Analysis.Poisson

variable {X Y F : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure X} {ν : Measure Y}

/-- Composition along a measure-preserving measurable equivalence is unitary
on L2, for scalar functions and for vector fields with the same convention. -/
def pullback (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) :
    Lp F 2 ν ≃ₗᵢ[ℝ] Lp F 2 μ :=
  LinearIsometryEquiv.ofLinearIsometry (Lp.compMeasurePreservingₗᵢ ℝ e he)
    (Lp.compMeasurePreservingₗ ℝ e.symm (MeasurePreserving.symm e he))
    (by
      apply LinearMap.ext
      intro u
      change Lp.compMeasurePreserving e he
        (Lp.compMeasurePreserving e.symm (MeasurePreserving.symm e he) u) = u
      rw [← Lp.compMeasurePreserving_comp_apply]
      simp only [MeasurableEquiv.symm_comp_self, Lp.compMeasurePreserving_id_apply])
    (by
      apply LinearMap.ext
      intro u
      change Lp.compMeasurePreserving e.symm (MeasurePreserving.symm e he)
        (Lp.compMeasurePreserving e he u) = u
      rw [← Lp.compMeasurePreserving_comp_apply]
      simp only [MeasurableEquiv.self_comp_symm, Lp.compMeasurePreserving_id_apply])

theorem pullback_coeFn (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (f : Lp F 2 ν) : pullback e he f =ᵐ[μ] fun x => f (e x) :=
  Lp.coeFn_compMeasurePreserving f he

/-- Spatial pullback preserves the actual scalar integral, hence centering. -/
theorem integral_pullback (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (f : Lp ℝ 2 ν) :
    (∫ x, pullback e he f x ∂μ) = ∫ y, f y ∂ν := by
  rw [integral_congr_ae (pullback_coeFn e he f)]
  exact he.integral_comp' f

end AcceleratedLogConcave.Analysis.Poisson
