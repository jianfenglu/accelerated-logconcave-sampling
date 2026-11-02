import AcceleratedLogConcave.Analysis.Poisson.Projection
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Reflection associated with the gradient projection

The time-dependent gradient realization, differentiation of the Poisson
inverse, and the material-derivative identity remain downstream dependencies.
-/

noncomputable section

namespace AcceleratedLogConcave.Analysis.Poisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Reflection across the orthogonal complement, in the manuscript's
`I - 2 C` sign convention. Mathlib's reflection across `G` has the opposite
sign. -/
def gradientReflection (G : ClosedSubmodule ℝ E) : E ≃ₗᵢ[ℝ] E :=
  G.toSubmoduleᗮ.reflection

/-- The exact sign and normalization of the manuscript reflection. -/
theorem gradientReflection_apply (G : ClosedSubmodule ℝ E) (v : E) :
    gradientReflection G v = v - (2 : ℝ) • gradientProjection G v := by
  change G.toSubmoduleᗮ.reflection v = _
  rw [G.toSubmodule.reflection_orthogonal_apply, Submodule.reflection_apply]
  simp only [gradientProjection, neg_sub, two_smul]

/-- `I - 2 C` preserves distances, not just norms. -/
theorem isometry_gradientReflection (G : ClosedSubmodule ℝ E) :
    Isometry (gradientReflection G) :=
  (gradientReflection G).isometry

theorem norm_sub_two_gradientProjection (G : ClosedSubmodule ℝ E) (v : E) :
    ‖v - (2 : ℝ) • gradientProjection G v‖ = ‖v‖ := by
  rw [← gradientReflection_apply]
  exact (gradientReflection G).norm_map v

@[simp]
theorem gradientReflection_involutive (G : ClosedSubmodule ℝ E) (v : E) :
    gradientReflection G (gradientReflection G v) = v :=
  G.toSubmoduleᗮ.reflection_reflection v

/-- The unbundled expression in the manuscript is itself an isometry. -/
theorem isometry_sub_two_gradientProjection (G : ClosedSubmodule ℝ E) :
    Isometry (fun v : E => v - (2 : ℝ) • gradientProjection G v) := by
  have hf : (fun v : E => v - (2 : ℝ) • gradientProjection G v) =
      (gradientReflection G : E → E) := by
    funext v
    exact (gradientReflection_apply G v).symm
  rw [hf]
  exact isometry_gradientReflection G

/-- Continuous-linear-operator form of the reflection contraction bound. -/
theorem sub_two_gradientProjection_norm_le (G : ClosedSubmodule ℝ E) :
    ‖ContinuousLinearMap.id ℝ E - (2 : ℝ) • gradientProjection G‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖v - (2 : ℝ) • gradientProjection G v‖ ≤ 1 * ‖v‖
  simp only [norm_sub_two_gradientProjection, one_mul, le_refl]

/-- Reflection introduces no extra constant in a downstream current bound. -/
theorem norm_gradientReflection_apply_le (G : ClosedSubmodule ℝ E)
    {v : E} {b : ℝ} (hv : ‖v‖ ≤ b) :
    ‖gradientReflection G v‖ ≤ b := by
  simpa only [(gradientReflection G).norm_map] using hv

/-- The reflection norm identity for an operator supplied through the weak
Poisson equation; its analytic construction is still an explicit hypothesis. -/
theorem norm_sub_two_operator_of_weak
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : V →ₗ[ℝ] E) (C : E →L[ℝ] E)
    (hmem : ∀ v, C v ∈ closedGradientRange D)
    (hweak : ∀ v φ, inner ℝ (v - C v) (D φ) = 0) (v : E) :
    ‖v - (2 : ℝ) • C v‖ = ‖v‖ := by
  rw [operator_eq_gradientProjection D C hmem hweak]
  exact norm_sub_two_gradientProjection _ v

end AcceleratedLogConcave.Analysis.Poisson
