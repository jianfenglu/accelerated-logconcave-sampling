import AcceleratedLogConcave.Conditional.Definitions
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Differentiating the actual independent-Gaussian interpolation path. -/
noncomputable section
open scoped Topology

namespace AcceleratedLogConcave.Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual pathwise interpolation velocity, before conditioning on its output. -/
def interpolationPathVelocity (ρ : ℝ) (p : E × E) : E :=
  p.1 - (ρ / Real.sqrt (conditionalVariance ρ)) • p.2

/-- Differentiation uses only positive interpolation variance. -/
theorem hasDerivAt_interpolationMap {ρ : ℝ} (hv : 0 < conditionalVariance ρ)
    (p : E × E) :
    HasDerivAt (fun t => interpolationMap t p) (interpolationPathVelocity ρ p) ρ := by
  have hvar : HasDerivAt conditionalVariance (-2 * ρ) ρ := by
    change HasDerivAt ((fun _ : ℝ => 1) - id ^ 2) (-2 * ρ) ρ
    simpa using! (hasDerivAt_const ρ (1 : ℝ)).sub ((hasDerivAt_id ρ).pow 2)
  have hsqrt : HasDerivAt (fun t => Real.sqrt (conditionalVariance t))
      (-(ρ / Real.sqrt (conditionalVariance ρ))) ρ := by
    have hh := (Real.hasDerivAt_sqrt hv.ne').comp ρ hvar
    have heq : (1 / (2 * Real.sqrt (conditionalVariance ρ))) * (-2 * ρ) =
        -(ρ / Real.sqrt (conditionalVariance ρ)) := by
      field_simp
    rw [heq] at hh
    exact hh
  change HasDerivAt ((fun t : ℝ => t • p.1) +
    (fun t => Real.sqrt (conditionalVariance t) • p.2))
    (p.1 - (ρ / Real.sqrt (conditionalVariance ρ)) • p.2) ρ
  simpa only [one_smul, neg_smul, sub_eq_add_neg, id_eq] using ((hasDerivAt_id ρ).smul_const p.1).add (hsqrt.smul_const p.2)

/-- The pathwise velocity is the conditional-velocity numerator divided by
variance, including probability time zero. -/
theorem interpolationPathVelocity_eq {ρ : ℝ} (hv : 0 < conditionalVariance ρ)
    (p : E × E) :
    interpolationPathVelocity ρ p =
      (conditionalVariance ρ)⁻¹ • (p.1 - ρ • interpolationMap ρ p) := by
  have hs : Real.sqrt (conditionalVariance ρ) ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have hsq := Real.sq_sqrt hv.le
  have hc : (conditionalVariance ρ)⁻¹ * (ρ * Real.sqrt (conditionalVariance ρ)) =
      ρ / Real.sqrt (conditionalVariance ρ) := by
    field_simp
    nlinarith [congrArg (fun a : ℝ => ρ * a) hsq]
  symm
  calc
    _ = ((conditionalVariance ρ)⁻¹ * (1 - ρ ^ 2)) • p.1 -
        ((conditionalVariance ρ)⁻¹ * (ρ * Real.sqrt (conditionalVariance ρ))) • p.2 := by
      unfold interpolationMap
      module
    _ = _ := by
      rw [show 1 - ρ ^ 2 = conditionalVariance ρ from rfl,
        inv_mul_cancel₀ hv.ne', hc, one_smul]
      rfl

end AcceleratedLogConcave.Conditional
