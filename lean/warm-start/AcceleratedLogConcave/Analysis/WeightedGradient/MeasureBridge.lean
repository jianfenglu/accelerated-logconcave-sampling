import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Identifying a normalized Gibbs density with Mathlib's exponential tilt

These identities avoid introducing another Gibbs measure definition. They apply
both to a normalized density and to a scalar multiple of the unnormalized law.
The potential need not be integrable before Gaussian regularization.
-/

open MeasureTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Gibbs

variable {E : Type*} [MeasurableSpace E]

/-- The usual normalized density is exactly Mathlib's exponential tilt. -/
theorem normalizedDensity_eq_tilted (ν : Measure E) (V : E → ℝ)
    (Z : ℝ) (hZ : Z = ∫ x, Real.exp (-V x) ∂ν) :
    ν.withDensity (fun x => ENNReal.ofReal (Z⁻¹ * Real.exp (-V x))) =
      ν.tilted (fun x => -V x) := by
  subst Z
  unfold Measure.tilted
  congr 1
  funext x
  rw [div_eq_mul_inv, mul_comm]

/-- Scalar normalization of the unnormalized density gives the same law. -/
theorem smul_withDensity_eq_tilted (ν : Measure E) (V : E → ℝ)
    (Z : ℝ) (hZ : Z = ∫ x, Real.exp (-V x) ∂ν) (hZpos : 0 < Z) :
    (ENNReal.ofReal Z)⁻¹ • ν.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))) =
      ν.tilted (fun x => -V x) := by
  rw [← ENNReal.ofReal_inv_of_pos hZpos]
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  convert normalizedDensity_eq_tilted ν V Z hZ using 1
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (ENNReal.ofReal_mul (inv_nonneg.mpr hZpos.le)).symm

/-- A supplied probability law can be identified without unfolding its definition. -/
theorem eq_tilted_of_normalizedDensity (ν μ : Measure E) (V : E → ℝ)
    (Z : ℝ) (hZ : Z = ∫ x, Real.exp (-V x) ∂ν)
    (hμ : μ = ν.withDensity (fun x => ENNReal.ofReal (Z⁻¹ * Real.exp (-V x)))) :
    μ = ν.tilted (fun x => -V x) :=
  hμ.trans (normalizedDensity_eq_tilted ν V Z hZ)

/-- The ENNReal partition function equals the real integral for an integrable density. -/
theorem lintegral_expNeg_eq_ofReal_integral (ν : Measure E) (V : E → ℝ)
    (hI : Integrable (fun x => Real.exp (-V x)) ν) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-V x)) ∂ν) =
      ENNReal.ofReal (∫ x, Real.exp (-V x) ∂ν) := by
  exact (ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-V x)).le)).symm

/-- Identification for an ENNReal partition function and normalized ENNReal density. -/
theorem ennreal_normalizedDensity_eq_tilted (ν : Measure E) [NeZero ν]
    (V : E → ℝ) (hI : Integrable (fun x => Real.exp (-V x)) ν)
    (Z : ℝ≥0∞) (hZ : Z = ∫⁻ x, ENNReal.ofReal (Real.exp (-V x)) ∂ν) :
    ν.withDensity (fun x => Z⁻¹ * ENNReal.ofReal (Real.exp (-V x))) =
      ν.tilted (fun x => -V x) := by
  rw [hZ, lintegral_expNeg_eq_ofReal_integral ν V hI]
  have hp : 0 < ∫ x, Real.exp (-V x) ∂ν := integral_exp_pos hI
  rw [← ENNReal.ofReal_inv_of_pos hp]
  convert normalizedDensity_eq_tilted ν V (∫ x, Real.exp (-V x) ∂ν) rfl using 1
  congr 1
  funext x
  exact (ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)).symm

/-- Scalar ENNReal normalization also matches exponential tilting. -/
theorem ennreal_smul_withDensity_eq_tilted (ν : Measure E) [NeZero ν]
    (V : E → ℝ) (hI : Integrable (fun x => Real.exp (-V x)) ν)
    (Z : ℝ≥0∞) (hZ : Z = ∫⁻ x, ENNReal.ofReal (Real.exp (-V x)) ∂ν) :
    Z⁻¹ • ν.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))) =
      ν.tilted (fun x => -V x) := by
  rw [hZ, lintegral_expNeg_eq_ofReal_integral ν V hI]
  exact smul_withDensity_eq_tilted ν V _ rfl (integral_exp_pos hI)

end AcceleratedLogConcave.Gibbs
