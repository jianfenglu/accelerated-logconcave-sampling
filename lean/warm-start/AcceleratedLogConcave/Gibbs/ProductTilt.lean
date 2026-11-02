import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Actual product and coordinate-change identities for normalized Gibbs laws.
These identities do not assume a partition identity or an integration-by-parts
certificate. They also cover zero/undefined partition normalization by the
existing total definition of Measure.tilted. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Gibbs

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Normalized Gibbs tilting commutes with a measurable coordinate equivalence. -/
theorem map_tilted_equiv (e : X ≃ᵐ Y) (μ : Measure X) (f : X → ℝ) :
    (μ.tilted f).map e = (μ.map e).tilted (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    tilted_apply_eq_ofReal_integral' f (e.measurable hs),
    tilted_apply_eq_ofReal_integral' (fun y => f (e.symm y)) hs,
    setIntegral_map_equiv, integral_map_equiv]
  simp only [e.symm_apply_apply]

/-- The product of two normalized Gibbs laws is the actual normalized sum
potential on product space, with both partition integrals calculated by Fubini. -/
theorem prod_tilted (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (μ.tilted f).prod (ν.tilted g) =
      (μ.prod ν).tilted (fun z => f z.1 + g z.2) := by
  have hZf : 0 ≤ ∫ x, Real.exp (f x) ∂μ :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  unfold Measure.tilted
  rw [prod_withDensity (hf.exp.div_const _).ennreal_ofReal
    (hg.exp.div_const _).ennreal_ofReal]
  congr 1
  funext z
  simp_rw [Real.exp_add]
  rw [integral_prod_mul (μ := μ) (ν := ν) (fun x => Real.exp (f x)) (fun y => Real.exp (g y))]
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZf)]
  congr 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end AcceleratedLogConcave.Gibbs
