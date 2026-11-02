import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod

/-! Lift an actual family of weighted observation laws through an independently
retained parameter. This is Tonelli on the literal random tape, not an assumed
conditional-density or tensor-product operator rule. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace AcceleratedLogConcave.Kinetic.Reheating

/-- Actual weighted-map identities hold fiberwise in a retained parameter. -/
theorem weighted_observation_retained_parameter
    {X Y P Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace P] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (κ : Measure P) (η : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite κ] [SFinite η]
    (q : X×Z → Y) (hq : Measurable q)
    (f : X×P → ℝ≥0∞) (g : Y×P → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hw : ∀ p, ((μ.prod η).withDensity (fun z => f (z.1,p))).map q =
      ν.withDensity (fun y => g (y,p))) :
    (((μ.prod κ).prod η).withDensity (fun z => f z.1)).map
      (fun z => (q (z.1.1,z.2),z.1.2)) = (ν.prod κ).withDensity g := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ (by fun_prop), lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hg hφ]
  simp only [Pi.mul_apply]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod_symm _ (by fun_prop),
    lintegral_prod_symm _ (by fun_prop)]
  apply lintegral_congr
  intro p
  have hh := congrArg (fun M : Measure Y => ∫⁻ y, φ (y,p) ∂M) (hw p)
  rw [lintegral_map (by fun_prop) hq,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    lintegral_prod _ (by fun_prop)] at hh
  exact hh

end AcceleratedLogConcave.Kinetic.Reheating
