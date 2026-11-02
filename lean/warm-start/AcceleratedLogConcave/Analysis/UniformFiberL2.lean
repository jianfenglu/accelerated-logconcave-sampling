import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! A uniform conditional energy bound yields joint L² without any parameter
moment hypothesis. Fiber integrability is supplied separately, never inferred
from a finite-valued Bochner integral. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Analysis.UniformFiberL2
variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E]

theorem memLp_prod_of_uniform_energy (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [SFinite ν] (f : X × Y → E)
    (hm : AEStronglyMeasurable f (μ.prod ν))
    (hf : ∀ x, MemLp (fun y => f (x,y)) 2 ν)
    (C : ℝ) (hC : ∀ x, (∫ y, ‖f (x,y)‖^2 ∂ν) ≤ C) :
    MemLp f 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hsq := hm.norm.pow 2
  apply (integrable_prod_iff hsq).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x =>
      (memLp_two_iff_integrable_sq_norm (hf x).aestronglyMeasurable).mp (hf x))
  · apply (MemLp.of_bound (p := 1) hsq.norm.integral_prod_right' C ?_).integrable le_rfl
    filter_upwards [] with x
    simp only [Pi.pow_apply,norm_pow,norm_norm]
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact hC x

theorem integral_prod_norm_sq_le (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [SFinite ν] (f : X × Y → E)
    (hm : AEStronglyMeasurable f (μ.prod ν))
    (hf : ∀ x, MemLp (fun y => f (x,y)) 2 ν)
    (C : ℝ) (hC : ∀ x, (∫ y, ‖f (x,y)‖^2 ∂ν) ≤ C) :
    (∫ z, ‖f z‖^2 ∂μ.prod ν) ≤ C := by
  have hi := (memLp_two_iff_integrable_sq_norm hm).mp
    (memLp_prod_of_uniform_energy μ ν f hm hf C hC)
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _x, C ∂μ := by
      apply integral_mono hi.integral_prod_left (integrable_const _)
      exact hC
    _ = C := by simp
end AcceleratedLogConcave.Analysis.UniformFiberL2
