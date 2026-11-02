import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.Real.Sqrt

/-!
Generic arbitrary-measure domination helpers.

No finite-measure, probability-measure, or individual-output moment assumption
is used. In applications f and g can themselves be differences; their separate
summands need not belong to L2. No external publication was performed.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Oracle.AnchorRmsHelpers

variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {μ : Measure Ω} {f : Ω → E} {g : Ω → F} {C : ℝ}

/-- General Lp domination. No sign hypothesis on C is needed for this API. -/
theorem memLp_of_norm_le_mul_ae {p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hg : MemLp g p μ)
    (hfg : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C * ‖g ω‖) : MemLp f p μ :=
  hg.of_le_mul hf hfg

/-- Extended-real seminorm estimate, valid before any finiteness assumption. -/
theorem eLpNorm_le_of_norm_le_mul_ae (p : ℝ≥0∞)
    (hf : AEStronglyMeasurable f μ)
    (hfg : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C * ‖g ω‖) :
    eLpNorm f p μ ≤ ENNReal.ofReal C * eLpNorm g p μ :=
  eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf hfg p

/-- Pointwise version yielding both second-moment membership and its norm bound. -/
theorem memLp_two_and_eLpNorm_le_of_norm_le_mul
    (hf : AEStronglyMeasurable f μ) (hg : MemLp g 2 μ)
    (hfg : ∀ ω, ‖f ω‖ ≤ C * ‖g ω‖) :
    MemLp f 2 μ ∧ eLpNorm f 2 μ ≤ ENNReal.ofReal C * eLpNorm g 2 μ :=
  ⟨hg.of_le_mul hf (Filter.Eventually.of_forall hfg),
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf (Filter.Eventually.of_forall hfg) 2⟩

/-- Squared Bochner-integral estimate on any measure, not only probabilities. -/
theorem integral_norm_sq_le_of_norm_le_mul_ae
    (hf : AEStronglyMeasurable f μ) (hg : MemLp g 2 μ)
    (hfg : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C * ‖g ω‖) :
    (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ C ^ 2 * ∫ ω, ‖g ω‖ ^ 2 ∂μ := by
  have hf2 : MemLp f 2 μ := hg.of_le_mul hf hfg
  have hfi : Integrable (fun ω => ‖f ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf).mp hf2
  have hgi : Integrable (fun ω => ‖g ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  calc
    (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ ∫ ω, C ^ 2 * ‖g ω‖ ^ 2 ∂μ := by
      apply integral_mono_ae hfi (hgi.const_mul (C ^ 2))
      filter_upwards [hfg] with ω hω
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (f ω)) hω 2
    _ = C ^ 2 * ∫ ω, ‖g ω‖ ^ 2 ∂μ := integral_const_mul _ _

/-- Real RMS domination; unlike the previous estimates, C must be nonnegative. -/
theorem rms_le_of_norm_le_mul_ae
    (hf : AEStronglyMeasurable f μ) (hg : MemLp g 2 μ)
    (hC : 0 ≤ C) (hfg : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C * ‖g ω‖) :
    Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤
      C * Real.sqrt (∫ ω, ‖g ω‖ ^ 2 ∂μ) := by
  calc
    Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤
        Real.sqrt (C ^ 2 * ∫ ω, ‖g ω‖ ^ 2 ∂μ) :=
      Real.sqrt_le_sqrt (integral_norm_sq_le_of_norm_le_mul_ae hf hg hfg)
    _ = C * Real.sqrt (∫ ω, ‖g ω‖ ^ 2 ∂μ) := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]

/-- Pointwise-input version of the real RMS estimate. -/
theorem rms_le_of_norm_le_mul
    (hf : AEStronglyMeasurable f μ) (hg : MemLp g 2 μ)
    (hC : 0 ≤ C) (hfg : ∀ ω, ‖f ω‖ ≤ C * ‖g ω‖) :
    Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤
      C * Real.sqrt (∫ ω, ‖g ω‖ ^ 2 ∂μ) :=
  rms_le_of_norm_le_mul_ae hf hg hC (Filter.Eventually.of_forall hfg)

end AcceleratedLogConcave.Oracle.AnchorRmsHelpers
