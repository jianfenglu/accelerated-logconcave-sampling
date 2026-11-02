import AcceleratedLogConcave.Schedule.DyadicReturnedLaw
import AcceleratedLogConcave.Channels.TerminalHeatBias

/-!
# Physical returned-law assembly with the terminal heat bias discharged

`V` here is the physical original-target potential in the manuscript. In
particular, the `F` parameter of `DyadicReturnedLaw` is instantiated with `V`,
NOT with the oracle-coordinate potential `z ↦ V (sqrt(h) • z)`. The latter
belongs to the separate interpreter/rescaling linkage and cannot be silently
substituted for this physical target.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace AcceleratedLogConcave.Schedule.PhysicalReturnedLaw

open AcceleratedLogConcave.Probability
open AcceleratedLogConcave.Channels
open AcceleratedLogConcave.Schedule.PhaseCooling
open AcceleratedLogConcave.Schedule.Dyadic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The adapter's normalization input follows from original C² curvature. -/
theorem densityIntegrable {V : E → ℝ} {κ : ℝ}
    (hκ : 1 ≤ κ) (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v) :
    Integrable (fun x ↦ Real.exp (-V x)) :=
  Gibbs.integrable_exp_neg_of_hessian_lower hV (inv_pos.mpr (by linarith)) hlo

/-- The one-time terminal error for the physical Gibbs target. Unlike the old
adapter, this theorem consumes the proved heat theorem rather than an `hheat`
premise. The output covariance is exactly `a / 2^L`. -/
theorem cooledLaw_heatBias_le
    (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (κ : ℝ) (hκ : 1 ≤ κ) (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hhi : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ ‖v‖ ^ 2)
    (hμ : μ = volume.tilted (fun x ↦ -V x)) (a : ℝ≥0) (L : ℕ) :
    letI := cooledLaw_isProbabilityMeasure (densityIntegrable hκ hV hlo) a L
    totalVariationDistance (cooledLaw V a L) μ ≤
      (1 / 2 : ℝ) * Real.sqrt ((d : ℝ) * ((a / 2 ^ L : ℝ≥0) : ℝ)) := by
  have := cooledLaw_isProbabilityMeasure (densityIntegrable hκ hV hlo) a L
  have hb := totalVariationDistance_forward_gibbs_le μ V κ hκ hV hlo hhi hμ
    (a / 2 ^ L)
  simpa only [cooledLaw, targetLaw, Dyadic.variance, ← hμ,
    div_eq_mul_inv, mul_comm, one_mul] using hb

/-- Final physical-target error with terminal heat bias discharged. The
supplied exact mixing estimate stops at the cooled reference, so the bias is
not counted twice. Both local KL suppliers remain exact-to-implemented and
averaged under exact references. No executable-kernel identity is inferred. -/
theorem error_le_of_mixing_and_localKL
    (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (κ : ℝ) (hκ : 1 ≤ κ) (hV : ContDiff ℝ 2 V)
    (hlo : ∀ x v, κ⁻¹ * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x v) v)
    (hhi : ∀ x v, (fderiv ℝ (fderiv ℝ V) x v) v ≤ ‖v‖ ^ 2)
    (hμ : μ = volume.tilted (fun x ↦ -V x))
    {a : ℝ≥0} (ha : 0 < a)
    {ν : Measure (E × E)} [IsProbabilityMeasure ν] {B : ℝ}
    (hWarm : L2Warm (phaseReference V a) ν B)
    (phase implementedPhase : Kernel (E × E) (E × E))
    [IsMarkovKernel phase] [IsMarkovKernel implementedPhase]
    (implementedCool : ℕ → Kernel E E) [∀ j, IsMarkovKernel (implementedCool j)]
    (hphase : phase ∘ₘ phaseReference V a = phaseReference V a)
    {q Γ : ℝ} (hq : 0 ≤ q) (hΓ : 0 < Γ) (N L : ℕ)
    (hphaseKL : (∫⁻ z, klDiv (phase z) (implementedPhase z) ∂phaseReference V a) ≤
      ENNReal.ofReal (q / Γ))
    (hcoolKL : ∀ j < L,
      (∫⁻ x, klDiv
        (coolingKernel V hV.continuous.measurable (densityIntegrable hκ hV hlo) a j x)
        (implementedCool j x) ∂cooledLaw V a j) ≤ ENNReal.ofReal q)
    {mixing : ℝ}
    (hmixing : letI := cooledLaw_isProbabilityMeasure (densityIntegrable hκ hV hlo) a L
      totalVariationDistance
        (returnedLaw ν phase Prod.fst measurable_fst
          (coolingKernel V hV.continuous.measurable (densityIntegrable hκ hV hlo) a) N L)
        (cooledLaw V a L) ≤ mixing) :
    totalVariationDistance
      (returnedLaw ν implementedPhase Prod.fst measurable_fst implementedCool N L) μ ≤
      mixing + (1 / 2 : ℝ) * Real.sqrt ((d : ℝ) * ((a / 2 ^ L : ℝ≥0) : ℝ)) +
        Real.sqrt (B / 2 * q * ((N : ℝ) / Γ + (L : ℝ))) := by
  exact Dyadic.error_le_of_suppliers hV.continuous.measurable
    (densityIntegrable hκ hV hlo) ha hWarm μ phase implementedPhase
    implementedCool hphase hq hΓ N L hphaseKL hcoolKL hmixing
    (cooledLaw_heatBias_le μ V κ hκ hV hlo hhi hμ a L)

end AcceleratedLogConcave.Schedule.PhysicalReturnedLaw
