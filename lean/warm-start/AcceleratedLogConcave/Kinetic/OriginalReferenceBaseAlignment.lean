import AcceleratedLogConcave.Kinetic.OriginalReferenceMixing
import AcceleratedLogConcave.Schedule.DyadicReturnedLaw

/-! The dyadic comparison and the genuine source phase use the same initial
heat marginal. This is a measure identity, with no executable error premise. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Kinetic.OriginalReferenceBaseAlignment
open AcceleratedLogConcave.Kinetic
open AcceleratedLogConcave.Kinetic.Reheating
open AcceleratedLogConcave.Schedule
open AcceleratedLogConcave.Gibbs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The phase base law in the dyadic error consumer is exactly the initial
law of the original-C² reverse-clock reference, including momentum. -/
theorem phaseReference_eq_original_clock_base {V : E → ℝ} {κ h R : ℝ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h)
    (hR : 2 * h ^ 2 < R)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2) :
    Dyadic.phaseReference V (Dyadic.sourceVariance h) =
      ((clockTransportFamily (originalHeatMixingFamily (R := R) hV hκ hh hR hlo hup)
        (by positivity) hR).law 0).prod (stdGaussian E) := by
  haveI : IsProbabilityMeasure (volume.tilted (fun x => -V x)) :=
    originalGibbs_probability_of_hessian_lower hV hκ hlo
  have hbase := clockTransportFamily_heated_law
    (originalHeatMixingFamily (R := R) hV hκ hh hR hlo hup)
    (show 0 < 2 * h ^ 2 by positivity) hR 0 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 (1/2))
  have hheat :
      heatedLaw (volume.tilted (fun x => -V x)) (2 * h ^ 2) =
        Channels.forward (volume.tilted (fun x => -V x)) (Dyadic.sourceVariance h) := by
    exact heatedLaw_eq_forward (volume.tilted (fun x => -V x))
      (Dyadic.sourceVariance h)
  unfold Dyadic.phaseReference Dyadic.cooledLaw Dyadic.targetLaw
  simp only [Dyadic.variance_zero]
  rw [← hheat]
  congr 1
  simpa using hbase.symm

/-- Exact source outer variance used by `OriginalReferencePhaseLaw`. -/
theorem phaseReference_eq_source_clock_base {V : E → ℝ} {κ h : ℝ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2) :
    Dyadic.phaseReference V (Dyadic.sourceVariance h) =
      ((clockTransportFamily
        (originalHeatMixingFamily (R := 2 * (2 * h ^ 2)) hV hκ hh
          (by nlinarith [sq_pos_of_pos hh]) hlo hup)
        (by positivity) (by nlinarith [sq_pos_of_pos hh])).law 0).prod
          (stdGaussian E) := by
  exact phaseReference_eq_original_clock_base hV hκ hh
    (by nlinarith [sq_pos_of_pos hh]) hlo hup

end AcceleratedLogConcave.Kinetic.OriginalReferenceBaseAlignment
