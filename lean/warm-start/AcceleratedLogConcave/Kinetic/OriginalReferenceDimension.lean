import AcceleratedLogConcave.Kinetic.OriginalReferencePhaseLaw
import AcceleratedLogConcave.Kinetic.SourceDimensionMixing

/-! The original C² reference TV guarantee with all geometric mixing
smallness conditions discharged by an explicit dimension threshold. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
namespace AcceleratedLogConcave.Kinetic.OriginalReferenceDimension
open AcceleratedLogConcave.Kinetic ReferencePhaseLaw OriginalReferenceMixing
open AcceleratedLogConcave.Root AcceleratedLogConcave.Gibbs Reheating
open AcceleratedLogConcave.Numerics.AffineGraph
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
private theorem referenceR_gt {h : ℝ} (hh : 0 < h) :
    2*h^2 < 2*(2*h^2) := by nlinarith [sq_pos_of_pos hh]

theorem original_reference_dimensionTV {V : E → ℝ} {κ e : ℝ} {m D : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ1 : 1 ≤ κ) (he : 0 < e)
    (hD : sourceMixingDimension e ≤ D)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ) :
    let h := (D:ℝ)^(-e)
    have hκ : 0 < κ := lt_of_lt_of_le (by norm_num) hκ1
    have hh : 0 < h := (source_dimension_step he hD).1
    have hh14 : h ≤ 1/4 := (source_dimension_mixing_parameters he hκ1 hD).2.2.2.1
    letI : IsProbabilityMeasure (volume.tilted (fun x => -V x)) :=
      originalGibbs_probability_of_hessian_lower hV hκ hlo
    let H := originalHeatMixingFamily (R := 2 * (2 * h ^ 2)) hV hκ hh
      (referenceR_gt hh) hlo hup
    let P := clockTransportFamily H (by positivity) (referenceR_gt hh)
    let Q := referenceKernel hV hκ hh (by linarith) hlo hup G hm t ht K
    let Γ := Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h
    ∀ (ν : Measure (E × E)) [IsProbabilityMeasure ν] (B ε : ℝ)
      (hwarm : AcceleratedLogConcave.Probability.L2Warm
        ((P.law 0).prod (stdGaussian E)) ν B)
      (_hB : 1 ≤ B) (_hε : 0 < ε),
      have : IsProbabilityMeasure (warmIterateLaw H (by positivity)
        (referenceR_gt hh) (Real.sqrt 2 * h) Γ Q ν
          (referenceHorizon (sourceRate sourceDamping κ h) (warmMixingExponent B ε))) :=
          ReferenceChannelIteration.iterateLaw_probability
            (input_preserving H (by positivity) (referenceR_gt hh)
              (Real.sqrt 2*h) Q)
            (output_preserving H (by positivity) (referenceR_gt hh)
              (Real.sqrt 2*h) Γ
              (mul_nonneg (Real.sqrt_nonneg _) hh.le) Q
              (fun clock => referenceKernel_invariant hV hκ hh (by linarith)
                hlo hup G hm t ht K clock))
            hwarm.absolutelyContinuous _
      AcceleratedLogConcave.Probability.totalVariationDistance
        (warmIterateLaw H (show 0 < 2*h^2 by positivity) (referenceR_gt hh)
          (Real.sqrt 2 * h) Γ Q ν
          (referenceHorizon (sourceRate sourceDamping κ h) (warmMixingExponent B ε)))
        ((P.law 0).prod (stdGaussian E)) ≤ ε := by
  have hp := source_dimension_mixing_parameters he hκ1 hD
  exact OriginalReferencePhaseLaw.original_reference_warmTV_horizon hV
    (lt_of_lt_of_le (by norm_num) hκ1) hp.2.2.1 hlo hup G hm t ht K hκ1
    hp.1 hp.2.2.2.2.2 hp.2.1 hp.2.2.2.1 hp.2.2.2.2.1

end AcceleratedLogConcave.Kinetic.OriginalReferenceDimension
