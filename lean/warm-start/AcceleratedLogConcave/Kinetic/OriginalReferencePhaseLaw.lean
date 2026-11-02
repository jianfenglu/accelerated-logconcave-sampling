import AcceleratedLogConcave.Kinetic.ReferencePhaseLaw
import AcceleratedLogConcave.Kinetic.OriginalReferenceWarmth
import AcceleratedLogConcave.Kinetic.SourcePhaseCount

/-! The genuine reference phase law started from an arbitrary joint warm
position-momentum measure, at the original C² source data. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
namespace AcceleratedLogConcave.Kinetic.OriginalReferencePhaseLaw
open AcceleratedLogConcave.Kinetic
open AcceleratedLogConcave.Kinetic.ReferencePhaseLaw
open AcceleratedLogConcave.Kinetic.OriginalReferenceMixing
open AcceleratedLogConcave.Root AcceleratedLogConcave.Gibbs
open AcceleratedLogConcave.Kinetic.Reheating
open AcceleratedLogConcave.Kinetic.ConditionalContraction
open AcceleratedLogConcave.Analysis.Poisson
open AcceleratedLogConcave.Numerics.AffineGraph
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

private theorem referenceR_gt {h : ℝ} (hh : 0 < h) :
    2*h^2 < 2*(2*h^2) := by nlinarith [sq_pos_of_pos hh]

/-- The law obtained by iterating the actual source root reference kernel has
the TV decay previously proved for the centered density operator. -/
theorem original_reference_warmTV {V : E → ℝ} {κ h : ℝ} {m : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
    {θ : ℝ} (hm1 : (κ + 2 * h ^ 2)⁻¹ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ Real.sqrt 2 / 32 / 32)
    (hh14 : h ≤ 1 / 4)
    (hhC : h ≤ (Real.sqrt 2 / 32) / (8 * ((1 : ℝ) / 2 + 200))) :
    letI : IsProbabilityMeasure (volume.tilted (fun x => -V x)) :=
      originalGibbs_probability_of_hessian_lower hV hκ hlo
    let H := originalHeatMixingFamily (R := 2 * (2 * h ^ 2)) hV hκ hh
      (referenceR_gt hh) hlo hup
    let P := clockTransportFamily H (by positivity) (referenceR_gt hh)
    let Q := referenceKernel hV hκ hh (by linarith) hlo hup G hm t ht K
    let Γ := Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h
    ∀ (ν : Measure (E × E)) [IsProbabilityMeasure ν] (B : ℝ)
      (hwarm : AcceleratedLogConcave.Probability.L2Warm
        ((P.law 0).prod (stdGaussian E)) ν B) (k : ℕ),
      have : IsProbabilityMeasure (warmIterateLaw H (by positivity)
        (referenceR_gt hh) (Real.sqrt 2 * h) Γ Q ν k) :=
          ReferenceChannelIteration.iterateLaw_probability
            (input_preserving H (by positivity) (referenceR_gt hh)
              (Real.sqrt 2*h) Q)
            (output_preserving H (by positivity) (referenceR_gt hh)
              (Real.sqrt 2*h) Γ
              (mul_nonneg (Real.sqrt_nonneg _) hh.le) Q
              (fun clock => referenceKernel_invariant hV hκ hh (by linarith)
                hlo hup G hm t ht K clock))
            hwarm.absolutelyContinuous k
      AcceleratedLogConcave.Probability.totalVariationDistance
        (warmIterateLaw H (show 0 < 2*h^2 by positivity) (referenceR_gt hh)
          (Real.sqrt 2 * h) Γ Q ν k)
        ((P.law 0).prod (stdGaussian E)) ≤
          Real.sqrt ((5/3:ℝ)*
            (sourceContractionFactor θ ((κ+2*h^2)⁻¹) h)^k)*
            Real.sqrt (B-1)/2 := by
  let : IsProbabilityMeasure (volume.tilted (fun x => -V x)) :=
    originalGibbs_probability_of_hessian_lower hV hκ hlo
  dsimp only
  intro ν hν B hwarm k
  let H := originalHeatMixingFamily (R := 2*(2*h^2)) hV hκ hh
    (referenceR_gt hh) hlo hup
  let Q := referenceKernel hV hκ hh (by linarith : h ≤ 1/2) hlo hup G hm t ht K
  let hQ := fun clock => referenceKernel_invariant hV hκ hh
    (by linarith : h ≤ 1/2) hlo hup G hm t ht K clock
  let Γ := Real.sqrt ((κ+2*h^2)⁻¹)*h
  let hΓ : 0 ≤ Γ := mul_nonneg (Real.sqrt_nonneg _) hh.le
  have htv := warmIterate_totalVariation_le H (by positivity) (referenceR_gt hh)
    (Real.sqrt 2*h) Γ hΓ Q hQ hwarm k
  have hpow := phaseDensity_power_centered H (by positivity) (referenceR_gt hh)
    (Real.sqrt 2*h) Γ hΓ Q hQ k hwarm.centeredDensity
  have hmix := OriginalReferenceWarmth.referenceHeatPhase_warmDensity
    hV hκ hh hlo hup G hm t ht K hm1 hθ0 hθ hh14 hhC ν B hwarm k
  have hnorm :
      ‖((phaseDensity H (by positivity) (referenceR_gt hh)
          (Real.sqrt 2*h) Γ hΓ Q hQ)^k)
        (hwarm.centeredDensity : Lp ℝ 2
          (((clockTransportFamily H (by positivity) (referenceR_gt hh)).law 0).prod
            (stdGaussian E)))‖ =
      ‖((sourceCenteredPhaseDensity H (by positivity) (referenceR_gt hh)
          (Real.sqrt 2*h) Γ hΓ (clockSection Q) hQ
          (fun f => sourceClockChannel_integrable H (by positivity)
            (referenceR_gt hh) (Real.sqrt 2*h) Γ hΓ Q hQ f))^k)
        hwarm.centeredDensity‖ := by
    rw [← hpow]
    rfl
  rw [hnorm] at htv
  exact htv.trans (div_le_div_of_nonneg_right hmix (by norm_num))

/-- A predetermined integer number of genuine reference transitions reaches
the requested TV tolerance. Its rate is the source square-root curvature
rate, and the initial law remains an arbitrary joint warm phase measure. -/
theorem original_reference_warmTV_horizon {V : E → ℝ} {κ h : ℝ} {m : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
    {θ : ℝ} (hκ1 : 1 ≤ κ) (hθpos : 0 < θ)
    (hm1 : (κ + 2 * h ^ 2)⁻¹ ≤ 1)
    (hθ : θ ≤ Real.sqrt 2 / 32 / 32)
    (hh14 : h ≤ 1 / 4)
    (hhC : h ≤ (Real.sqrt 2 / 32) / (8 * ((1 : ℝ) / 2 + 200))) :
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
          (referenceHorizon (sourceRate θ κ h) (warmMixingExponent B ε))) :=
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
          (referenceHorizon (sourceRate θ κ h) (warmMixingExponent B ε)))
        ((P.law 0).prod (stdGaussian E)) ≤ ε := by
  let : IsProbabilityMeasure (volume.tilted (fun x => -V x)) :=
    originalGibbs_probability_of_hessian_lower hV hκ hlo
  dsimp only
  intro ν hν B ε hwarm hB hε
  let a := sourceRate θ κ h
  let L := warmMixingExponent B ε
  let k := referenceHorizon a L
  have ha : 0 < a := sourceRate_pos hθpos hκ1 hh
  have hθ1 : θ ≤ 1 := by
    have hs : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
    linarith
  have ha1 : a ≤ 1 := sourceRate_le_one hθpos.le hθ1 hκ1 hh.le
    (by linarith : h ≤ 1)
  have htv := original_reference_warmTV hV hκ hh hlo hup G hm t ht K
    hm1 hθpos.le hθ hh14 hhC ν B hwarm k
  have hs := warm_horizon_bound ha ha1 hB hε
  rw [sourceContractionFactor_eq_rate] at htv
  exact htv.trans hs

end AcceleratedLogConcave.Kinetic.OriginalReferencePhaseLaw
