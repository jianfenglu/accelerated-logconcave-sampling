import AcceleratedLogConcave.Kinetic.OriginalReferenceMixing
import AcceleratedLogConcave.Probability.WarmCenteredDensity

/-! The actual reference phase density acting on an arbitrary supplied joint
warm law. No independence of position and momentum is assumed. Identifying
this evolved density with an executed output measure remains separate. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Kinetic.OriginalReferenceWarmth
open AcceleratedLogConcave.Root AcceleratedLogConcave.Gibbs
open AcceleratedLogConcave.Kinetic AcceleratedLogConcave.Kinetic.Reheating
open AcceleratedLogConcave.Kinetic.ConditionalContraction
open AcceleratedLogConcave.Analysis.Poisson
open AcceleratedLogConcave.Numerics.AffineGraph
open OriginalReferenceMixing
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
private theorem referenceR_gt {h : ℝ} (hh : 0 < h) :
    2*h^2 < 2*(2*h^2) := by nlinarith [sq_pos_of_pos hh]

theorem referenceHeatPhase_warmDensity {V : E → ℝ} {κ h : ℝ} {m : ℕ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hh : 0 < h)
    (hlo : ∀ z v, κ⁻¹ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖ ^ 2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
    {θ : ℝ} (hm1 : (κ + 2 * h ^ 2)⁻¹ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ Real.sqrt 2 / 32 / 32)
    (hh14 : h ≤ 1 / 4)
    (hhC : h ≤ (Real.sqrt 2 / 32) / (8 * ((1 : ℝ) / 2 + 200))) :
    have : IsProbabilityMeasure (volume.tilted (fun x => -V x)) :=
      originalGibbs_probability_of_hessian_lower hV hκ hlo
    let H := originalHeatMixingFamily (R := 2 * (2 * h ^ 2)) hV hκ hh
      (referenceR_gt hh) hlo hup
    let P := clockTransportFamily H (by positivity) (referenceR_gt hh)
    let Q := referenceKernel hV hκ hh (by linarith) hlo hup G hm t ht K
    let hQ := fun clock => referenceKernel_invariant hV hκ hh (by linarith)
      hlo hup G hm t ht K clock
    let T := sourceCenteredPhaseDensity H (by positivity) (referenceR_gt hh)
      (Real.sqrt 2 * h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h)
      (mul_nonneg (Real.sqrt_nonneg _) hh.le) (clockSection Q) hQ
      (fun f => sourceClockChannel_integrable H (by positivity) (referenceR_gt hh)
        (Real.sqrt 2 * h) (Real.sqrt ((κ + 2 * h ^ 2)⁻¹) * h)
        (mul_nonneg (Real.sqrt_nonneg _) hh.le) Q hQ f)
    ∀ (ν : Measure (E × E)) [IsProbabilityMeasure ν] (B : ℝ)
      (hwarm : AcceleratedLogConcave.Probability.L2Warm
        ((P.law 0).prod (stdGaussian E)) ν B) (k : ℕ),
      ‖((T : centered ((P.law 0).prod (stdGaussian E)) →L[ℝ]
        centered ((P.law 0).prod (stdGaussian E))) ^ k) hwarm.centeredDensity‖ ≤
        Real.sqrt ((5/3:ℝ)*(sourceContractionFactor θ ((κ+2*h^2)⁻¹) h)^k)*
          Real.sqrt (B-1) := by
  have : IsProbabilityMeasure (volume.tilted (fun x => -V x)) :=
    originalGibbs_probability_of_hessian_lower hV hκ hlo
  have hmix := referenceHeatPhase_mixing hV hκ hh hlo hup G hm t ht K hm1 hθ0 hθ hh14 hhC
  dsimp only
  intro ν hν B hwarm k
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (hmix k).1 hwarm.norm_centeredDensity_le
      (norm_nonneg _) (Real.sqrt_nonneg _))

end AcceleratedLogConcave.Kinetic.OriginalReferenceWarmth
