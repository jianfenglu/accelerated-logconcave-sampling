import AcceleratedLogConcave.Root.OuterRootOriginalQuadrature

/-! Literal physical heat-score readout of the conditional root's first jet.
This fixes output units on the actual Gaussian-start common seed, including
both boundary clocks, before using the quadrature estimate. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace AcceleratedLogConcave.Root.OuterRootScoreReadout
open Numerics Numerics.ConditionalSmoothing OuterRootPhysicalPath
variable {ι : Type*} [Fintype ι]
variable {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
  {h : ℝ} (hh : 0 < h)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)

/-- The source first jet is exactly minus the physical score times sqrt(2h²).
The source input remains the same (xF,zeta); no marginal substitution occurs. -/
theorem jet_one_physical (xF zeta : EuclideanSpace ℝ ι) {u : ℝ}
    (hu : u ∈ Icc (0:ℝ) (1/2)) :
    (jet (OuterRootOriginalData.data hV hh hlo hup) 1 u (xF,zeta)).2 =
      (-Real.sqrt (2*h^2)) • gradient (Gibbs.heatPotential V (variance h u))
        (position hV hh hlo hup xF zeta u) := by
  let d := OuterRootOriginalData.data hV hh hlo hup
  have ht : u ∈ Icc (Analysis.PositiveVarianceSlab.left d.b)
      (Analysis.PositiveVarianceSlab.right d.b) :=
    (fixedData d xF).source_subset_construction hu
  rw [jet_one, openVelocity, time_eq d ht, jointPath_fst]
  dsimp only
  rw [jointPath_snd_eq_source d xF zeta hu]
  have hp : SamplingCenterLp.path d xF u zeta = rawY hV hh hlo hup xF zeta u := by
    simp only [SamplingCenterLp.path, SamplingFlowLp.sourcePath,
      SamplingFlowLp.sourceTime_eq d.hb hu, rawY, d]
  rw [hp]
  change (-Real.sqrt (2*h)) • Conditional.conditionalMean
    (OuterRootOriginalData.potential V h) xF (Real.sqrt (2*h)) u
    (rawY hV hh hlo hup xF zeta u) = _
  rw [conditional_score hV hh hlo hup xF _ hu, smul_smul, neg_mul, scale_sqrt hh]
  rfl

/-- Score units can be recovered without dividing by the clock. Only h>0 is
needed, so this includes the source clock zero. -/
theorem physical_score_eq_jet (xF zeta : EuclideanSpace ℝ ι) {u : ℝ}
    (hu : u ∈ Icc (0:ℝ) (1/2)) :
    gradient (Gibbs.heatPotential V (variance h u))
      (position hV hh hlo hup xF zeta u) =
      (-Real.sqrt (2*h^2))⁻¹ •
        (jet (OuterRootOriginalData.data hV hh hlo hup) 1 u (xF,zeta)).2 := by
  rw [jet_one_physical hV hh hlo hup xF zeta hu, smul_smul,
    inv_mul_cancel₀ (neg_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))), one_smul]

end AcceleratedLogConcave.Root.OuterRootScoreReadout
