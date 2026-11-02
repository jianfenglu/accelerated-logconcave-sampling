import AcceleratedLogConcave.Root.ClockQuadratureRows
import AcceleratedLogConcave.Root.OuterRootScoreReadout
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! FTC and the actual prescribed row on the Gaussian-start source path.
This is the reference quadrature defect, not a bound for noisy executed child
replies. No child accuracy or numerical regularity certificate is an input. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace AcceleratedLogConcave.Root.OuterRootOutputQuadrature
open OuterRootStrongJetLp OuterRootFlowIdentification
open Numerics Numerics.ConditionalSmoothing Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι]

/-- L2 FTC on the actual common-seed path; source endpoints lie inside its
smooth construction interval, so neither boundary requires legacy smoothness. -/
theorem integral_jet_one {a b : ℝ}
    (F : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) a b)
    (d : SamplingCenterLp.Data ι) (c : ℝ) {s t : ℝ}
    (hs : s ∈ Icc 0 d.b) (ht : t ∈ Icc 0 d.b) :
    (∫ u in s..t, jetLp F d c 1 u) = jetLp F d c 0 t - jetLp F d c 0 s := by
  have hsub : uIcc s t ⊆ Ioo (left d.b) (right d.b) := by
    intro u hu
    exact source_subset d.hb d.hb1
      (uIcc_subset_Icc hs ht hu)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    simpa only [Nat.zero_add] using jetLp_deriv F d c 0 (hsub hu)
  · exact ((jetLp_contDiffOn F d c 1 0).continuousOn.mono hsub).intervalIntegrable

variable {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
  {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
  (hlo : ∀ z v, m * ‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)

/-- The L2 endpoint is the literal conditional Gaussian-start readout on the
same common seed, rather than a different reverse-heat initial law. -/
theorem source_endpoint_ae (clock : ClockLaw.Clock) :
    let F := family hV hm hh hlo hup
    let d := OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup
    (jetLp F d (Real.sqrt h)⁻¹ 0 (clock:ℝ) :
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) → EuclideanSpace ℝ ι) =ᵐ[seedMeasure F]
      fun p => OuterRootPhysicalPath.rawY hV hh (lower_nonneg hm hlo) hup
        ((Real.sqrt h)⁻¹ • p.1) p.2 clock := by
  dsimp only
  let F := family hV hm hh hlo hup
  let d := OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup
  filter_upwards [(seedJet_memLp F d (Real.sqrt h)⁻¹ 0 (clock:ℝ)).coeFn_toLp] with p hp
  change (jetLp F d (Real.sqrt h)⁻¹ 0 (clock:ℝ)) p = _
  change (jetLp F d (Real.sqrt h)⁻¹ 0 (clock:ℝ)) p = seedJet d (Real.sqrt h)⁻¹ 0 (clock:ℝ) p at hp
  rw [hp]
  change (jet d 0 (clock:ℝ) ((Real.sqrt h)⁻¹ • p.1,p.2)).2 = _
  rw [jet_zero, jointPath_snd_eq_source d _ _ clock.2]
  simp only [SamplingCenterLp.path, SamplingFlowLp.sourcePath,
    SamplingFlowLp.sourceTime_eq d.hb clock.2, OuterRootPhysicalPath.rawY, d]

/-- Actual endpoint change minus the literal prescribed source quadrature.
All times, labels, weights, dimensions and orders are those of ClockSchedule. -/
theorem source_endpoint_defect (hsmall : h ≤ 1/2) (K : ℕ) (clock : ClockLaw.Clock) :
    let F := family hV hm hh hlo hup
    let d := OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup
    let n := ClockSchedule.sourceOrder K - 1
    ‖(jetLp F d (Real.sqrt h)⁻¹ 0 (clock:ℝ) - jetLp F d (Real.sqrt h)⁻¹ 0 0) -
      ∑ j : ClockCollocation.MainIndex h K,
        ClockSchedule.weight (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) clock j •
          jetLp F d (Real.sqrt h)⁻¹ 1 (ClockCollocation.u h K clock j)‖ ≤
      (ClockSchedule.sourceCells h : ℝ) *
        (2*((clock:ℝ)/(ClockSchedule.sourceCells h:ℝ))^(n+2)*
          ((2*h^2)*materialOrderFactor (Fintype.card ι) n / (3/4)^(n+1)) /
            ((n+1).factorial:ℝ)) := by
  have H := ClockQuadratureRows.source_finalRow hV hm hh hlo hup hsmall K clock
  dsimp only at H ⊢
  rw [integral_jet_one _ _ _ (by exact ⟨le_rfl, by norm_num [OuterRootOriginalData.data]⟩)
    (by exact clock.2)] at H
  exact H

end AcceleratedLogConcave.Root.OuterRootOutputQuadrature
