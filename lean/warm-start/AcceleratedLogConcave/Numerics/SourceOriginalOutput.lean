import AcceleratedLogConcave.Numerics.SourceResolvedOutput
import AcceleratedLogConcave.Numerics.AngleSmoothAssembly
import AcceleratedLogConcave.Numerics.SourceScheduledCoupling

/-! Original-data numerical guarantees for the existing same-seed smooth
receiver. Both analytic interfaces are discharged. Source mesh, size and
resolution conditions remain explicit scalar conditions. The common-seed
coupling retains G0; no identification with the recursive compiler P is made. -/
noncomputable section
open MeasureTheory
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourceOriginalOutput
open MeanFlowLp MeanResidualBridge MeanCollocationLp SourceScheduledData
open SmoothQuantitativeAssembly SourceOutputCoefficient
open Analysis.PositiveVarianceSlab AffineGraph
variable {D m : ℕ}

theorem original_regularity (d : Data (Fin D) m) (hm : 1 ≤ m) :
    AffineResidual.Mean.Regularity d.G (curvesWithSmoothBranches d) (operator d) 0 d.r
      (left (backwardEnd d.G.R))
      (right (backwardEnd d.G.R)) (budget d) :=
  regularity d hm (velocityBounds_original_data d) (angleBounds_original_data d hm)

theorem output_bound (A : OriginalData D) (K : ℕ) {c C y S : ℝ}
    (hc : 0 < c) (hc80 : c ≤ 1/80) (hC : 30 ≤ C)
    (hy : meshResolution K c C ≤ y) (hS : 1 ≤ S)
    (hsizeR : A.ell*A.r^2 ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hsizeS : A.ell*A.r/A.sigma ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hpay : 12*Real.log (520*(SourceSchedule.m K c C:ℝ)^5*S) ≤ y)
    (hcoef : SourceResolvedOutput.coefficientThreshold K c C ≤ y) :
    let d := datum A K c C y hc (by linarith) hy
    ‖output d (SourceSchedule.nP K C)-terminalTarget d‖ ≤
      physicalScale d*(SourceSchedule.δ y)^(2*(K:ℝ)+39/2) := by
  have hm : 1 ≤ SourceSchedule.m K c C := by
    have := SourceSchedule.m_ge_two K hc (by linarith : c ≤ 1) (by linarith : 1 ≤ C)
    omega
  exact SourceResolvedOutput.output_bound A K hc hc80 hC hy hS hsizeR hsizeS hpay
    hcoef (angleBounds_original_data _ hm)

theorem coupling_bound (A : OriginalData D) (K : ℕ) {c C y S : ℝ}
    (hc : 0 < c) (hc80 : c ≤ 1/80) (hC : 30 ≤ C)
    (hy : meshResolution K c C ≤ y) (hS : 1 ≤ S)
    (hsizeR : A.ell*A.r^2 ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hsizeS : A.ell*A.r/A.sigma ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hpay : 12*Real.log (520*(SourceSchedule.m K c C:ℝ)^5*S) ≤ y)
    (hcoef : SourceResolvedOutput.coefficientThreshold K c C ≤ y) :
    let d := datum A K c C y hc (by linarith) hy
    MeanBenchmarkCoupling.CouplingTarget d ∧
      (∫ z, ‖z.1.1-z.2.1‖^2 ∂MeanBenchmarkCoupling.coupling d (SourceSchedule.nP K C)) ≤
        (physicalScale d*(SourceSchedule.δ y)^(2*(K:ℝ)+39/2))^2 := by
  let d := datum A K c C y hc (by linarith) hy
  refine ⟨MeanBenchmarkCoupling.coupling_target d, ?_⟩
  rw [MeanBenchmarkCoupling.coupling_cost_eq]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (output_bound A K hc hc80 hC hy hS hsizeR hsizeS hpay hcoef) 2

end AcceleratedLogConcave.Numerics.SourceOriginalOutput
