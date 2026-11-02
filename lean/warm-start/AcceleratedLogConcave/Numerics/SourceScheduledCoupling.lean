import AcceleratedLogConcave.Numerics.SourceScheduledConvergence
import AcceleratedLogConcave.Numerics.MeanBenchmarkCoupling

/-! Scheduled error on the existing genuine common-seed retained coupling.
The retained coordinate here is the centering input G0. It is NOT identified
with the original compiler P or with the recursive executable tape. That
separate joint-law identification remains an explicit downstream obligation.
No legacy clipped endpoint regularity is used. -/
noncomputable section
open MeasureTheory
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourceScheduledCoupling
open MeanFlowLp MeanResidualBridge MeanCollocationLp SourceScheduledData
open SmoothQuantitativeAssembly SmoothQuadraturePayments SourceScheduledConvergence
variable {D : ℕ}

theorem coupling_bound (A : OriginalData D) (K : ℕ) {c C y S : ℝ}
    (hc : 0 < c) (hc80 : c ≤ 1/80) (hC : 30 ≤ C)
    (hy : meshResolution K c C ≤ y) (hS : 1 ≤ S)
    (hsizeR : A.ell*A.r^2 ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hsizeS : A.ell*A.r/A.sigma ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hpay : 12*Real.log (520*(SourceSchedule.m K c C:ℝ)^5*S) ≤ y)
    (hvelocity : VelocityBounds (datum A K c C y hc (by linarith) hy))
    (hangle : AngleBounds (datum A K c C y hc (by linarith) hy)) :
    let d := datum A K c C y hc (by linarith) hy
    MeanBenchmarkCoupling.CouplingTarget d ∧
      (∫ z, ‖z.1.1-z.2.1‖^2 ∂MeanBenchmarkCoupling.coupling d (SourceSchedule.nP K C)) ≤
        (coefficient d*(SourceSchedule.δ y)^(2*(K:ℝ)+20))^2 := by
  let d := datum A K c C y hc (by linarith) hy
  refine ⟨MeanBenchmarkCoupling.coupling_target d, ?_⟩
  rw [MeanBenchmarkCoupling.coupling_cost_eq]
  have h := SourceScheduledConvergence.scheduled_output_bound A K hc hc80 hC hy hS
    hsizeR hsizeS hpay hvelocity hangle
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end AcceleratedLogConcave.Numerics.SourceScheduledCoupling
