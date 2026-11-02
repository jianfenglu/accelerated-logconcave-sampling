import AcceleratedLogConcave.Numerics.SourceOutputCoefficient
import AcceleratedLogConcave.Numerics.SourceCoefficientAbsorption
import AcceleratedLogConcave.Numerics.VelocitySmoothAssembly

/-! Complete coefficient payment for the actual smooth finite receiver.
Velocity is discharged by the published original-data supplier. Angle remains
an explicit analytic premise; this is not an executable-tape identification. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourceResolvedOutput
open MeanFlowLp MeanResidualBridge MeanCollocationLp SourceScheduledData
open SmoothQuantitativeAssembly SourceOutputCoefficient
variable {D : ℕ}

/-- No dimension, potential, oracle answer or resolution occurs in this
order-only coefficient threshold. -/
def coefficientThreshold (K : ℕ) (c C : ℝ) : ℝ :=
  2*(SourceCoefficientAbsorption.orderLogBudget K c C+Real.log 22)

theorem coefficient_payment (K : ℕ) {c C y : ℝ}
    (hy : coefficientThreshold K c C ≤ y) :
    22*orderEnvelope (SourceSchedule.m K c C)*
      SourceSchedule.δ y ^ ((1:ℝ)/2) ≤ 1 := by
  have h := SourceCoefficientAbsorption.scalar_payment
    (u := orderEnvelope (SourceSchedule.m K c C))
    (B := SourceCoefficientAbsorption.orderLogBudget K c C)
    (N := 22) (s := 22) (a := (1:ℝ)/2) (y := y)
    (by simp [orderEnvelope, SourceCoefficientAbsorption.orderLogBudget])
    (by norm_num) (by unfold coefficientThreshold at hy; linarith)
    (by norm_num) le_rfl
  simpa only [mul_comm (22:ℝ)] using h

/-- Scheduled numerical error with all order-dependent coefficients paid.
The remaining scale is the original gradient plus `ell*r*sqrt D`. -/
theorem output_bound (A : OriginalData D) (K : ℕ) {c C y S : ℝ}
    (hc : 0 < c) (hc80 : c ≤ 1/80) (hC : 30 ≤ C)
    (hy : meshResolution K c C ≤ y) (hS : 1 ≤ S)
    (hsizeR : A.ell*A.r^2 ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hsizeS : A.ell*A.r/A.sigma ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hpay : 12*Real.log (520*(SourceSchedule.m K c C:ℝ)^5*S) ≤ y)
    (hcoef : coefficientThreshold K c C ≤ y)
    (hangle : AngleBounds (datum A K c C y hc (by linarith) hy)) :
    let d := datum A K c C y hc (by linarith) hy
    ‖output d (SourceSchedule.nP K C)-terminalTarget d‖ ≤
      physicalScale d*(SourceSchedule.δ y)^(2*(K:ℝ)+39/2) := by
  let d := datum A K c C y hc (by linarith) hy
  have hm : 1 ≤ SourceSchedule.m K c C := by
    have := SourceSchedule.m_ge_two K hc (by linarith : c ≤ 1) (by linarith : 1 ≤ C)
    omega
  have ho := SourceScheduledConvergence.scheduled_output_bound A K hc hc80 hC hy hS
    hsizeR hsizeS hpay (velocityBounds_original_data d) hangle
  have hco := coefficient_le d hm
  have hp := coefficient_payment K hcoef
  have hd := SourceSchedule.delta_pos y
  have hpow := Real.rpow_nonneg hd.le (2*(K:ℝ)+20)
  have htail := Real.rpow_nonneg hd.le (2*(K:ℝ)+39/2)
  have hs := physicalScale_nonneg d
  apply ho.trans
  apply (mul_le_mul_of_nonneg_right hco hpow).trans
  rw [show (2*(K:ℝ)+20:ℝ) = 1/2+(2*(K:ℝ)+39/2) by ring,
    Real.rpow_add hd]
  nlinarith [mul_nonneg hs (mul_nonneg (sub_nonneg.mpr hp) htail)]

end AcceleratedLogConcave.Numerics.SourceResolvedOutput
