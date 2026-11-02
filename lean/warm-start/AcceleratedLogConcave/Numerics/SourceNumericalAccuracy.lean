import AcceleratedLogConcave.Numerics.SourceOriginalOutput

/-! The manuscript's internal numerical precision, with the available K+19
powers used to pay the entire derivative coefficient. Unlike a half-power
payment, this threshold retains the source's gain of one power of K. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourceNumericalAccuracy
open MeanFlowLp MeanResidualBridge MeanCollocationLp SourceScheduledData
open SmoothQuantitativeAssembly SourceOutputCoefficient
variable {D : ℕ}

def coefficientThreshold (K : ℕ) (c C : ℝ) : ℝ :=
  (SourceCoefficientAbsorption.orderLogBudget K c C+Real.log 22)/((K:ℝ)+19)

theorem coefficient_payment (K : ℕ) {c C y : ℝ}
    (hy : coefficientThreshold K c C ≤ y) :
    22*orderEnvelope (SourceSchedule.m K c C)*
      SourceSchedule.δ y ^ ((K:ℝ)+19) ≤ 1 := by
  have hp : 0 < (K:ℝ)+19 := by positivity
  have hpay := (div_le_iff₀ hp).mp hy
  have h := SourceCoefficientAbsorption.scalar_payment
    (u := orderEnvelope (SourceSchedule.m K c C))
    (B := SourceCoefficientAbsorption.orderLogBudget K c C)
    (N := 22) (s := 22) (a := (K:ℝ)+19) (y := y)
    (by simp [orderEnvelope, SourceCoefficientAbsorption.orderLogBudget])
    (by norm_num) (by simpa only [mul_comm] using hpay)
    (by norm_num) le_rfl
  simpa only [mul_comm (22:ℝ)] using h

/-- Internal numerical accuracy in its original physical units. All smoothness
and derivative premises are proved from the original C² data. -/
theorem output_bound (A : OriginalData D) (K : ℕ) {c C y S : ℝ}
    (hc : 0 < c) (hc80 : c ≤ 1/80) (hC : 30 ≤ C)
    (hy : meshResolution K c C ≤ y) (hS : 1 ≤ S)
    (hsizeR : A.ell*A.r^2 ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hsizeS : A.ell*A.r/A.sigma ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hpay : 12*Real.log (520*(SourceSchedule.m K c C:ℝ)^5*S) ≤ y)
    (hcoef : coefficientThreshold K c C ≤ y) :
    let d := datum A K c C y hc (by linarith) hy
    ‖output d (SourceSchedule.nP K C)-terminalTarget d‖ ≤
      physicalScale d*(SourceSchedule.δ y)^((K:ℝ)+1) := by
  let d := datum A K c C y hc (by linarith) hy
  have hm : 1 ≤ SourceSchedule.m K c C := by
    have := SourceSchedule.m_ge_two K hc (by linarith : c ≤ 1) (by linarith : 1 ≤ C)
    omega
  have ho := SourceScheduledConvergence.scheduled_output_bound A K hc hc80 hC hy hS
    hsizeR hsizeS hpay (velocityBounds_original_data d) (angleBounds_original_data d hm)
  have hco := coefficient_le d hm
  have hp := coefficient_payment K hcoef
  have hd := SourceSchedule.delta_pos y
  have hpow := Real.rpow_nonneg hd.le (2*(K:ℝ)+20)
  have htail := Real.rpow_nonneg hd.le ((K:ℝ)+1)
  have hs := physicalScale_nonneg d
  apply ho.trans
  apply (mul_le_mul_of_nonneg_right hco hpow).trans
  rw [show (2*(K:ℝ)+20:ℝ) = ((K:ℝ)+19)+((K:ℝ)+1) by ring,
    Real.rpow_add hd]
  nlinarith [mul_nonneg hs (mul_nonneg (sub_nonneg.mpr hp) htail)]

/-- A public dimension threshold pays any fixed scalar resolution requirement.
The threshold is fixed before the dimension and potential. -/
def dimensionThreshold (e B : ℝ) : ℕ := Nat.ceil (max 1 (Real.exp (B/e)))

theorem resolution_of_dimension {e B : ℝ} (he : 0 < e) {D : ℕ}
    (hD : dimensionThreshold e B ≤ D) : B ≤ e*Real.log (D:ℝ) := by
  have hceil : max 1 (Real.exp (B/e)) ≤ (D:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hD)
  have hlog := Real.log_le_log (Real.exp_pos (B/e)) ((le_max_right _ _).trans hceil)
  rw [Real.log_exp] at hlog
  exact (div_le_iff₀ he).mp hlog |>.trans_eq (mul_comm _ _)

theorem delta_dimension {e : ℝ} {D : ℕ} (hD : 0 < D) :
    SourceSchedule.δ (e*Real.log (D:ℝ)) = (D:ℝ)^(-e) := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  rw [SourceSchedule.δ, Real.rpow_def_of_pos hd]
  congr 1
  ring

end AcceleratedLogConcave.Numerics.SourceNumericalAccuracy
