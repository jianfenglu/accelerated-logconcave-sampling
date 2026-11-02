import AcceleratedLogConcave.Numerics.SourceScheduledConvergence
import AcceleratedLogConcave.Numerics.SourcePhysicalError

/-! Original-gradient and dimension dependence of the complete scheduled
coefficient, including the full centering defect. No coefficient bound is
supplied as a hypothesis. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourceOutputCoefficient
open MeanFlowLp MeanResidualBridge MeanCollocationLp
open SmoothQuantitativeAssembly SmoothQuadraturePayments SmoothInventoryDimension
variable {D m : ℕ}

def orderEnvelope (m : ℕ) : ℝ :=
  Real.exp (10200*((m:ℝ)+3)*Real.log ((m:ℝ)+3))

def physicalScale (d : Data (Fin D) m) : ℝ :=
  d.ell*d.r*Real.sqrt (D:ℝ)+‖gradient d.F d.x‖

theorem orderEnvelope_ge_one (m : ℕ) : 1 ≤ orderEnvelope m := by
  apply Real.one_le_exp_iff.mpr
  have : 0 ≤ Real.log ((m:ℝ)+3) := Real.log_nonneg (by have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith)
  positivity

theorem scoreUnit_le_orderEnvelope (m : ℕ) : scoreUnit m ≤ orderEnvelope m := by
  apply (Real.le_exp_log _).trans
  apply Real.exp_le_exp.mpr
  have h := scoreUnit_log_le m
  have hl : 0 ≤ Real.log ((m:ℝ)+3) := Real.log_nonneg (by have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith)
  simp only [Nat.cast_add, Nat.cast_ofNat] at h
  nlinarith [mul_nonneg (show 0 ≤ (m:ℝ)+3 by positivity) hl]

/-- Exact factorization, valid also in dimension zero and at zero curvature. -/
theorem centering_coefficient_eq (d : Data (Fin D) m) :
    2*centerCoefficient d/(m.factorial:ℝ) =
      (d.ell*d.r*Real.sqrt (D:ℝ))*(scoreUnit m/2) := by
  unfold centerCoefficient scoreUnit auxiliaryConstant
  rw [show 2*(D:ℝ)*Tensor.AdjointReduction.PhaseBudget.Q 128 (5*m+1) =
    (D:ℝ)*(2*Tensor.AdjointReduction.PhaseBudget.Q 128 (5*m+1)) by ring,
    Real.sqrt_mul (Nat.cast_nonneg D)]
  ring

theorem physicalScale_nonneg (d : Data (Fin D) m) : 0 ≤ physicalScale d := by
  unfold physicalScale
  have := d.hell
  have := d.hr.le
  positivity

/-- The explicit complete coefficient has only the original gradient, physical
radius and square-root dimension outside its order-only exponential. -/
theorem coefficient_le (d : Data (Fin D) m) (hm : 1 ≤ m) :
    SourceScheduledConvergence.coefficient d ≤
      22*orderEnvelope m*physicalScale d := by
  have hseed := SourceContractedOutput.seed_payment d
  have hA : A m ≤ orderEnvelope m := SourcePhysicalError.A_value_bound hm
  have hscore := scoreUnit_le_orderEnvelope m
  have hE := orderEnvelope_ge_one m
  have hp : 0 ≤ d.ell*d.r*Real.sqrt (D:ℝ) :=
    mul_nonneg (mul_nonneg d.hell d.hr.le) (Real.sqrt_nonneg _)
  have hg := norm_nonneg (gradient d.F d.x)
  have hcenter := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hscore (by norm_num : (0:ℝ) ≤ 2)) hp
  have hquad := mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hp)
  rw [← centering_coefficient_eq d] at hcenter
  unfold SourceScheduledConvergence.coefficient physicalScale
  nlinarith [mul_nonneg (sub_nonneg.mpr hE) hp,
    mul_nonneg (sub_nonneg.mpr hE) hg]

end AcceleratedLogConcave.Numerics.SourceOutputCoefficient
