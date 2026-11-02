import AcceleratedLogConcave.Oracle.SourceSchedule
import AcceleratedLogConcave.Root.ClockQuadraturePower
import AcceleratedLogConcave.Numerics.SourceNumericalAccuracy

/-! Explicit order-dependent resolution payment for the prescribed outer
quadrature. The threshold is fixed before the dimension or potential. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
namespace AcceleratedLogConcave.Root.ClockQuadratureResolution
open Oracle

def threshold (K : ℕ) : ℝ := Real.log (max 1 (ClockQuadraturePower.orderConstant K))/6

theorem threshold_nonneg (K : ℕ) : 0≤threshold K :=
  div_nonneg (Real.log_nonneg (le_max_left _ _)) (by norm_num)

/-- Pays the actual factorial/order envelope; it is not dropped from the bound. -/
theorem order_payment (P : SourceSchedule) (hy : threshold P.K≤P.y) :
    ClockQuadraturePower.orderConstant P.K*P.delta^6≤1 := by
  have hp : 0<max 1 (ClockQuadraturePower.orderConstant P.K) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have he : Real.log (max 1 (ClockQuadraturePower.orderConstant P.K))≤6*P.y := by
    unfold threshold at hy
    linarith
  have hb := Real.exp_le_exp.mpr he
  rw [Real.exp_log hp] at hb
  have hd : P.delta^6=Real.exp (-(6*P.y)) := by
    change (Real.exp (-P.y))^6=_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hd]
  calc
    _ ≤ Real.exp (6*P.y)*Real.exp (-(6*P.y)) :=
      mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hb) (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

theorem endpoint_payment (P : SourceSchedule) (hy : threshold P.K≤P.y) :
    ClockQuadraturePower.orderConstant P.K*P.delta^(P.K+6)≤P.delta^P.K := by
  rw [pow_add]
  calc
    _ = (ClockQuadraturePower.orderConstant P.K*P.delta^6)*P.delta^P.K := by ring
    _ ≤ 1*P.delta^P.K := mul_le_mul_of_nonneg_right (order_payment P hy) (pow_nonneg P.delta_pos.le _)
    _ = _ := one_mul _

/-- The public dimension choice pays this scalar threshold together with any
other fixed resolution requirement B, without changing the source mesh. -/
def dimensionThreshold (K : ℕ) (e B : ℝ) : ℕ :=
  Numerics.SourceNumericalAccuracy.dimensionThreshold e (max B (threshold K))

theorem dimension_payments {K D : ℕ} {e B : ℝ} (he : 0<e)
    (hD : dimensionThreshold K e B≤D) :
    B≤e*Real.log (D:ℝ) ∧ threshold K≤e*Real.log (D:ℝ) := by
  have h := Numerics.SourceNumericalAccuracy.resolution_of_dimension he hD
  exact ⟨(le_max_left _ _).trans h,(le_max_right _ _).trans h⟩
end AcceleratedLogConcave.Root.ClockQuadratureResolution
