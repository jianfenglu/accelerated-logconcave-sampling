import AcceleratedLogConcave.Oracle.CubicSchedulePayments
import AcceleratedLogConcave.Root.ClockSchedule

/-! Scalar payment for a separately witnessed outer center inventory. The
cubic threshold and its constants are unchanged; no actual outer table is
constructed and no inventory is identified with NP or the final slot count. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.OuterInventoryPayment
open Oracle Oracle.ScalarSchedulePayment Oracle.CubicScheduleThreshold
variable (P : SourceSchedule)

/-- An algebraic envelope coefficient, not a new threshold constant. -/
def inventoryCoefficient : ℝ := 4096*P.Csch*((P.K:ℝ)+4)

theorem coefficient_gt_one (hC : 1 ≤ P.Csch) : 1 < inventoryCoefficient P := by
  have hk : (0:ℝ) ≤ P.K := Nat.cast_nonneg _
  have hc : 0 ≤ P.Csch := by linarith
  unfold inventoryCoefficient
  nlinarith [mul_nonneg hc hk]

theorem coefficient_le_a (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch) :
    inventoryCoefficient P ≤ a P := by
  have hn := (P.NP_bounds hC).1
  change P.Csch*((P.K:ℝ)+2) ≤ (P.NP:ℝ) at hn
  have hk : (0:ℝ) ≤ P.K := Nat.cast_nonneg _
  have hC0 : 0 ≤ P.Csch := by linarith
  have hn0 : (0:ℝ) ≤ P.NP := Nat.cast_nonneg _
  have hm4 : (1:ℝ) ≤ (P.m:ℝ)^4 := one_le_pow₀ (m_ge_one P hc hsmall hC)
  have ha : 256100*((P.NP:ℝ)+2) ≤ a P := by
    exact le_mul_of_one_le_right (by positivity) hm4
  have hb : inventoryCoefficient P ≤ 8192*(P.NP:ℝ) := by
    unfold inventoryCoefficient
    nlinarith [mul_nonneg hC0 hk]
  exact hb.trans (by linarith)

theorem log_coefficient_le_Ywork (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch) :
    Real.log (inventoryCoefficient P) ≤ Ywork P := by
  have hA := Real.log_nonneg (a_lower P hc hsmall hC).2
  have hL := Real.log_nonneg (L_ge_one P)
  have hG := G_ge_one P
  calc
    Real.log (inventoryCoefficient P) ≤ Real.log (a P) :=
      Real.log_le_log (by linarith [coefficient_gt_one P hC]) (coefficient_le_a P hc hsmall hC)
    _ ≤ Real.log (a P)+2*Real.log (L P) := by linarith
    _ ≤ 256*(G P:ℝ)*(Real.log (a P)+2*Real.log (L P)) :=
      le_mul_of_one_le_left (by linarith) (by linarith)

theorem ceil_exp_bound {y : ℝ} (hy : 0 ≤ y) :
    (Nat.ceil (Real.exp (y/128)):ℝ) ≤ 2*Real.exp (y/128) := by
  have he : 1 ≤ Real.exp (y/128) := Real.one_le_exp_iff.mpr (by positivity)
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (y/128)).le
  linarith

/-- Exact natural outer order: no rounding loss is introduced. -/
theorem outer_order_literal : Nat.ceil (128*((P.K:ℝ)+4)) = 128*(P.K+4) :=
  (ClockSchedule.sourceOrder_eq_ceil P.K).symm

/-- Prescribed outer uniform-cell count, without identifying any center inventory. -/
theorem outer_cells_literal : ClockSchedule.sourceCells P.delta = Nat.ceil (Real.exp (P.y/128)) := by
  unfold ClockSchedule.sourceCells
  congr 1
  rw [Real.rpow_def_of_pos P.delta_pos, SourceSchedule.delta, Real.log_exp]
  congr 1
  ring

/-- The witnessed inventory, with its genuine ceiling, pays this exponential envelope. -/
theorem inventory_envelope (hC : 0 ≤ P.Csch) (hy : 0 ≤ P.y) {Nr : ℕ}
    (hinv : (Nr:ℝ) ≤ P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ)) :
    16*(Nr:ℝ) ≤ inventoryCoefficient P*Real.exp (P.y/128) := by
  have hc := ceil_exp_bound hy
  calc
    16*(Nr:ℝ) ≤ 16*(P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ)) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ ≤ 16*(P.Csch*128*((P.K:ℝ)+4)*(2*Real.exp (P.y/128))) := by gcongr
    _ = _ := by unfold inventoryCoefficient; ring

theorem payment_square (Nr : ℕ) :
    (4*Real.sqrt (Nr:ℝ)*P.delta^(1-P.t))^2 =
      16*(Nr:ℝ)*Real.exp (-2*(1-P.t)*P.y) := by
  have hd : P.delta^(1-P.t) = Real.exp (-(1-P.t)*P.y) := by
    rw [Real.rpow_def_of_pos P.delta_pos, SourceSchedule.delta, Real.log_exp]
    congr 1
    ring
  rw [hd, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg Nr), pow_two (Real.exp (-(1-P.t)*P.y)), ← Real.exp_add]
  norm_num only [show (4:ℝ)^2 = 16 by norm_num]
  congr 2
  ring

/-- The exact 191/128 exponent comes from 2*(1-t)-1/128 at t<=1/4. -/
theorem square_envelope (hC : 0 ≤ P.Csch) (hy : 0 ≤ P.y) (ht : P.t ≤ 1/4) {Nr : ℕ}
    (hinv : (Nr:ℝ) ≤ P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ)) :
    (4*Real.sqrt (Nr:ℝ)*P.delta^(1-P.t))^2 ≤
      inventoryCoefficient P*Real.exp (-191*P.y/128) := by
  have hb0 : 0 ≤ inventoryCoefficient P := by unfold inventoryCoefficient; positivity
  rw [payment_square]
  calc
    16*(Nr:ℝ)*Real.exp (-2*(1-P.t)*P.y) ≤
        (inventoryCoefficient P*Real.exp (P.y/128))*Real.exp (-2*(1-P.t)*P.y) :=
      mul_le_mul_of_nonneg_right (inventory_envelope P hC hy hinv) (Real.exp_pos _).le
    _ = inventoryCoefficient P*Real.exp (P.y/128-2*(1-P.t)*P.y) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      nlinarith [mul_nonneg (show 0 ≤ 1/4-P.t by linarith) hy])) hb0

theorem payment_of_log (hC : 1 ≤ P.Csch) (hy : 0 ≤ P.y) (ht : P.t ≤ 1/4)
    (hlog : Real.log (inventoryCoefficient P) ≤ P.y) {Nr : ℕ}
    (hinv : (Nr:ℝ) ≤ P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ)) :
    4*Real.sqrt (Nr:ℝ)*P.delta^(1-P.t) ≤ 1 := by
  have hB : 0 < inventoryCoefficient P := by linarith [coefficient_gt_one P hC]
  have hlast : inventoryCoefficient P*Real.exp (-P.y) ≤ 1 := by
    rw [← Real.exp_log hB, ← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hs := (square_envelope P (by linarith) hy ht hinv).trans
    ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : -191*P.y/128 ≤ -P.y)) hB.le).trans hlast)
  exact (le_abs_self _).trans ((sq_le_one_iff_abs_le_one _).mp hs)

section Cubic
variable (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
  (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y)
include hK hc hsmall hC hy

theorem cubic_log_coefficient : Real.log (inventoryCoefficient P) ≤ P.y :=
  (log_coefficient_le_Ywork P hc hsmall (by linarith)).trans
    (CubicSchedulePayments.prerequisites P hK hc hsmall hC hy).2.1

/-- The old explicit scalar payment is discharged using only the source inventory witness. -/
theorem cubic_inventory_payment {Nr : ℕ}
    (hinv : (Nr:ℝ) ≤ P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ)) :
    4*Real.sqrt (Nr:ℝ)*P.delta^(1-P.t) ≤ 1 :=
  payment_of_log P (by linarith) (CubicSchedulePayments.prerequisites P hK hc hsmall hC hy).1
    ((P.t_le hc hsmall).trans (by norm_num)) (cubic_log_coefficient P hK hc hsmall hC hy) hinv
end Cubic
end AcceleratedLogConcave.Root.OuterInventoryPayment
