import AcceleratedLogConcave.Root.ClockCollocationInventory

/-! Aggregate numerical work payment for the fixed-clock main component.
The existing cubic threshold is unchanged. Initialization is charged, and
Gaussian work means blocks, not scalar normals or arithmetic operations. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockMainWorkBounds
open Oracle Oracle.ScalarSchedulePayment Oracle.CubicScheduleThreshold
open scoped BigOperators
variable (P : SourceSchedule)

/-- The literal internal mean order dominates K+2. -/
theorem order_lower (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch) :
    (P.K:ℝ)+2 ≤ (P.m:ℝ) := by
  have hw := P.w_pos hc
  have hw1 : P.w ≤ 1 := (P.w_lt_t hc hC).le.trans ((P.t_le hc hsmall).trans (by norm_num))
  have hA := P.A_ge hC
  have hA0 : 0 ≤ P.A := by linarith [Nat.cast_nonneg (α := ℝ) P.K]
  have hdiv : P.A ≤ P.A/P.w := (le_div_iff₀ hw).mpr (mul_le_of_le_one_right hA0 hw1)
  exact hA.trans (hdiv.trans (P.m_bounds hc hC).1)

theorem layers_lower (hC : 1 ≤ P.Csch) : (P.K:ℝ)+2 ≤ (P.NP:ℝ)+2 := by
  have h := (P.A_ge hC).trans (P.NP_bounds hC).1
  linarith

/-- The old logarithmic payment already reserves the coefficient cost. -/
theorem log_a_payment (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hwork : Ywork P ≤ P.y) : Real.log (a P) ≤ P.y/256 := by
  have ha := Real.log_nonneg (a_lower P hc hsmall hC).2
  have hl := Real.log_nonneg (L_ge_one P)
  calc
    Real.log (a P) ≤ Real.log (a P)+2*Real.log (L P) := by linarith
    _ ≤ (G P:ℝ)*(Real.log (a P)+2*Real.log (L P)) :=
      le_mul_of_one_le_left (by positivity) (G_ge_one P)
    _ ≤ P.y/256 := work_log_payment P hwork

theorem coefficient_payment (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch) :
    3585*((P.K:ℝ)+2)^2 ≤ a P := by
  have hu : (2:ℝ) ≤ (P.K:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) P.K]
  have hm := order_lower P hc hsmall hC
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (P.K:ℝ)+2) hm 4
  have hu2 : 4 ≤ ((P.K:ℝ)+2)^2 := by nlinarith
  have hu4 : 4*((P.K:ℝ)+2)^2 ≤ ((P.K:ℝ)+2)^4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu2) (sq_nonneg ((P.K:ℝ)+2))]
  have ha := (a_lower P hc hsmall hC).1
  nlinarith [sq_nonneg ((P.K:ℝ)+2)]

/-- Retains the literal ceiling and the 128*(K+4) outer order. -/
theorem inventory_literal : ClockCollocation.count P.delta P.K =
    128*(P.K+4)*Nat.ceil (Real.exp (P.y/128)) := by
  unfold ClockCollocation.count
  rw [OuterInventoryPayment.outer_cells_literal]
  unfold ClockSchedule.sourceOrder
  ring

theorem inventory_upper (hy : 0 ≤ P.y) :
    (ClockCollocation.count P.delta P.K:ℝ) ≤ 256*((P.K:ℝ)+4)*Real.exp (P.y/128) := by
  rw [inventory_literal]
  push_cast
  have h := mul_le_mul_of_nonneg_left (OuterInventoryPayment.ceil_exp_bound hy)
    (by positivity : 0 ≤ 128*((P.K:ℝ)+4))
  nlinarith

/-- Pure scalar accounting, including one setup block and N initialization blocks. -/
theorem component_envelope {u d n E F : ℝ} (hu : 1 ≤ u) (hd0 : 0 ≤ d) (hd : d ≤ 2*u)
    (hn0 : 0 ≤ n) (hn : n ≤ 256*d*F) (hE : 1 ≤ E) (hF : 1 ≤ F)
    {s : ℝ} (hs : s ≤ n*E) :
    1+n+d*(2*n+s) ≤ 3585*u^2*F*E := by
  have hE0 : 0 ≤ E := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hpoly : 1+256*d+768*d^2 ≤ 3585*u^2 := by
    have hd2 := pow_le_pow_left₀ hd0 hd 2
    nlinarith [sq_nonneg (u-1), mul_nonneg hu0 (sub_nonneg.mpr hu)]
  have hc : 1+n+3*d*n ≤ (1+256*d+768*d^2)*F := by
    nlinarith [mul_le_mul_of_nonneg_left hn (show 0 ≤ 3*d by positivity)]
  calc
    1+n+d*(2*n+s) ≤ (1+n+3*d*n)*E := by
      nlinarith [mul_nonneg (show 0 ≤ 1+n+2*d*n by positivity) (sub_nonneg.mpr hE),
        mul_le_mul_of_nonneg_left hs hd0]
    _ ≤ ((1+256*d+768*d^2)*F)*E := mul_le_mul_of_nonneg_right hc hE0
    _ ≤ (3585*u^2*F)*E := by gcongr

/-- No new threshold: the existing Ywork assumption absorbs the aggregate work. -/
theorem scalar_payment (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hwork : Ywork P ≤ P.y) {s : ℝ}
    (hs : s ≤ (ClockCollocation.count P.delta P.K:ℝ)*Real.exp (P.y/64)) :
    1+(ClockCollocation.count P.delta P.K:ℝ)+((P.K:ℝ)+4)*
      (2*(ClockCollocation.count P.delta P.K:ℝ)+s) ≤ Real.exp (7*P.y/256) := by
  have ha : a P ≤ Real.exp (P.y/256) :=
    (Real.log_le_iff_le_exp (by linarith [(a_lower P hc hsmall hC).2])).mp
      (log_a_payment P hc hsmall hC hwork)
  have he := component_envelope (u := (P.K:ℝ)+2) (d := (P.K:ℝ)+4)
    (by linarith [Nat.cast_nonneg (α := ℝ) P.K]) (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) P.K])
    (Nat.cast_nonneg _) (inventory_upper P hy)
    (Real.one_le_exp_iff.mpr (by positivity)) (Real.one_le_exp_iff.mpr (by positivity)) hs
  calc
    _ ≤ 3585*((P.K:ℝ)+2)^2*Real.exp (P.y/128)*Real.exp (P.y/64) := he
    _ ≤ a P*Real.exp (P.y/128)*Real.exp (P.y/64) := by
      gcongr
      exact coefficient_payment P hc hsmall hC
    _ ≤ Real.exp (P.y/256)*Real.exp (P.y/128)*Real.exp (P.y/64) := by gcongr
    _ = Real.exp (7*P.y/256) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem cubic_payment (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y) {s : ℝ}
    (hs : s ≤ (ClockCollocation.count P.delta P.K:ℝ)*Real.exp (P.y/64)) :
    1+(ClockCollocation.count P.delta P.K:ℝ)+((P.K:ℝ)+4)*
      (2*(ClockCollocation.count P.delta P.K:ℝ)+s) ≤ Real.exp (P.y/32) := by
  have hp := CubicSchedulePayments.prerequisites P hK hc hsmall hC hy
  exact (scalar_payment P hc hsmall (by linarith) hp.1 hp.2.1 hs).trans
    (Real.exp_le_exp.mpr (by linarith [hp.1]))

end AcceleratedLogConcave.Root.ClockMainWorkBounds
