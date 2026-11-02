import AcceleratedLogConcave.Oracle.PrivateSourceScalarAbsorption
import AcceleratedLogConcave.Numerics.SourceOutputCoefficient

/-! Dimension-independent absorption of the actual mean receiver's proved
order envelope. The enlargement is a fixed absolute multiplier of the existing
cubic-log coefficient; it changes neither the source algorithm nor its pins. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
namespace AcceleratedLogConcave.Oracle.MeanSourceScalarAbsorption
open Numerics SourceSchedule SchedulePolynomialBounds

/-- One explicit absolute enlargement, fixed before precision and dimension. -/
def threshold (P : SourceSchedule) : ℝ := 10000*PrivateSourceScalarAbsorption.threshold P

variable (P : SourceSchedule)

theorem private_threshold (hc : 0<P.csch) (hc1 : P.csch≤1) (hC : 1≤P.Csch)
    (hy : threshold P≤P.y) : PrivateSourceScalarAbsorption.threshold P≤P.y := by
  have hco := (CubicScheduleThreshold.coefficients_nonneg hc hc1 hC).2.2
  have hquad := PrivateSourceScalarAbsorption.Cquad_nonneg P hc hc1 hC
  have hlog := CubicScheduleThreshold.log_u_ge_half P
  have hn : 0≤PrivateSourceScalarAbsorption.threshold P := by
    unfold PrivateSourceScalarAbsorption.threshold PrivateSourceScalarAbsorption.Ccomplete
    positivity
  exact (by unfold threshold; linarith : PrivateSourceScalarAbsorption.threshold P≤threshold P).trans hy

/-- Reusing the proved logarithmic schedule estimate at a rescaled resolution
pays the larger mean derivative inventory. Order and all fixed schedule
constants are unchanged; no numerical-error bound is assumed. -/
theorem log_payment (hK : 10≤P.K) (hc : 0<P.csch) (hc1 : P.csch≤1)
    (hC : 1≤P.Csch) (hy : threshold P≤P.y) :
    (560000/P.w)*Real.log (12*(P.m:ℝ))≤P.y := by
  let S : SourceSchedule := {P with y := P.y/10000}
  have he : PrivateSourceScalarAbsorption.threshold S=PrivateSourceScalarAbsorption.threshold P := rfl
  have hs : PrivateSourceScalarAbsorption.threshold S≤S.y := by
    rw [he]
    change PrivateSourceScalarAbsorption.threshold P≤P.y/10000
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<10000)).2
    simpa only [threshold,mul_comm] using hy
  have h := PrivateSourceScalarAbsorption.quad_log_payment S hK hc hc1 hC hs
  change (56/P.w)*Real.log (12*(P.m:ℝ))≤P.y/10000 at h
  have hh := (le_div_iff₀ (by norm_num : (0:ℝ)<10000)).mp h
  calc
    (560000/P.w)*Real.log (12*(P.m:ℝ)) =
        ((56/P.w)*Real.log (12*(P.m:ℝ)))*10000 := by ring
    _ ≤ P.y := hh

/-- The actual order envelope grows at most with the stated order-log factor. -/
theorem log_orderEnvelope_le (m : ℕ) (hm : 1≤m) :
    Real.log (SourceOutputCoefficient.orderEnvelope m)≤40800*(m:ℝ)*Real.log (12*(m:ℝ)) := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hl : Real.log ((m:ℝ)+3)≤Real.log (12*(m:ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hn : 0≤Real.log (12*(m:ℝ)) := Real.log_nonneg (by linarith)
  unfold SourceOutputCoefficient.orderEnvelope
  rw [Real.log_exp]
  exact (mul_le_mul_of_nonneg_left hl (by positivity)).trans
    (mul_le_mul_of_nonneg_right (by linarith) hn)

/-- The true mean derivative envelope is absorbed with half the available
quadrature exponent left for precision, uniformly in dimension. -/
theorem order_payment (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
    (hC : 8≤P.Csch) (hy : threshold P≤P.y) :
    SourceOutputCoefficient.orderEnvelope P.m*P.delta^(P.A/2)≤P.delta^((P.K:ℝ)+1) := by
  have hc1 : P.csch≤1 := by linarith
  have hC1 : 1≤P.Csch := by linarith
  have hw := P.w_pos hc
  have hm : 1≤P.m := by have := P.m_ge_two hc hsmall hC1; omega
  have hA : 8*((P.K:ℝ)+2)≤P.A := mul_le_mul_of_nonneg_right hC (by positivity)
  have hmargin : P.A/4≤P.A/2-((P.K:ℝ)+1) := by nlinarith [Nat.cast_nonneg (α := ℝ) P.K]
  have hmw : (P.m:ℝ)*P.w≤2*P.A := by
    have hb := (P.m_bounds hc hC1).2
    have ht := (P.w_lt_t hc hC1).trans_le (P.t_le hc hsmall)
    have hh := (lt_div_iff₀ hw).mp (show (P.m:ℝ)-1<P.A/P.w by linarith)
    nlinarith [Nat.cast_nonneg (α := ℝ) P.K]
  have hscale : 40800*(P.m:ℝ)≤(P.A/2-((P.K:ℝ)+1))*(560000/P.w) := by
    apply (mul_le_mul_iff_left₀ hw).mp
    have he : ((P.A/2-((P.K:ℝ)+1))*(560000/P.w))*P.w =
        560000*(P.A/2-((P.K:ℝ)+1)) := by field_simp
    rw [he]
    nlinarith [Nat.cast_nonneg (α := ℝ) P.K]
  have hlog := log_orderEnvelope_le P.m hm
  have hn : 0≤Real.log (12*(P.m:ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1≤12*P.m by omega))
  have hpaid := log_payment P hK hc hc1 hC1 hy
  have hbound : Real.log (SourceOutputCoefficient.orderEnvelope P.m)≤(P.A/2-((P.K:ℝ)+1))*P.y :=
    hlog.trans ((mul_le_mul_of_nonneg_right hscale hn).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpaid (by linarith : 0≤P.A/2-((P.K:ℝ)+1))))
  have hp : 0<SourceOutputCoefficient.orderEnvelope P.m := Real.exp_pos _
  apply (Real.log_le_log_iff (mul_pos hp (Real.rpow_pos_of_pos P.delta_pos _))
    (Real.rpow_pos_of_pos P.delta_pos _)).mp
  rw [Real.log_mul hp.ne' (Real.rpow_pos_of_pos P.delta_pos _).ne',
    Real.log_rpow P.delta_pos,Real.log_rpow P.delta_pos,delta,Real.log_exp]
  nlinarith

/-- Both literal mean quadrature powers dominate the exponent used by the
order-envelope payment, with natural subtraction justified by m≥2. -/
theorem quadrature_exponents (hc : 0<P.csch) (hsmall : P.csch<1/160)
    (hC : 8≤P.Csch) :
    P.A/2≤SmoothRowPayments.exponent P.m P.w P.t ∧ P.A/2≤(P.m:ℝ)/3 := by
  have hC1 : 1≤P.Csch := by linarith
  have hm := P.m_ge_two hc hsmall hC1
  have hmR : (2:ℝ)≤P.m := by exact_mod_cast hm
  have hw := P.w_pos hc
  have hwt := P.w_lt_t hc hC1
  have ht := P.t_le hc hsmall
  have hA : 8*((P.K:ℝ)+2)≤P.A := mul_le_mul_of_nonneg_right hC (by positivity)
  have hmw : P.A≤(P.m:ℝ)*P.w := (div_le_iff₀ hw).mp (P.m_bounds hc hC1).1
  constructor
  · unfold SmoothRowPayments.exponent
    rw [Nat.cast_sub (by omega : 1≤P.m),Nat.cast_one]
    nlinarith [Nat.cast_nonneg (α := ℝ) P.K]
  · nlinarith [mul_le_mul_of_nonneg_left (hwt.le.trans ht) (by linarith : (0:ℝ)≤P.m)]

/-- Actual source row quadrature order is paid without a dimension factor
inside the resolution threshold. -/
theorem row_order_payment (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
    (hC : 8≤P.Csch) (hy : threshold P≤P.y) :
    SourceOutputCoefficient.orderEnvelope P.m*
      P.delta^(SmoothRowPayments.exponent P.m P.w P.t)≤P.delta^((P.K:ℝ)+1) := by
  have hbase := private_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
  have hd := P.delta_le_one (CubicSchedulePayments.prerequisites P hK hc hsmall hC
    (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith) (by linarith) hbase)).1
  have hp := Real.rpow_le_rpow_of_exponent_ge P.delta_pos hd (quadrature_exponents P hc hsmall hC).1
  exact (mul_le_mul_of_nonneg_left hp (le_trans (by norm_num) (SourceOutputCoefficient.orderEnvelope_ge_one P.m))).trans
    (order_payment P hK hc hsmall hC hy)

/-- The full final centering term uses its actual m/3 power. -/
theorem center_order_payment (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
    (hC : 8≤P.Csch) (hy : threshold P≤P.y) :
    SourceOutputCoefficient.orderEnvelope P.m*P.delta^((P.m:ℝ)/3)≤P.delta^((P.K:ℝ)+1) := by
  have hbase := private_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
  have hd := P.delta_le_one (CubicSchedulePayments.prerequisites P hK hc hsmall hC
    (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith) (by linarith) hbase)).1
  have hp := Real.rpow_le_rpow_of_exponent_ge P.delta_pos hd (quadrature_exponents P hc hsmall hC).2
  exact (mul_le_mul_of_nonneg_left hp (le_trans (by norm_num) (SourceOutputCoefficient.orderEnvelope_ge_one P.m))).trans
    (order_payment P hK hc hsmall hC hy)

end AcceleratedLogConcave.Oracle.MeanSourceScalarAbsorption
