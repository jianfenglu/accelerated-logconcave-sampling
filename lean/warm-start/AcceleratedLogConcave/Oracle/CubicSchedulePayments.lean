import AcceleratedLogConcave.Oracle.CubicScheduleThreshold
import AcceleratedLogConcave.Oracle.ScalarSchedulePayment

/-! Source guards and actual producer scalar payments from the fixed cubic-log
threshold. Actual query-shift, full work and original-data root assembly are
separate consumers and are not applied here. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.CubicSchedulePayments
open SourceSchedule SchedulePolynomialBounds ScalarSchedulePayment CubicScheduleThreshold

variable (P : SourceSchedule)

theorem shift_precision (hK : 10 ≤ P.K) : (1/2:ℝ) < (P.K:ℝ) := by
  have hk : (10:ℝ) ≤ P.K := by exact_mod_cast hK
  linarith

theorem support_height (hC : 8 ≤ P.Csch) : 8*(P.K:ℝ)+4 ≤ (P.Hs:ℝ) := by
  have hn := (P.NP_bounds (by linarith : 1 ≤ P.Csch)).1
  have hp := mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ (P.K:ℝ)+2)
  change P.A ≤ (P.Hs:ℝ) at hn
  unfold A at hn
  linarith

/-- Natural truncated subtraction remains literal; casting is justified only
once 2 <= 4*K is established. -/
theorem quarter_rank_cast (hK : 10 ≤ P.K) :
    (Precision.precisionRank (1/4) (P.K:ℝ):ℝ) = 4*(P.K:ℝ)-2 := by
  rw [P.quarter_rank, Nat.cast_sub (by omega : 2 ≤ 4*P.K)]
  push_cast
  rfl

theorem quarter_rank_cap (hK : 10 ≤ P.K) (hC : 8 ≤ P.Csch) :
    Precision.precisionRank (1/4) (P.K:ℝ) ≤ P.Hs :=
  RecursiveExecutable.quarterRank_le_source_height (shift_precision P hK) (support_height P hC)

theorem source_guards (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 8 ≤ P.Csch) :
    (1/2:ℝ) < (P.K:ℝ) ∧ 8*(P.K:ℝ)+4 ≤ (P.Hs:ℝ) ∧
    0 < P.w ∧ P.w < P.t ∧ P.t ≤ 1/60 ∧ 2 ≤ P.m ∧
    Precision.precisionRank (1/4) (P.K:ℝ) = 4*P.K-2 ∧
    Precision.precisionRank (1/4) (P.K:ℝ) ≤ P.Hs ∧ rho P ≤ P.H ∧
    10*P.t*(Precision.precisionRank (1/4) (P.K:ℝ):ℝ) < 1/4 := by
  have hC1 : 1 ≤ P.Csch := by linarith
  exact ⟨shift_precision P hK, support_height P hC, P.w_pos hc, P.w_lt_t hc hC1,
    P.t_le hc hsmall, P.m_ge_two hc hsmall hC1, P.quarter_rank,
    quarter_rank_cap P hK hC, rho_le_H P hc hC1, P.rank_budget hc hsmall⟩

/-- The only new resolution hypothesis is the fixed cubic-log threshold. -/
theorem prerequisites (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y) :
    0 ≤ P.y ∧ Ywork P ≤ P.y ∧ Ygeom P ≤ P.y :=
  threshold_pays P hK hc (by linarith) (by linarith) hy

theorem radius_guard (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y) : P.R ≤ 1/2 := by
  have hp := prerequisites P hK hc hsmall hC hy
  have hg := geometry_caps P hc hsmall (by linarith) hp.1 hp.2.2
  exact hg.2.2.1.trans hg.2.2.2

theorem actual_counts (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y) :
    let hR := radius_guard P hK hc hsmall hC hy
    (n P hR:ℝ) ≤ 1280*(P.m:ℝ)^4*(1+P.t*P.y)^2*Real.exp (2*P.w*P.y) ∧
    (ns P hR:ℝ) ≤ 1280*(P.m:ℝ)^4*(1+P.t*P.y)^2*Real.exp (2*P.w*P.y) := by
  have hp := prerequisites P hK hc hsmall hC hy
  exact ScalarSchedulePayment.actual_counts P _ hc hsmall (by linarith) hp.1 hp.2.2

theorem actual_scalar_payments (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y) :
    let hR := radius_guard P hK hc hsmall hC hy
    D P hR ≤ a P*(1+P.y)^2*Real.exp (2*P.w*P.y) ∧
    (D P hR)^(G P) ≤ Real.exp (P.y/64) ∧
    (D P hR)^(P.Hs+2) ≤ P.Ds ∧ (D P hR)^(P.Hs+1) ≤ P.Ds ∧
    P.delta ≤ (Q P)^(-12:ℝ) ∧
    (0 < P.delta ∧ P.delta ≤ P.R ∧ P.R ≤ P.h0 ∧ P.h0 ≤ 1/2) ∧
    Real.sqrt (n P hR) ≤ P.Bsize*P.delta^(-P.w) ∧ Real.sqrt (ns P hR) ≤ P.Bsize*P.delta^(-P.w) := by
  have hp := prerequisites P hK hc hsmall hC hy
  exact ScalarSchedulePayment.actual_payments P hc hsmall (by linarith) hp.1 hp.2.1 hp.2.2
end AcceleratedLogConcave.Oracle.CubicSchedulePayments
