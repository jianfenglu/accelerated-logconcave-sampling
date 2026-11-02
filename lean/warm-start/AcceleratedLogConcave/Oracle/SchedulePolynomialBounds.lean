import AcceleratedLogConcave.Oracle.SourceSchedule

/-! Polynomial envelopes for the unchanged scalar schedule and elementary
logarithmic absorption. These facts do not pay a resolution, shift or work
threshold. All counts remain the original natural ceilings. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.SchedulePolynomialBounds
open SourceSchedule

def u (S : SourceSchedule) : ℝ := (S.K:ℝ)+2

variable (S : SourceSchedule)

theorem u_ge_two : 2 ≤ u S := by unfold u; linarith [Nat.cast_nonneg (α := ℝ) S.K]
theorem u_pos : 0 < u S := by have := u_ge_two S; linarith

theorem NP_upper (hC : 1 ≤ S.Csch) : (S.NP:ℝ) ≤ 2*S.Csch*u S := by
  have ha := S.A_ge hC
  have hu := u_ge_two S
  have hn := (S.NP_bounds hC).2
  change u S ≤ S.Csch*u S at ha
  change (S.NP:ℝ) < S.Csch*u S+1 at hn
  linarith

theorem D0_upper (hC : 1 ≤ S.Csch) : (S.D0:ℝ) ≤ 2*S.Csch*u S := by
  have ha := S.A_ge hC
  have hu := u_ge_two S
  have hn := (S.NP_bounds hC).2
  change u S ≤ S.Csch*u S at ha
  change (S.NP:ℝ) < S.Csch*u S+1 at hn
  simp only [D0, Nat.cast_add, Nat.cast_one]
  linarith

theorem A_div_t (hc : 0 < S.csch) : S.A/S.t = S.Csch*(u S)^2/S.csch := by
  unfold A t u
  field_simp

theorem H_add_one_upper (hc : 0 < S.csch) (hc1 : S.csch ≤ 1) (hC : 1 ≤ S.Csch) :
    (S.H:ℝ)+1 ≤ 2*S.Csch*(u S)^2/S.csch := by
  have hu := u_ge_two S
  have hCu : (u S)^2 ≤ S.Csch*(u S)^2 := le_mul_of_one_le_left (sq_nonneg _) hC
  have htwo : 2 ≤ S.Csch*(u S)^2/S.csch := (le_div_iff₀ hc).2 (by nlinarith)
  have hn := (S.H_bounds hc hC).2
  rw [A_div_t S hc] at hn
  calc
    _ ≤ 2*(S.Csch*(u S)^2/S.csch) := by linarith
    _ = _ := by ring

theorem T_upper (hc : 0 < S.csch) (hc1 : S.csch ≤ 1) (hC : 1 ≤ S.Csch) :
    S.T ≤ 256*S.Csch^2*(u S)^3/S.csch := by
  have hC0 : 0 ≤ S.Csch := by linarith
  have hu0 := u_pos S
  have hp := mul_le_mul (D0_upper S hC) (H_add_one_upper S hc hc1 hC)
    (by positivity : 0 ≤ (S.H:ℝ)+1) (by positivity : 0 ≤ 2*S.Csch*u S)
  calc
    _ = 64*((S.D0:ℝ)*((S.H:ℝ)+1)) := by unfold T gammaM; ring
    _ ≤ 64*((2*S.Csch*u S)*(2*S.Csch*(u S)^2/S.csch)) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

theorem inv_w_upper (hc : 0 < S.csch) (hc1 : S.csch ≤ 1) (hC : 1 ≤ S.Csch) :
    1/S.w ≤ 256*S.Csch^2*(u S)^3/S.csch^2 := by
  calc
    _ = S.T/S.csch := by unfold w; field_simp
    _ ≤ (256*S.Csch^2*(u S)^3/S.csch)/S.csch :=
      div_le_div_of_nonneg_right (T_upper S hc hc1 hC) hc.le
    _ = _ := by ring

theorem m_upper (hc : 0 < S.csch) (hc1 : S.csch ≤ 1) (hC : 1 ≤ S.Csch) :
    (S.m:ℝ) ≤ 257*S.Csch^3*(u S)^4/S.csch^2 := by
  have hu := u_ge_two S
  have hC0 : 0 ≤ S.Csch := by linarith
  have hCu : 1 ≤ S.Csch^3*(u S)^4 := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hC) (one_le_pow₀ (by linarith : 1 ≤ u S))
  have henv : 1 ≤ S.Csch^3*(u S)^4/S.csch^2 := (le_div_iff₀ (sq_pos_of_pos hc)).2 (by nlinarith)
  have hi := mul_le_mul_of_nonneg_left (inv_w_upper S hc hc1 hC)
    (by positivity : 0 ≤ S.Csch*u S)
  have hx : S.A/S.w ≤ 256*(S.Csch^3*(u S)^4/S.csch^2) := by
    calc
      _ = (S.Csch*u S)*(1/S.w) := by unfold A u; ring
      _ ≤ (S.Csch*u S)*(256*S.Csch^2*(u S)^3/S.csch^2) := hi
      _ = _ := by ring
  have hm := (S.m_bounds hc hC).2
  calc
    _ ≤ 257*(S.Csch^3*(u S)^4/S.csch^2) := by linarith
    _ = _ := by ring

/-- Adjustable logarithmic absorption; no schedule or threshold is changed. -/
theorem log_one_add_le {y L : ℝ} (hy : 0 ≤ y) (hL : 1 ≤ L) :
    Real.log (1+y) ≤ y/L+Real.log L := by
  have hL0 : 0 < L := by linarith
  have hy1 : 0 < 1+y := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hy1 hL0)
  rw [Real.log_div hy1.ne' hL0.ne', add_div] at h
  have hi : 1/L ≤ (1:ℝ) := (div_le_one₀ hL0).2 hL
  linarith

/-- The order stays inside a logarithm: only 4*log(K+2), not a quartic loss. -/
theorem log_m_upper (hc : 0 < S.csch) (hc1 : S.csch ≤ 1) (hC : 1 ≤ S.Csch) :
    Real.log (S.m:ℝ) ≤ Real.log 257+3*Real.log S.Csch+4*Real.log (u S)-2*Real.log S.csch := by
  have hC0 : 0 < S.Csch := by linarith
  have hm0 : (0:ℝ) < S.m := by exact_mod_cast S.m_pos hc hC
  have hu := u_pos S
  have h := Real.log_le_log hm0 (m_upper S hc hc1 hC)
  rw [Real.log_div (by positivity) (pow_ne_zero _ hc.ne'),
    Real.log_mul (by positivity) (pow_ne_zero _ hu.ne'),
    Real.log_mul (by norm_num) (pow_ne_zero _ hC0.ne'), Real.log_pow, Real.log_pow, Real.log_pow] at h
  norm_num at h
  exact h

theorem t_le_one (hc1 : S.csch ≤ 1) : S.t ≤ 1 := by
  apply (div_le_iff₀ (u_pos S)).2
  have hu := u_ge_two S
  change S.csch ≤ 1*u S
  linarith

theorem log_one_add_ty_le (hc : 0 < S.csch) (hc1 : S.csch ≤ 1) (hy : 0 ≤ S.y) :
    Real.log (1+S.t*S.y) ≤ Real.log (1+S.y) := by
  have ht := S.t_pos hc
  apply Real.log_le_log (by positivity)
  have hty := mul_le_mul_of_nonneg_right (t_le_one S hc1) hy
  linarith

theorem log_one_add_ty_absorb (hc : 0 < S.csch) (hy : 0 ≤ S.y) {L : ℝ} (hL : 1 ≤ L) :
    Real.log (1+S.t*S.y) ≤ S.t*S.y/L+Real.log L :=
  log_one_add_le (mul_nonneg (S.t_pos hc).le hy) hL

/-- A useful cubic-scale specialization, without asserting a paid threshold. -/
theorem log_one_add_ty_cubic (hc : 0 < S.csch) (hy : 0 ≤ S.y) :
    Real.log (1+S.t*S.y) ≤ S.t*S.y/(u S)^3+3*Real.log (u S) := by
  have hu : 1 ≤ u S := le_trans (by norm_num) (u_ge_two S)
  simpa only [Real.log_pow, Nat.cast_ofNat] using
    log_one_add_ty_absorb S hc hy (one_le_pow₀ hu : 1 ≤ (u S)^3)

/-- The Bsize factor keeps its y-dependent logarithm. -/
theorem log_Bsize (hc : 0 < S.csch) (hC : 1 ≤ S.Csch) (hy : 0 ≤ S.y) :
    Real.log S.Bsize = Real.log (Real.sqrt 1280)+2*Real.log (S.m:ℝ)+Real.log (1+S.t*S.y) := by
  have hm0 : (0:ℝ) < S.m := by exact_mod_cast S.m_pos hc hC
  have ht := S.t_pos hc
  unfold Bsize
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (pow_ne_zero _ hm0.ne'), Real.log_pow]
  norm_num

/-- Exact logarithm of the earlier real count envelope. This is an expression
identity, not a newly assumed or constructed finite inventory. In particular
2*w*y and the log(1+t*y) term must not be discarded. -/
theorem log_count_expression (hc : 0 < S.csch) (hC : 1 ≤ S.Csch) (hy : 0 ≤ S.y) :
    Real.log (1280*(S.m:ℝ)^4*((1+S.t*S.y)/S.h0)^2) =
      Real.log 1280+4*Real.log (S.m:ℝ)+2*Real.log (1+S.t*S.y)+2*S.w*S.y := by
  have hm0 : (0:ℝ) < S.m := by exact_mod_cast S.m_pos hc hC
  have ht := S.t_pos hc
  have hh := S.h0_pos
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (pow_ne_zero _ hm0.ne'), Real.log_pow, Real.log_pow,
    Real.log_div (by positivity) hh.ne', S.h0_eq_exp, Real.log_exp]
  norm_num
  ring
end AcceleratedLogConcave.Oracle.SchedulePolynomialBounds
