import AcceleratedLogConcave.Oracle.SchedulePolynomialBounds
import AcceleratedLogConcave.Oracle.RecursiveSizeBound

/-! Explicit scalar payments. Thresholds retain their logarithms and are not
converted to a cubic public recipe. Actual finite inventories are supplied by
the companion producer adapter, not assumed to count seeds or dimensions. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.ScalarSchedulePayment
open SourceSchedule SchedulePolynomialBounds RecursiveSize

def G (P : SourceSchedule) : ℕ := P.D0*(P.H+1)
def a (P : SourceSchedule) : ℝ := 256100*((P.NP:ℝ)+2)*(P.m:ℝ)^4
def L (P : SourceSchedule) : ℝ := 512*(G P:ℝ)
def Ywork (P : SourceSchedule) : ℝ := 256*(G P:ℝ)*(Real.log (a P)+2*Real.log (L P))
def Ygeom (P : SourceSchedule) : ℝ := Real.log 2/P.w
def rho (P : SourceSchedule) : ℕ := Precision.precisionRank P.t (P.K:ℝ)
def step (P : SourceSchedule) : ℝ := RecursiveSize.stepFactor P.m P.Bsize
def Q (P : SourceSchedule) : ℝ := 520*(P.m:ℝ)^5*(step P)^(rho P)

variable (P : SourceSchedule)

theorem G_pos : 0 < G P := Nat.mul_pos P.D0_pos (Nat.succ_pos _)
theorem G_real_pos : 0 < (G P:ℝ) := by exact_mod_cast G_pos P
theorem G_ge_one : (1:ℝ) ≤ G P := by exact_mod_cast G_pos P

theorem T_eq : P.T = 64*(G P:ℝ) := by unfold T gammaM G; push_cast; ring

theorem G_mul_w : (G P:ℝ)*P.w = P.csch/64 := by
  rw [w, T_eq P]
  field_simp [(G_real_pos P).ne']

theorem L_ge_one : 1 ≤ L P := by unfold L; have := G_ge_one P; linarith

theorem rho_le_H (hc : 0 < P.csch) (hC : 1 ≤ P.Csch) : rho P ≤ P.H := P.precision_rank_le_H hc hC

theorem rho_add_one_le_G (hc : 0 < P.csch) (hC : 1 ≤ P.Csch) : rho P+1 ≤ G P := by
  have h := rho_le_H P hc hC
  have hd := P.D0_pos
  have hm : P.H+1 ≤ P.D0*(P.H+1) := Nat.le_mul_of_pos_left _ hd
  exact (Nat.add_le_add_right h 1).trans hm

theorem m_ge_one (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch) : (1:ℝ) ≤ P.m := by
  exact_mod_cast (show 1 ≤ P.m by have := P.m_ge_two hc hsmall hC; omega)

theorem a_lower (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch) :
    1000*(P.m:ℝ)^4 ≤ a P ∧ 1 ≤ a P := by
  have hm := m_ge_one P hc hsmall hC
  have hp : 1 ≤ (P.m:ℝ)^4 := one_le_pow₀ hm
  have hnp : 0 ≤ (P.NP:ℝ) := Nat.cast_nonneg _
  have ha : 1000*(P.m:ℝ)^4 ≤ a P := by
    unfold a
    nlinarith [mul_nonneg hnp (pow_nonneg (Nat.cast_nonneg P.m) 4)]
  exact ⟨ha, by linarith⟩

theorem geometry_caps (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hgeom : Ygeom P ≤ P.y) :
    0 < P.delta ∧ P.delta ≤ P.R ∧ P.R ≤ P.h0 ∧ P.h0 ≤ 1/2 := by
  have hres : Real.log 2 ≤ P.w*P.y := by
    have h := (div_le_iff₀ (P.w_pos hc)).mp hgeom
    nlinarith
  have ht : P.t ≤ 1 := (P.t_le hc hsmall).trans (by norm_num)
  have hδR := Real.rpow_le_rpow_of_exponent_ge P.delta_pos (P.delta_le_one hy) ht
  refine ⟨P.delta_pos, ?_, P.R_le_h0 hc hC hy, P.h0_le_half_iff.mpr hres⟩
  simpa only [Real.rpow_one, SourceSchedule.R] using hδR

theorem work_log_payment (hwork : Ywork P ≤ P.y) :
    (G P:ℝ)*(Real.log (a P)+2*Real.log (L P)) ≤ P.y/256 := by
  unfold Ywork at hwork
  linarith

/-- D's polynomial/exponential envelope is paid without dropping its y dependence. -/
theorem log_D_payment (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hwork : Ywork P ≤ P.y) (d : ℝ) (hd : 1 ≤ d)
    (hupper : d ≤ a P*(1+P.y)^2*Real.exp (2*P.w*P.y)) :
    (G P:ℝ)*Real.log d ≤ P.y/64 := by
  have ha := (a_lower P hc hsmall hC).2
  have hg := (G_real_pos P).le
  have hlog := Real.log_le_log (show 0 < d by linarith) hupper
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by linarith) (by positivity),
    Real.log_pow, Real.log_exp] at hlog
  have h1 := mul_le_mul_of_nonneg_left hlog hg
  have habs := log_one_add_le hy (L_ge_one P)
  have h2 := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 2*(G P:ℝ))
  have hcancel : 2*(G P:ℝ)*(P.y/L P) = P.y/256 := by
    unfold L
    field_simp [(G_real_pos P).ne']
    ring
  have hw : 2*(G P:ℝ)*P.w*P.y = P.csch*P.y/32 := by
    have he := G_mul_w P
    nlinarith [congrArg (fun x : ℝ => x*P.y) he]
  have hpaid := work_log_payment P hwork
  have hsmallY := mul_le_mul_of_nonneg_right (show P.csch ≤ 1/4 by linarith) hy
  norm_num at h1
  nlinarith

theorem D_power_payment (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hwork : Ywork P ≤ P.y) (d : ℝ) (hd : 1 ≤ d)
    (hupper : d ≤ a P*(1+P.y)^2*Real.exp (2*P.w*P.y)) :
    d^(G P) ≤ Real.exp (P.y/64) := by
  apply (Real.log_le_iff_le_exp (pow_pos (by linarith : 0 < d) _)).mp
  rw [Real.log_pow]
  exact log_D_payment P hc hsmall hC hy hwork d hd hupper

theorem support_exponent (hc : 0 < P.csch) (hC : 1 ≤ P.Csch) :
    ((P.Hs+2:ℕ):ℝ) ≤ 64*(G P:ℝ)*P.t := by
  have hAt := (div_le_iff₀ (P.t_pos hc)).mp (P.H_bounds hc hC).1
  have hu := P.A_ge hC
  have hHt : 2 ≤ (P.H:ℝ)*P.t := by linarith [Nat.cast_nonneg (α := ℝ) P.K]
  have hd : (1:ℝ) ≤ P.D0 := by exact_mod_cast P.D0_pos
  have ht := P.t_pos hc
  have hp := mul_le_mul_of_nonneg_left hHt (show 0 ≤ (P.D0:ℝ) by positivity)
  have he : ((P.Hs+2:ℕ):ℝ) = (P.D0:ℝ)+1 := by simp only [Hs, D0, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]; ring
  rw [he]
  unfold G
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (P.D0:ℝ) by positivity) ht.le]

theorem D_support_payment (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hwork : Ywork P ≤ P.y) (d : ℝ) (hd : 1 ≤ d)
    (hupper : d ≤ a P*(1+P.y)^2*Real.exp (2*P.w*P.y)) :
    d^(P.Hs+2) ≤ P.Ds ∧ d^(P.Hs+1) ≤ P.Ds := by
  have hd0 : 0 < d := by linarith
  have hlog0 := Real.log_nonneg hd
  have hx := mul_le_mul_of_nonneg_right (support_exponent P hc hC) hlog0
  have hp := mul_le_mul_of_nonneg_left (log_D_payment P hc hsmall hC hy hwork d hd hupper)
    (show 0 ≤ 64*P.t by have := P.t_pos hc; positivity)
  have hlog : ((P.Hs+2:ℕ):ℝ)*Real.log d ≤ P.t*P.y := by nlinarith
  have hDs : P.Ds = Real.exp (P.t*P.y) := by
    rw [Ds, Real.rpow_def_of_pos P.delta_pos, delta, Real.log_exp]
    congr 1
    ring
  have hs : d^(P.Hs+2) ≤ P.Ds := by
    rw [hDs]
    apply (Real.log_le_iff_le_exp (pow_pos hd0 _)).mp
    rw [Real.log_pow]
    exact hlog
  exact ⟨hs, (pow_le_pow_right₀ hd (by omega : P.Hs+1 ≤ P.Hs+2)).trans hs⟩

/-- The coefficient multiplication is exact, not a decimal approximation. -/
theorem sqrt_coefficient : 4*Real.sqrt 5*Real.sqrt 1280 = 320 := by
  have h : Real.sqrt 5*Real.sqrt 1280 = (80:ℝ) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤5)]
    norm_num
  nlinarith

theorem a_square_bounds (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch) :
    83203*(P.m:ℝ)^7 ≤ (a P)^2 ∧ 520*(P.m:ℝ)^5 ≤ (a P)^2 := by
  have hm := m_ge_one P hc hsmall hC
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1000*(P.m:ℝ)^4) (a_lower P hc hsmall hC).1 2
  have h8 : 1000000*(P.m:ℝ)^8 ≤ (a P)^2 := by nlinarith [hpow]
  have h7 := pow_le_pow_right₀ hm (by norm_num : 7 ≤ (8:ℕ))
  have h5 := pow_le_pow_right₀ hm (by norm_num : 5 ≤ (8:ℕ))
  constructor <;> nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) P.m) 8]

theorem step_upper (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) : step P ≤ 83203*(P.m:ℝ)^7*(1+P.y) ∧ step P ≤ (a P)^2*(1+P.y) := by
  have hm := m_ge_one P hc hsmall hC
  have ht := P.t_pos hc
  have hty := mul_le_mul_of_nonneg_right (t_le_one P (by linarith : P.csch ≤ 1)) hy
  have h5 : 1 ≤ (P.m:ℝ)^5 := one_le_pow₀ hm
  have hrow : 256*(P.m:ℝ)^5+4 ≤ 260*(P.m:ℝ)^5 := by linarith
  have he : step P = 3+320*(P.m:ℝ)^2*(1+P.t*P.y)*(256*(P.m:ℝ)^5+4) := by
    unfold step RecursiveSize.stepFactor mainFactor rowFactor Bsize
    have h := sqrt_coefficient
    calc
      _ = 3+(4*Real.sqrt 5*Real.sqrt 1280)*(P.m:ℝ)^2*(1+P.t*P.y)*(256*(P.m:ℝ)^5+4) := by ring
      _ = _ := by rw [h]
  have hprod : 1 ≤ (P.m:ℝ)^7*(1+P.y) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hm) (by linarith)
  have hs : step P ≤ 83203*(P.m:ℝ)^7*(1+P.y) := by
    calc
      _ ≤ 3+320*(P.m:ℝ)^2*(1+P.y)*(260*(P.m:ℝ)^5) := by rw [he]; gcongr; linarith
      _ ≤ _ := by nlinarith [hprod]
  exact ⟨hs, hs.trans (mul_le_mul_of_nonneg_right (a_square_bounds P hc hsmall hC).1 (by linarith))⟩

theorem Q_pos (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch) (hy : 0 ≤ P.y) : 0 < Q P := by
  have hm := m_ge_one P hc hsmall hC
  have hs := stepFactor_ge_three P.m P.Bsize (le_trans (by norm_num) (P.Bsize_ge_one hc hsmall hC hy))
  change 3 ≤ step P at hs
  unfold Q
  positivity

theorem Q_upper (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch) (hy : 0 ≤ P.y) :
    Q P ≤ (a P)^(2*G P)*(1+P.y)^(G P) := by
  have ha := (a_lower P hc hsmall hC).2
  have hs0 : 0 ≤ step P := by
    have h := stepFactor_ge_three P.m P.Bsize (le_trans (by norm_num) (P.Bsize_ge_one hc hsmall hC hy))
    change 3 ≤ step P at h
    linarith
  have hp := pow_le_pow_left₀ hs0 (step_upper P hc hsmall hC hy).2 (rho P)
  have hr := rho_add_one_le_G P hc hC
  calc
    _ ≤ (a P)^2*((a P)^2*(1+P.y))^(rho P) :=
      mul_le_mul (a_square_bounds P hc hsmall hC).2 hp (by positivity) (sq_nonneg _)
    _ = (a P)^(2*(rho P+1))*(1+P.y)^(rho P) := by
      rw [mul_pow, ← mul_assoc, ← pow_succ', ← pow_mul]
    _ ≤ _ := mul_le_mul (pow_le_pow_right₀ ha (by omega))
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1+P.y) (by omega)) (by positivity) (by positivity)

theorem Q_log_payment (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hwork : Ywork P ≤ P.y) : 12*Real.log (Q P) ≤ (15/128)*P.y := by
  have ha := (a_lower P hc hsmall hC).2
  have hl := L_ge_one P
  have hloga := Real.log_nonneg ha
  have hlogL := Real.log_nonneg hl
  have hq := Real.log_le_log (Q_pos P hc hsmall hC hy) (Q_upper P hc hsmall hC hy)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hq
  push_cast at hq
  have habs := mul_le_mul_of_nonneg_left (log_one_add_le hy hl) (G_real_pos P).le
  have he : (G P:ℝ)*(P.y/L P) = P.y/512 := by unfold L; field_simp [(G_real_pos P).ne']
  have hp := work_log_payment P hwork
  have hnon := mul_nonneg (G_real_pos P).le hlogL
  nlinarith

theorem resolution_payment (hc : 0 < P.csch) (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hwork : Ywork P ≤ P.y) : P.delta ≤ (Q P)^(-12:ℝ) := by
  rw [delta, Real.rpow_def_of_pos (Q_pos P hc hsmall hC hy)]
  apply Real.exp_le_exp.mpr
  have h := Q_log_payment P hc hsmall hC hy hwork
  nlinarith
end AcceleratedLogConcave.Oracle.ScalarSchedulePayment
