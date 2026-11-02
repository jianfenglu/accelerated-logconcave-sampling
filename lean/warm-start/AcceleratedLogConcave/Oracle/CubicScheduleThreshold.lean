import AcceleratedLogConcave.Oracle.ScalarSchedulePaymentBounds

/-! Explicit coefficients for the cubic-log threshold. Each coefficient takes
only the two fixed schedule constants. This converts the bounded scalar
payments, not all analytic or every-execution work obligations. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.CubicScheduleThreshold
open SourceSchedule SchedulePolynomialBounds ScalarSchedulePayment

def g0 (c C : ℝ) : ℝ := 4*C^2/c
def m0 (c C : ℝ) : ℝ := 257*C^3/c^2
def A0 (c C : ℝ) : ℝ := 768300*C*(m0 c C)^4
def Cwork (c C : ℝ) : ℝ :=
  512*g0 c C*(2*Real.log (A0 c C)+4*Real.log (512*g0 c C)+23)
def Cgeom (c C : ℝ) : ℝ := 256*g0 c C*Real.log 2/c
def C1 (c C : ℝ) : ℝ := 1+Cwork c C+Cgeom c C

def threshold (P : SourceSchedule) : ℝ :=
  C1 P.csch P.Csch*(P.K:ℝ)^3*Real.log (u P)

variable {c C : ℝ}

theorem g0_ge_one (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C) : 1 ≤ g0 c C := by
  have hC2 := one_le_pow₀ hC (n := 2)
  apply (le_div_iff₀ hc).2
  nlinarith

theorem m0_ge_one (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C) : 1 ≤ m0 c C := by
  have hC3 := one_le_pow₀ hC (n := 3)
  apply (le_div_iff₀ (sq_pos_of_pos hc)).2
  nlinarith

theorem A0_ge_one (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C) : 1 ≤ A0 c C := by
  exact one_le_mul_of_one_le_of_one_le
    (by nlinarith : 1 ≤ 768300*C) (one_le_pow₀ (m0_ge_one hc hc1 hC))

theorem coefficients_nonneg (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C) :
    0 ≤ Cwork c C ∧ 0 ≤ Cgeom c C ∧ 1 ≤ C1 c C := by
  have hg := g0_ge_one hc hc1 hC
  have hA := Real.log_nonneg (A0_ge_one hc hc1 hC)
  have hL := Real.log_nonneg (show 1 ≤ 512*g0 c C by linarith)
  have h2 := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  have hw : 0 ≤ Cwork c C := by unfold Cwork; positivity
  have hh : 0 ≤ Cgeom c C := by unfold Cgeom; positivity
  exact ⟨hw, hh, by unfold C1; linarith⟩

variable (P : SourceSchedule)

theorem log_u_ge_half : (1/2:ℝ) ≤ Real.log (u P) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hm := Real.log_le_log (by norm_num : (0:ℝ)<2) (u_ge_two P)
  norm_num at h
  linarith

theorem u_cube_le (hK : 10 ≤ P.K) : (u P)^3 ≤ 2*(P.K:ℝ)^3 := by
  have hk : (10:ℝ) ≤ P.K := by exact_mod_cast hK
  have hu : u P ≤ (6/5:ℝ)*(P.K:ℝ) := by unfold u; linarith
  calc
    _ ≤ ((6/5:ℝ)*(P.K:ℝ))^3 := pow_le_pow_left₀ (u_pos P).le hu 3
    _ ≤ _ := by nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) P.K) 3]

theorem G_upper (hc : 0 < P.csch) (hc1 : P.csch ≤ 1) (hC : 1 ≤ P.Csch) :
    (G P:ℝ) ≤ g0 P.csch P.Csch*(u P)^3 := by
  have ht := T_upper P hc hc1 hC
  rw [T_eq P] at ht
  calc
    _ ≤ (256*P.Csch^2*(u P)^3/P.csch)/64 :=
      (le_div_iff₀ (by norm_num : (0:ℝ)<64)).2 (by linarith)
    _ = _ := by unfold g0; ring

theorem m_upper_scaled (hc : 0 < P.csch) (hc1 : P.csch ≤ 1) (hC : 1 ≤ P.Csch) :
    (P.m:ℝ) ≤ m0 P.csch P.Csch*(u P)^4 := by
  simpa only [m0, div_mul_eq_mul_div] using m_upper P hc hc1 hC

theorem a_upper (hc : 0 < P.csch) (hc1 : P.csch ≤ 1) (hC : 1 ≤ P.Csch) :
    a P ≤ A0 P.csch P.Csch*(u P)^17 := by
  have hu := u_ge_two P
  have hC0 : 0 ≤ P.Csch := by linarith
  have hCu : 2 ≤ P.Csch*u P := le_trans hu (le_mul_of_one_le_left (u_pos P).le hC)
  have hn : (P.NP:ℝ)+2 ≤ 3*P.Csch*u P := by have := NP_upper P hC; linarith
  have hm := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) P.m) (m_upper_scaled P hc hc1 hC) 4
  calc
    _ ≤ 256100*(3*P.Csch*u P)*(m0 P.csch P.Csch*(u P)^4)^4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) hm (by positivity) (by positivity)
    _ = _ := by unfold A0; ring

theorem log_a_upper (hc : 0 < P.csch) (hc1 : P.csch ≤ 1) (hC : 1 ≤ P.Csch) :
    Real.log (a P) ≤ Real.log (A0 P.csch P.Csch)+17*Real.log (u P) := by
  have hm : (0:ℝ) < P.m := by exact_mod_cast P.m_pos hc hC
  have ha : 0 < a P := by unfold a; positivity
  have hA : 0 < A0 P.csch P.Csch := lt_of_lt_of_le (by norm_num) (A0_ge_one hc hc1 hC)
  have h := Real.log_le_log ha (a_upper P hc hc1 hC)
  rw [Real.log_mul hA.ne' (pow_ne_zero _ (u_pos P).ne'), Real.log_pow] at h
  norm_num at h
  exact h

theorem log_L_upper (hc : 0 < P.csch) (hc1 : P.csch ≤ 1) (hC : 1 ≤ P.Csch) :
    Real.log (L P) ≤ Real.log (512*g0 P.csch P.Csch)+3*Real.log (u P) := by
  have hg := g0_ge_one hc hc1 hC
  have hL : 0 < L P := lt_of_lt_of_le (by norm_num) (L_ge_one P)
  have h := Real.log_le_log hL (mul_le_mul_of_nonneg_left (G_upper P hc hc1 hC) (by norm_num : (0:ℝ)≤512))
  change Real.log (L P) ≤ Real.log (512*(g0 P.csch P.Csch*(u P)^3)) at h
  rw [← mul_assoc, Real.log_mul (by positivity) (pow_ne_zero _ (u_pos P).ne'), Real.log_pow] at h
  norm_num at h
  exact h

theorem Ywork_cubic (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hc1 : P.csch ≤ 1) (hC : 1 ≤ P.Csch) :
    Ywork P ≤ Cwork P.csch P.Csch*(P.K:ℝ)^3*Real.log (u P) := by
  let V := 2*Real.log (A0 P.csch P.Csch)+4*Real.log (512*g0 P.csch P.Csch)+23
  have hg := g0_ge_one hc hc1 hC
  have hA := Real.log_nonneg (A0_ge_one hc hc1 hC)
  have hL := Real.log_nonneg (show 1 ≤ 512*g0 P.csch P.Csch by linarith)
  have hu := log_u_ge_half P
  have hv : 0 ≤ V := by dsimp [V]; positivity
  have hα := mul_le_mul_of_nonneg_left hu hA
  have hβ := mul_le_mul_of_nonneg_left hu hL
  have hs : Real.log (a P)+2*Real.log (L P) ≤ V*Real.log (u P) := by
    dsimp [V]
    nlinarith [log_a_upper P hc hc1 hC, log_L_upper P hc hc1 hC]
  calc
    _ ≤ 256*(G P:ℝ)*(V*Real.log (u P)) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ 256*(g0 P.csch P.Csch*(u P)^3)*(V*Real.log (u P)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (G_upper P hc hc1 hC) (by norm_num)) (by positivity)
    _ = (256*g0 P.csch P.Csch*V*Real.log (u P))*(u P)^3 := by ring
    _ ≤ (256*g0 P.csch P.Csch*V*Real.log (u P))*(2*(P.K:ℝ)^3) :=
      mul_le_mul_of_nonneg_left (u_cube_le P hK) (by positivity)
    _ = _ := by unfold Cwork; dsimp [V]; ring

theorem Ygeom_cubic (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hc1 : P.csch ≤ 1) (hC : 1 ≤ P.Csch) :
    Ygeom P ≤ Cgeom P.csch P.Csch*(P.K:ℝ)^3*Real.log (u P) := by
  have h2 := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  have hg := g0_ge_one hc hc1 hC
  have hp := mul_le_mul_of_nonneg_left (log_u_ge_half P)
    (by positivity : 0 ≤ (256*g0 P.csch P.Csch*Real.log 2/P.csch)*(P.K:ℝ)^3)
  calc
    _ = Real.log 2*(1/P.w) := by unfold Ygeom; ring
    _ ≤ Real.log 2*(256*P.Csch^2*(u P)^3/P.csch^2) :=
      mul_le_mul_of_nonneg_left (inv_w_upper P hc hc1 hC) h2
    _ = (64*g0 P.csch P.Csch*Real.log 2/P.csch)*(u P)^3 := by unfold g0; ring
    _ ≤ (64*g0 P.csch P.Csch*Real.log 2/P.csch)*(2*(P.K:ℝ)^3) :=
      mul_le_mul_of_nonneg_left (u_cube_le P hK) (by positivity)
    _ = (256*g0 P.csch P.Csch*Real.log 2/P.csch)*(P.K:ℝ)^3*(1/2) := by ring
    _ ≤ _ := by simpa only [Cgeom] using hp

theorem threshold_pays (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hc1 : P.csch ≤ 1) (hC : 1 ≤ P.Csch)
    (hy : threshold P ≤ P.y) : 0 ≤ P.y ∧ Ywork P ≤ P.y ∧ Ygeom P ≤ P.y := by
  have hh := coefficients_nonneg hc hc1 hC
  have hb : 0 ≤ (P.K:ℝ)^3*Real.log (u P) := by have := log_u_ge_half P; positivity
  have hw : Cwork P.csch P.Csch ≤ C1 P.csch P.Csch := by unfold C1; linarith
  have hg : Cgeom P.csch P.Csch ≤ C1 P.csch P.Csch := by unfold C1; linarith
  have hwp := mul_le_mul_of_nonneg_right hw hb
  have hgp := mul_le_mul_of_nonneg_right hg hb
  have hpos : 0 ≤ threshold P := by unfold threshold; have := hh.2.2; have := log_u_ge_half P; positivity
  refine ⟨hpos.trans hy, ?_, ?_⟩
  · have := Ywork_cubic P hK hc hc1 hC
    unfold threshold at hy
    nlinarith
  · have := Ygeom_cubic P hK hc hc1 hC
    unfold threshold at hy
    nlinarith
end AcceleratedLogConcave.Oracle.CubicScheduleThreshold
