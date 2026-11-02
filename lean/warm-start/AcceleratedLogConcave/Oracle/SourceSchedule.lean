import AcceleratedLogConcave.Oracle.RecursiveExecutable
import AcceleratedLogConcave.Root.RecursiveRadiusFamily
import AcceleratedLogConcave.Oracle.Precision

/-! Literal scalar schedule from warm-start.tex, eq:k3-schedule.
NP is the fixed synchronous source layer count; H is a separate scalar rank
cap. Positivity does not pay shift support, resolution, work, or root data. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle

/-- Only the four independent scalar inputs; every schedule quantity is derived. -/
structure SourceSchedule where
  K : ℕ
  csch : ℝ
  Csch : ℝ
  y : ℝ

namespace SourceSchedule

def A (S : SourceSchedule) : ℝ := S.Csch*((S.K:ℝ)+2)
def t (S : SourceSchedule) : ℝ := S.csch/((S.K:ℝ)+2)
def NP (S : SourceSchedule) : ℕ := RecursiveExecutable.sourceLayers S.Csch S.K
def Hs (S : SourceSchedule) : ℕ := S.NP
def D0 (S : SourceSchedule) : ℕ := S.NP+1
def H (S : SourceSchedule) : ℕ := Nat.ceil (S.A/S.t)
def gammaM : ℝ := 1/64
def T (S : SourceSchedule) : ℝ := (S.D0:ℝ)*((S.H:ℝ)+1)/gammaM
def w (S : SourceSchedule) : ℝ := S.csch/S.T
def m (S : SourceSchedule) : ℕ := Root.RecursiveRadiusFamily.meanOrder S.Csch S.K S.w
def delta (S : SourceSchedule) : ℝ := Real.exp (-S.y)
def R (S : SourceSchedule) : ℝ := S.delta^S.t
def psi (S : SourceSchedule) : ℝ := S.delta^(4*S.t)
def h0 (S : SourceSchedule) : ℝ := S.delta^S.w
def Ds (S : SourceSchedule) : ℝ := S.delta^(-S.t)
def Bsize (S : SourceSchedule) : ℝ := Real.sqrt 1280*(S.m:ℝ)^2*(1+S.t*S.y)

variable (S : SourceSchedule)

@[simp] theorem NP_literal : S.NP = Nat.ceil S.A := rfl
@[simp] theorem Hs_eq_NP : S.Hs = S.NP := rfl
@[simp] theorem m_literal : S.m = Nat.ceil (S.A/S.w) := rfl

theorem A_ge (hC : 1 ≤ S.Csch) : (S.K:ℝ)+2 ≤ S.A := by
  exact le_mul_of_one_le_left (by positivity) hC

theorem A_pos (hC : 1 ≤ S.Csch) : 0 < S.A :=
  (by positivity : (0:ℝ)<(S.K:ℝ)+2).trans_le (S.A_ge hC)

theorem NP_bounds (hC : 1 ≤ S.Csch) : S.A ≤ (S.NP:ℝ) ∧ (S.NP:ℝ) < S.A+1 := by
  rw [NP_literal]
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (S.A_pos hC).le⟩

theorem NP_pos (hC : 1 ≤ S.Csch) : 0 < S.NP := by
  rw [NP_literal]
  exact Nat.ceil_pos.mpr (S.A_pos hC)

theorem D0_pos : 0 < S.D0 := Nat.succ_pos _

theorem t_pos (hc : 0 < S.csch) : 0 < S.t := div_pos hc (by positivity)

theorem t_le (hc : 0 < S.csch) (hsmall : S.csch < 1/160) : S.t ≤ 1/60 := by
  have hk : (2:ℝ) ≤ (S.K:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) S.K]
  unfold t
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(S.K:ℝ)+2)).2
  nlinarith

theorem H_bounds (hc : 0 < S.csch) (hC : 1 ≤ S.Csch) :
    S.A/S.t ≤ (S.H:ℝ) ∧ (S.H:ℝ) < S.A/S.t+1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (div_pos (S.A_pos hC) (S.t_pos hc)).le⟩

theorem H_pos (hc : 0 < S.csch) (hC : 1 ≤ S.Csch) : 0 < S.H :=
  Nat.ceil_pos.mpr (div_pos (S.A_pos hC) (S.t_pos hc))

theorem T_pos : 0 < S.T := by
  unfold T gammaM
  have hd : (0:ℝ) < S.D0 := by exact_mod_cast S.D0_pos
  positivity

theorem T_gt (hC : 1 ≤ S.Csch) : (S.K:ℝ)+2 < S.T := by
  have hn := (S.A_ge hC).trans (S.NP_bounds hC).1
  have hD : (S.K:ℝ)+3 ≤ (S.D0:ℝ) := by
    have he : (S.D0:ℝ) = (S.NP:ℝ)+1 := by simp only [D0, Nat.cast_add, Nat.cast_one]
    linarith
  have hH : 0 ≤ (S.H:ℝ) := Nat.cast_nonneg _
  have hd0 : 0 ≤ (S.D0:ℝ) := Nat.cast_nonneg _
  unfold T gammaM
  nlinarith [mul_nonneg hd0 hH]

theorem w_pos (hc : 0 < S.csch) : 0 < S.w := div_pos hc S.T_pos

theorem w_lt_t (hc : 0 < S.csch) (hC : 1 ≤ S.Csch) : S.w < S.t :=
  div_lt_div_of_pos_left hc (by positivity) (S.T_gt hC)

theorem m_pos (hc : 0 < S.csch) (hC : 1 ≤ S.Csch) : 0 < S.m :=
  Root.RecursiveRadiusFamily.meanOrder_pos (lt_of_lt_of_le zero_lt_one hC) (S.w_pos hc) S.K

theorem m_bounds (hc : 0 < S.csch) (hC : 1 ≤ S.Csch) :
    S.A/S.w ≤ (S.m:ℝ) ∧ (S.m:ℝ) < S.A/S.w+1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (div_pos (S.A_pos hC) (S.w_pos hc)).le⟩

theorem m_ge_two (hc : 0 < S.csch) (hsmall : S.csch < 1/160) (hC : 1 ≤ S.Csch) :
    2 ≤ S.m := by
  have hw := (S.w_lt_t hc hC).trans_le (S.t_le hc hsmall)
  have ha := S.A_ge hC
  have htwo : (2:ℝ) ≤ S.A/S.w := (le_div_iff₀ (S.w_pos hc)).2 (by nlinarith [Nat.cast_nonneg (α := ℝ) S.K])
  have hb := htwo.trans (S.m_bounds hc hC).1
  exact_mod_cast hb

theorem base_budget (hsmall : S.csch < 1/160) : 40*((S.K:ℝ)+2)*S.t < 1/4 := by
  have he : 40*((S.K:ℝ)+2)*S.t = 40*S.csch := by
    unfold t
    field_simp
  rw [he]
  linarith

/-- Exact quarter rank, with natural truncated subtraction also at K=0. -/
theorem quarter_rank : Precision.precisionRank (1/4) (S.K:ℝ) = 4*S.K-2 := by
  unfold Precision.precisionRank
  calc
    _ = Nat.ceil (((4*S.K:ℕ):ℝ)-(2:ℕ)) := congrArg Nat.ceil (by push_cast; ring)
    _ = Nat.ceil ((4*S.K:ℕ):ℝ)-2 := Nat.ceil_sub_natCast _ _
    _ = _ := by rw [Nat.ceil_natCast]

theorem rank_budget (hc : 0 < S.csch) (hsmall : S.csch < 1/160) :
    10*S.t*(Precision.precisionRank (1/4) (S.K:ℝ):ℝ) < 1/4 := by
  have hn : (Precision.precisionRank (1/4) (S.K:ℝ):ℝ) ≤ 4*((S.K:ℝ)+2) := by
    rw [S.quarter_rank]
    exact_mod_cast (show 4*S.K-2 ≤ 4*(S.K+2) by omega)
  have ht := S.t_pos hc
  have hp := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 10*S.t)
  nlinarith [S.base_budget hsmall]

theorem padded_rank_budget (hc : 0 < S.csch) (hsmall : S.csch < 1/160) :
    10*S.t*((Precision.precisionRank (1/4) (S.K:ℝ)+1:ℕ):ℝ) < 1/4 := by
  have hn : ((Precision.precisionRank (1/4) (S.K:ℝ)+1:ℕ):ℝ) ≤ 4*((S.K:ℝ)+2) := by
    rw [S.quarter_rank]
    exact_mod_cast (show 4*S.K-2+1 ≤ 4*(S.K+2) by omega)
  have ht := S.t_pos hc
  have hp := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 10*S.t)
  nlinarith [S.base_budget hsmall]

/-- A scalar rank cap, distinct from the fixed synchronous NP. -/
theorem precision_rank_le_H (hc : 0 < S.csch) (hC : 1 ≤ S.Csch) :
    Precision.precisionRank S.t (S.K:ℝ) ≤ S.H := by
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (S.t_pos hc).le
  linarith [S.A_ge hC]

theorem delta_pos : 0 < S.delta := Real.exp_pos _
theorem delta_le_one (hy : 0 ≤ S.y) : S.delta ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
theorem R_pos : 0 < S.R := Real.rpow_pos_of_pos S.delta_pos _
theorem h0_pos : 0 < S.h0 := Real.rpow_pos_of_pos S.delta_pos _
theorem Ds_pos : 0 < S.Ds := Real.rpow_pos_of_pos S.delta_pos _

theorem psi_eq_R_pow : S.psi = S.R^4 := by
  unfold psi R
  rw [mul_comm (4:ℝ) S.t]
  exact Real.rpow_mul_natCast S.delta_pos.le S.t 4

theorem R_mul_Ds : S.R*S.Ds = 1 := by
  rw [R, Ds, ← Real.rpow_add S.delta_pos]
  simp

theorem abs_log_R (hc : 0 < S.csch) (hy : 0 ≤ S.y) : |Real.log (S.delta^S.t)| = S.t*S.y := by
  rw [Real.log_rpow S.delta_pos, delta, Real.log_exp]
  have hty : 0 ≤ S.t*S.y := mul_nonneg (S.t_pos hc).le hy
  rw [mul_neg, abs_neg, abs_of_nonneg hty]

theorem Bsize_eq_log (hc : 0 < S.csch) (hy : 0 ≤ S.y) :
    S.Bsize = Real.sqrt 1280*(S.m:ℝ)^2*(1+|Real.log (S.delta^S.t)|) := by
  rw [S.abs_log_R hc hy]
  rfl

theorem Bsize_ge_one (hc : 0 < S.csch) (hsmall : S.csch < 1/160) (hC : 1 ≤ S.Csch)
    (hy : 0 ≤ S.y) : 1 ≤ S.Bsize := by
  have hm : (1:ℝ) ≤ S.m := by exact_mod_cast (show 1 ≤ S.m by have := S.m_ge_two hc hsmall hC; omega)
  have hroot : (1:ℝ) ≤ Real.sqrt 1280 := Real.le_sqrt_of_sq_le (by norm_num)
  have hlast : 1 ≤ 1+S.t*S.y := by nlinarith [mul_nonneg (S.t_pos hc).le hy]
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hroot (one_le_pow₀ hm)) hlast

theorem h0_eq_exp : S.h0 = Real.exp (-S.w*S.y) := by
  rw [h0, Real.rpow_def_of_pos S.delta_pos, delta, Real.log_exp]
  congr 1
  ring

/-- This explicit resolution payment is necessary and sufficient for the half-step cap. -/
theorem h0_le_half_iff : S.h0 ≤ 1/2 ↔ Real.log 2 ≤ S.w*S.y := by
  have he : Real.exp (-Real.log 2) = (1:ℝ)/2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [S.h0_eq_exp, ← he, Real.exp_le_exp]
  constructor <;> intro h <;> linarith

theorem R_le_h0 (hc : 0 < S.csch) (hC : 1 ≤ S.Csch) (hy : 0 ≤ S.y) : S.R ≤ S.h0 :=
  Real.rpow_le_rpow_of_exponent_ge S.delta_pos (S.delta_le_one hy) (S.w_lt_t hc hC).le

theorem resolved_half (hc : 0 < S.csch) (hC : 1 ≤ S.Csch) (hy : 0 ≤ S.y)
    (hresolution : Real.log 2 ≤ S.w*S.y) : S.h0 ≤ 1/2 ∧ S.R ≤ 1/2 :=
  ⟨S.h0_le_half_iff.mpr hresolution, (S.R_le_h0 hc hC hy).trans (S.h0_le_half_iff.mpr hresolution)⟩

/-- Csch=1 satisfies its elementary guard but cannot pay the separate support height. -/
theorem Hs_at_one (hC : S.Csch = 1) : S.Hs = S.K+2 := by
  change Nat.ceil (S.Csch*((S.K:ℝ)+2)) = S.K+2
  rw [hC, one_mul]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using Nat.ceil_natCast (R := ℝ) (S.K+2)

theorem support_height_not_paid (hC : S.Csch = 1) : ¬ 8*S.K+4 ≤ S.Hs := by
  rw [S.Hs_at_one hC]
  omega
end SourceSchedule
end AcceleratedLogConcave.Oracle
