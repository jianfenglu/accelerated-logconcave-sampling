import AcceleratedLogConcave.Oracle.RecursiveReachableSize
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Scalar feasibility of the source compiler schedule

This is the literal schedule of `sources/warm-start.tex`, equation
`eq:k3-schedule`, with `γ_M = 1/64`. Theorems below pay the explicit
affine-row resolution test used by `RecursiveCall.Path.scalar_smallness`.
The other source payments (quadrature, derivative envelopes and work counts)
are separate.
-/

noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.SourceSchedule

def t (K : ℕ) (c : ℝ) : ℝ := c / (K + 2)
def nP (K : ℕ) (C : ℝ) : ℕ := Nat.ceil (C * (K + 2))
def d0 (K : ℕ) (C : ℝ) : ℕ := nP K C + 1
def H (K : ℕ) (c C : ℝ) : ℕ := Nat.ceil (C * (K + 2) / t K c)
def Hs (K : ℕ) (C : ℝ) : ℕ := Nat.ceil (C * (K + 2))
def T (K : ℕ) (c C : ℝ) : ℝ := (d0 K C : ℝ) * (H K c C + 1) * 64
def w (K : ℕ) (c C : ℝ) : ℝ := c / T K c C
def m (K : ℕ) (c C : ℝ) : ℕ := Nat.ceil (C * (K + 2) / w K c C)
def δ (y : ℝ) : ℝ := Real.exp (-y)
def R (K : ℕ) (c y : ℝ) : ℝ := δ y ^ t K c
def psi (K : ℕ) (c y : ℝ) : ℝ := δ y ^ (4 * t K c)
def h₀ (K : ℕ) (c C y : ℝ) : ℝ := δ y ^ w K c C

theorem t_pos (K : ℕ) {c : ℝ} (hc : 0 < c) : 0 < t K c := by
  unfold t
  positivity

theorem H_pos (K : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 1 ≤ C) :
    0 < H K c C := by
  unfold H
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (by linarith) (by positivity)) (t_pos K hc)

theorem d0_ge_two (K : ℕ) {C : ℝ} (hC : 1 ≤ C) : 2 ≤ d0 K C := by
  have hceil : (1 : ℝ) ≤ (nP K C : ℝ) := by
    exact (show (1 : ℝ) ≤ C * (K + 2) by nlinarith).trans (Nat.le_ceil _)
  have hn : 1 ≤ nP K C := by exact_mod_cast hceil
  unfold d0
  omega

theorem T_ge_K_add_two (K : ℕ) {c C : ℝ} (hC : 1 ≤ C) :
    (K : ℝ) + 2 ≤ T K c C := by
  have hceil : (K : ℝ) + 2 ≤ (nP K C : ℝ) := by
    exact (show (K : ℝ) + 2 ≤ C * (K + 2) by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (Nat.cast_nonneg K)]).trans
      (Nat.le_ceil _)
  have hd : (K : ℝ) + 2 ≤ (d0 K C : ℝ) := by
    unfold d0
    push_cast
    linarith
  have hd0 : 0 ≤ (d0 K C : ℝ) := Nat.cast_nonneg _
  have hH : 1 ≤ ((H K c C : ℕ) + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  unfold T
  nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hH)]

theorem w_pos (K : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 1 ≤ C) :
    0 < w K c C := by
  unfold w
  exact div_pos hc (lt_of_lt_of_le (by positivity : (0 : ℝ) < (K : ℝ) + 2)
    (T_ge_K_add_two K hC))

theorem w_le_t (K : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 1 ≤ C) :
    w K c C ≤ t K c := by
  unfold w t
  exact div_le_div_of_nonneg_left hc.le (by positivity) (T_ge_K_add_two K hC)

theorem t_le_sixtieth (K : ℕ) {c : ℝ} (hc : 0 ≤ c) (hc60 : c ≤ 1 / 60) :
    t K c ≤ 1 / 60 := by
  unfold t
  have hk : (2 : ℝ) ≤ (K : ℝ) + 2 := by exact_mod_cast Nat.le_add_left 2 K
  have ht := div_le_self hc (by linarith : 1 ≤ (K : ℝ) + 2)
  linarith

theorem m_ge_two (K : ℕ) {c C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hC : 1 ≤ C) : 2 ≤ m K c C := by
  have hw := w_le_t K hc hC
  have hwp := w_pos K hc hC
  have htc : t K c ≤ c := by
    unfold t
    exact div_le_self hc.le (by have := (Nat.cast_nonneg K : 0 ≤ (K : ℝ)); linarith)
  have hnum : (2 : ℝ) ≤ C * (K + 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (Nat.cast_nonneg K)]
  have harg : (2 : ℝ) ≤ C * (K + 2) / w K c C := by
    apply (le_div_iff₀ hwp).mpr
    nlinarith
  have hceil : (2 : ℝ) ≤ (m K c C : ℝ) :=
    harg.trans (Nat.le_ceil _)
  exact_mod_cast hceil

theorem delta_pos (y : ℝ) : 0 < δ y := Real.exp_pos _

theorem delta_le_one {y : ℝ} (hy : 0 ≤ y) : δ y ≤ 1 := by
  simpa only [δ, ← Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : -y ≤ 0)

/-- The explicit logarithmic payment is exactly the affine row test. -/
theorem delta_le_resolution {y A : ℝ} (hA : 0 < A)
    (hy : 12 * Real.log A ≤ y) : δ y ≤ A ^ (-12 : ℝ) := by
  unfold δ
  rw [Real.rpow_def_of_pos hA]
  exact Real.exp_le_exp.mpr (by ring_nf at hy ⊢; linarith)

theorem delta_power_payment {y A a : ℝ} (hA : 0 < A)
    (hpay : Real.log A ≤ a * y) : A * δ y ^ a ≤ 1 := by
  rw [Real.rpow_def_of_pos (delta_pos y)]
  simp only [δ, Real.log_exp]
  have he : A * Real.exp (-y * a) = Real.exp (Real.log A - a * y) := by
    rw [Real.exp_sub, Real.exp_log hA,
      show -y * a = -(a * y) by ring, Real.exp_neg, div_eq_mul_inv]
  rw [he, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The source's compiler test for its literal tier majorant `S`. -/
theorem compiler_scalar_test (K : ℕ) {c C y B₀ Cstar : ℝ}
    (hc : 0 < c) (hC : 1 ≤ C) (hB₀ : 0 < B₀) (hCstar : 0 < Cstar)
    (hpay : 4 * Real.log
      (Cstar * (H K c C : ℝ) * B₀ * (32 * B₀) ^ (H K c C + 2)) ≤ y) :
    Cstar * (H K c C : ℝ) * B₀ * (32 * B₀) ^ (H K c C + 2) *
      δ y ^ ((1 : ℝ) / 4) ≤ 1 := by
  have hH : (0 : ℝ) < H K c C := by exact_mod_cast H_pos K hc hC
  have hA : 0 < Cstar * (H K c C : ℝ) * B₀ *
      (32 * B₀) ^ (H K c C + 2) := by positivity
  exact delta_power_payment hA (by nlinarith [hpay])

theorem delta_rpow (y a : ℝ) : δ y ^ a = Real.exp (-y * a) := by
  rw [Real.rpow_def_of_pos (delta_pos y)]
  simp only [δ, Real.log_exp]

/-- Both real geometric scales are powers of the same resolution. -/
theorem geometric_caps (K : ℕ) {c C y : ℝ}
    (hR : Real.log 2 ≤ y * t K c)
    (hh : Real.log 2 ≤ y * w K c C) :
    R K c y ≤ 1 / 2 ∧ h₀ K c C y ≤ 1 / 2 := by
  have hhalf : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  constructor
  · unfold R
    rw [delta_rpow, ← hhalf]
    exact Real.exp_le_exp.mpr (by linarith)
  · unfold h₀
    rw [delta_rpow, ← hhalf]
    exact Real.exp_le_exp.mpr (by linarith)

/-- Conditions on the actual backward geometric mesh and angular interval. -/
theorem mesh_scales (K : ℕ) {c C y : ℝ}
    (hc : 0 < c) (hC : 1 ≤ C) (hy : 0 ≤ y)
    (hR : Real.log 2 ≤ y * t K c)
    (hh : Real.log 2 ≤ y * w K c C) :
    0 < R K c y ∧ R K c y ≤ 1 / 2 ∧
    0 < psi K c y ∧ psi K c y ≤ 1 ∧
    0 < h₀ K c C y ∧ h₀ K c C y ≤ 1 / 2 := by
  have hcaps := geometric_caps K hR hh
  have hδ := delta_pos y
  have hδ1 := delta_le_one hy
  have ht := t_pos K hc
  have hw := w_pos K hc hC
  refine ⟨?_, hcaps.1, ?_, ?_, ?_, hcaps.2⟩
  · exact Real.rpow_pos_of_pos hδ _
  · exact Real.rpow_pos_of_pos hδ _
  · exact Real.rpow_le_one hδ.le hδ1 (by positivity)
  · exact Real.rpow_pos_of_pos hδ _

/-- The source schedule pays the actual mean-row envelope once the root size
bound and the logarithmic scalar payment have been verified. -/
theorem mean_row_small (K : ℕ) {c C y S L r σ : ℝ}
    (hc : 0 < c) (hc60 : c ≤ 1 / 60) (hC : 1 ≤ C)
    (hy : 0 ≤ y) (hS : 1 ≤ S) (hσ : 0 < σ)
    (hsizeR : L * r ^ 2 ≤ S * δ y ^ (1 / 2 : ℝ))
    (hsizeS : L * r / σ ≤ S * δ y ^ (1 / 2 : ℝ))
    (hpay : 12 * Real.log (520 * (m K c C : ℝ) ^ 5 * S) ≤ y) :
    2 * L * (256 * (m K c C : ℝ) ^ 5 * r /
      (σ * psi K c y * h₀ K c C y) + 4 * r ^ 2) ≤
      δ y ^ ((1 : ℝ) / 3) := by
  have hm := m_ge_two K hc (le_trans hc60 (by norm_num)) hC
  have hA : 0 < 520 * (m K c C : ℝ) ^ 5 * S := by
    have : (0 : ℝ) < (m K c C : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    positivity
  simpa only [psi, h₀] using
    AffineGraph.affine_mean_envelope_le_rpow_third hm (delta_pos y)
      (delta_le_one hy) (w_pos K hc hC).le (w_le_t K hc hC)
      (t_le_sixtieth K hc.le hc60) (by norm_num : (1 : ℝ) / 2 ≤ 1 / 2)
      hS hσ hsizeR hsizeS (delta_le_resolution hA hpay)

/-- A public root precision no larger than `K+2` pays the expensive-child
rank charge in the source schedule. -/
theorem cost_rank_paid (K : ℕ) {c q : ℝ} (hc : 0 < c)
    (hc80 : c ≤ 1 / 80) (hq : q ≤ (K : ℝ) + 2) :
    10 * t K c * (Oracle.Precision.precisionRank (1 / 4) q : ℝ) ≤ 1 / 2 := by
  have hrank : Oracle.Precision.precisionRank (1 / 4) q ≤ 4 * (K + 2) := by
    unfold Oracle.Precision.precisionRank
    apply Nat.ceil_le.mpr
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    norm_num
    nlinarith
  have hrankR : (Oracle.Precision.precisionRank (1 / 4) q : ℝ) ≤
      4 * ((K : ℝ) + 2) := by exact_mod_cast hrank
  have ht : 0 < t K c := t_pos K hc
  have hbound : t K c * ((K : ℝ) + 2) = c := by
    unfold t
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hrankR ht.le
  calc
    _ ≤ 10 * (t K c * (4 * ((K : ℝ) + 2))) := by
      convert mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 10) using 1; ring
    _ = 40 * c := by rw [show t K c * (4 * ((K : ℝ) + 2)) =
        4 * (t K c * ((K : ℝ) + 2)) by ring, hbound]; ring
    _ ≤ 1 / 2 := by linarith

/-- The literal simultaneous-layer count pays the first raw numerical defect. -/
theorem layer_defect_exponent (K : ℕ) {C : ℝ} (hC : 30 ≤ C) :
    2 * (K : ℝ) + 20 ≤ (nP K C : ℝ) / 3 := by
  have hlo : C * ((K : ℝ) + 2) ≤ (nP K C : ℝ) := Nat.le_ceil _
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ (K : ℝ) + 2)
  nlinarith

/-- The prescribed height dominates every root precision at most `K+2`. -/
theorem rank_le_height (K : ℕ) {c C q : ℝ}
    (hc : 0 < c) (hC : 1 ≤ C) (hq : q ≤ (K : ℝ) + 2) :
    Oracle.Precision.precisionRank (t K c) q ≤ H K c C := by
  unfold Oracle.Precision.precisionRank H
  apply Nat.ceil_mono
  have ht := t_pos K hc
  apply (div_le_div_iff_of_pos_right ht).mpr
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr hC) (by linarith : 0 ≤ (K : ℝ) + 2)]

/-- The actual ceiling `m=⌈C(K+2)/w⌉` pays the geometric-mesh defect
after the `m-1` loss and the four powers of `R`. -/
theorem mesh_defect_exponent (K : ℕ) {c C : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 30 ≤ C) :
    2 * (K : ℝ) + 20 ≤
      w K c C * ((m K c C : ℝ) - 1) - 4 * t K c := by
  have hC1 : 1 ≤ C := by linarith
  have hw := w_pos K hc hC1
  have hwt := w_le_t K hc hC1
  have htc : t K c ≤ c := by
    unfold t
    exact div_le_self hc.le (by have := (Nat.cast_nonneg K : 0 ≤ (K : ℝ)); linarith)
  have hmlo : C * ((K : ℝ) + 2) / w K c C ≤ (m K c C : ℝ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hmlo hw.le
  have hnum : C * ((K : ℝ) + 2) ≤ (m K c C : ℝ) * w K c C := by
    convert hmul using 1 <;> field_simp [hw.ne']
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hCmul := mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ (K : ℝ) + 2)
  nlinarith

/-- A deliberately explicit fixed-order threshold absorbs the slow
`log(1+y)` growth of any polynomial scalar majorant. -/
theorem log_one_add_payment {A y : ℝ} (hA : 0 ≤ A)
    (hy1 : 1 ≤ y) (hyA : 32 * A ^ 2 ≤ y) :
    A * Real.log (1 + y) ≤ y / 2 := by
  have hu : 0 ≤ 1 + y := by linarith
  have hsqrt := Real.sqrt_nonneg (1 + y)
  have hsquare := Real.sq_sqrt hu
  have hlog := Real.log_le_self hsqrt
  rw [Real.log_sqrt hu] at hlog
  have hmult := mul_nonneg (sub_nonneg.mpr hyA) (by linarith : 0 ≤ y)
  have hsq : (4 * A * Real.sqrt (1 + y)) ^ 2 ≤ y ^ 2 := by
    nlinarith [sq_nonneg A]
  have hroot : 4 * A * Real.sqrt (1 + y) ≤ y := by
    nlinarith [sq_nonneg (4 * A * Real.sqrt (1 + y) + y)]
  have hlogmul := mul_le_mul_of_nonneg_left hlog hA
  nlinarith

/-- Concrete resolution threshold for the manuscript's tier majorant
`S=(32 B₀)^(H+2)` when its coefficient `B₀` is bounded by a polynomial
in `1+y`. The threshold depends only on the already fixed order, height
and polynomial coefficients, never on an oracle answer. -/
theorem tier_resolution_of_polynomial
    (m Hn p : ℕ) {B₀ Bpoly y : ℝ}
    (hm : 2 ≤ m) (hB₀ : 0 < B₀) (hBpoly : 1 ≤ Bpoly)
    (hBbound : B₀ ≤ Bpoly * (1 + y) ^ p)
    (hy1 : 1 ≤ y)
    (hyquad : 32 * (12 * ((Hn : ℝ) + 2) * (p : ℝ)) ^ 2 ≤ y)
    (hyconst : 2 * (12 * (Real.log 520 + 5 * Real.log (m : ℝ) +
      ((Hn : ℝ) + 2) * (Real.log 32 + Real.log Bpoly))) ≤ y) :
    12 * Real.log (520 * (m : ℝ) ^ 5 * (32 * B₀) ^ (Hn + 2)) ≤ y := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hBpolypos : 0 < Bpoly := by linarith
  have hypos : 0 < 1 + y := by linarith
  have hlogB : Real.log B₀ ≤ Real.log Bpoly +
      (p : ℝ) * Real.log (1 + y) := by
    calc
      Real.log B₀ ≤ Real.log (Bpoly * (1 + y) ^ p) :=
        Real.log_le_log hB₀ hBbound
      _ = _ := by rw [Real.log_mul hBpolypos.ne' (pow_ne_zero _ hypos.ne'), Real.log_pow]
  have hH : 0 ≤ (Hn : ℝ) + 2 := by positivity
  have hlogtarget : Real.log (520 * (m : ℝ) ^ 5 * (32 * B₀) ^ (Hn + 2)) ≤
      Real.log 520 + 5 * Real.log (m : ℝ) +
      ((Hn : ℝ) + 2) * (Real.log 32 + Real.log Bpoly) +
      ((Hn : ℝ) + 2) * (p : ℝ) * Real.log (1 + y) := by
    rw [Real.log_mul (mul_ne_zero (by norm_num : (520 : ℝ) ≠ 0)
      (pow_ne_zero _ hmpos.ne')) (pow_ne_zero _ (mul_pos (by norm_num) hB₀).ne'),
      Real.log_mul (by norm_num : (520 : ℝ) ≠ 0) (pow_ne_zero _ hmpos.ne'),
      Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hB₀.ne']
    have hh := mul_le_mul_of_nonneg_left hlogB hH
    push_cast at hh ⊢
    nlinarith
  have hA : 0 ≤ 12 * ((Hn : ℝ) + 2) * (p : ℝ) := by positivity
  have hpay := log_one_add_payment hA hy1 hyquad
  nlinarith [hlogtarget]

/-- Any recursive tier whose factor is covered by `32 B₀` inherits the
computed resolution threshold for the literal `S` majorant. -/
theorem recursive_tier_resolution
    (m Hn p rank : ℕ) {D B₀ Bpoly y : ℝ}
    (hm : 2 ≤ m) (hD : 0 < D) (hB₀ : 1 ≤ B₀) (hBpoly : 1 ≤ Bpoly)
    (hDcap : D ≤ 32 * B₀) (hrank : rank ≤ Hn)
    (hBbound : B₀ ≤ Bpoly * (1 + y) ^ p)
    (hy1 : 1 ≤ y)
    (hyquad : 32 * (12 * ((Hn : ℝ) + 2) * (p : ℝ)) ^ 2 ≤ y)
    (hyconst : 2 * (12 * (Real.log 520 + 5 * Real.log (m : ℝ) +
      ((Hn : ℝ) + 2) * (Real.log 32 + Real.log Bpoly))) ≤ y) :
    12 * Real.log (520 * (m : ℝ) ^ 5 * D ^ rank) ≤ y := by
  have hbase : 1 ≤ 32 * B₀ := by
    nlinarith
  have hpow : D ^ rank ≤ (32 * B₀) ^ (Hn + 2) := by
    calc
      D ^ rank ≤ (32 * B₀) ^ rank := by gcongr
      _ ≤ (32 * B₀) ^ (Hn + 2) :=
        pow_le_pow_right₀ hbase (by omega)
  have hfactor : 0 < 520 * (m : ℝ) ^ 5 := by
    have : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    positivity
  have htarget : 0 < 520 * (m : ℝ) ^ 5 * D ^ rank := by positivity
  have hlog := Real.log_le_log htarget (mul_le_mul_of_nonneg_left hpow hfactor.le)
  have htier := tier_resolution_of_polynomial m Hn p hm (by linarith) hBpoly
    hBbound hy1 hyquad hyconst
  nlinarith

end AcceleratedLogConcave.Numerics.SourceSchedule

namespace AcceleratedLogConcave.Oracle.RecursiveCall
open AcceleratedLogConcave.Numerics.SourceSchedule RecursiveSize Precision

/-- The source schedule discharges order, exponent gap, cost rank and scalar
resolution for every actual recursive occurrence. The root size certificate,
inventory estimates and descendant width bound are the independent compiler
premises from which `Path.scalar_smallness` propagates sizes. -/
theorem Path.source_schedule_scalar_smallness
    {m n ns K d j : ℕ} {Csrc : Source m n ns} {p₀ p : State}
    (hp : Path Csrc p₀ p d j) (L B c Csch y : ℝ)
    (hroot : SizeBound L Csrc.δ 1 1 p₀.radius p₀.width)
    (hc : 0 < c) (hc80 : c ≤ 1 / 80) (hCsch : 1 ≤ Csch)
    (hy : 0 ≤ y) (hm : m = AcceleratedLogConcave.Numerics.SourceSchedule.m K c Csch)
    (hδ : Csrc.δ = AcceleratedLogConcave.Numerics.SourceSchedule.δ y)
    (ht : Csrc.t = AcceleratedLogConcave.Numerics.SourceSchedule.t K c)
    (hw : Csrc.w = AcceleratedLogConcave.Numerics.SourceSchedule.w K c Csch)
    (hR : Csrc.M.R = AcceleratedLogConcave.Numerics.SourceSchedule.R K c y)
    (hq : p₀.precision ≤ (K : ℝ) + 2)
    (hL : 0 ≤ L) (hr : 0 < p₀.radius) (hσ : 0 < p₀.width)
    (hDs : 0 < Csrc.Ds) (hDsBound : Csrc.Ds ≤ Csrc.δ ^ (-Csrc.t))
    (hB : 1 ≤ B)
    (hn : Real.sqrt n ≤ B * Csrc.δ ^ (-Csrc.w))
    (hns : Real.sqrt ns ≤ B * Csrc.δ ^ (-Csrc.w))
    (hpay : 12 * Real.log
      (520 * (m : ℝ) ^ 5 * (stepFactor m B) ^
        (precisionRank Csrc.t p₀.precision)) ≤ y) :
    2 * L * SourceMeanExecutable.rowBound (m := m)
      p.radius p.width Csrc.δ Csrc.t Csrc.w ≤ Csrc.δ ^ ((1 : ℝ) / 3) ∧
    2 * L * p.radius ^ 2 ≤ Csrc.δ ^ ((1 : ℝ) / 3) := by
  have hm2 : 2 ≤ m := by rw [hm]; exact AcceleratedLogConcave.Numerics.SourceSchedule.m_ge_two K hc (by linarith) hCsch
  have hδpos : 0 < Csrc.δ := by rw [hδ]; exact AcceleratedLogConcave.Numerics.SourceSchedule.delta_pos y
  have hδ1 : Csrc.δ ≤ 1 := by rw [hδ]; exact AcceleratedLogConcave.Numerics.SourceSchedule.delta_le_one hy
  have htpos : 0 < Csrc.t := by rw [ht]; exact AcceleratedLogConcave.Numerics.SourceSchedule.t_pos K hc
  have ht60 : Csrc.t ≤ 1 / 60 := by
    rw [ht]
    exact AcceleratedLogConcave.Numerics.SourceSchedule.t_le_sixtieth K hc.le (by linarith)
  have hwpos : 0 ≤ Csrc.w := by
    rw [hw]
    exact (AcceleratedLogConcave.Numerics.SourceSchedule.w_pos K hc hCsch).le
  have hwt : Csrc.w ≤ Csrc.t := by
    rw [hw, ht]
    exact AcceleratedLogConcave.Numerics.SourceSchedule.w_le_t K hc hCsch
  have hcost : 10 * Csrc.t * (precisionRank (1 / 4) p₀.precision : ℝ) ≤ 1 / 2 := by
    rw [ht]
    exact AcceleratedLogConcave.Numerics.SourceSchedule.cost_rank_paid K hc hc80 hq
  have hR' : Csrc.M.R = Csrc.δ ^ Csrc.t := by
    simpa only [hδ, ht, AcceleratedLogConcave.Numerics.SourceSchedule.R] using hR
  have hstep : 1 ≤ stepFactor m B :=
    (by norm_num : (1 : ℝ) ≤ 3).trans (stepFactor_ge_three m B (by linarith))
  have hA : 0 < 520 * (m : ℝ) ^ 5 *
      (stepFactor m B) ^ (precisionRank Csrc.t p₀.precision) := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm2)
    positivity
  have hres : Csrc.δ ≤
      (520 * (m : ℝ) ^ 5 * (stepFactor m B) ^
        (precisionRank Csrc.t p₀.precision)) ^ (-12 : ℝ) := by
    rw [hδ]
    exact AcceleratedLogConcave.Numerics.SourceSchedule.delta_le_resolution hA hpay
  exact hp.scalar_smallness L B hroot hm2 hL hr hσ hDs hδpos hδ1
    htpos ht60 hwpos hwt hB hR' hDsBound hn hns hcost hres

/-- Fully computed polynomial-tier version of the actual occurrence-path
scalar estimate. The premise on `B₀` states the source's coefficient-polynomial
choice, while the two displayed lower bounds on `y` are explicit and do not
assume the desired row or resolution inequality. -/
theorem Path.source_schedule_scalar_smallness_polynomial
    {m n ns K d j p : ℕ} {Csrc : Source m n ns} {p₀ child : State}
    (hp : Path Csrc p₀ child d j) (L B c Csch y B₀ Bpoly : ℝ)
    (hroot : SizeBound L Csrc.δ 1 1 p₀.radius p₀.width)
    (hc : 0 < c) (hc80 : c ≤ 1 / 80) (hCsch : 1 ≤ Csch)
    (hm : m = AcceleratedLogConcave.Numerics.SourceSchedule.m K c Csch)
    (hδ : Csrc.δ = AcceleratedLogConcave.Numerics.SourceSchedule.δ y)
    (ht : Csrc.t = AcceleratedLogConcave.Numerics.SourceSchedule.t K c)
    (hw : Csrc.w = AcceleratedLogConcave.Numerics.SourceSchedule.w K c Csch)
    (hR : Csrc.M.R = AcceleratedLogConcave.Numerics.SourceSchedule.R K c y)
    (hq : p₀.precision ≤ (K : ℝ) + 2)
    (hL : 0 ≤ L) (hr : 0 < p₀.radius) (hσ : 0 < p₀.width)
    (hDs : 0 < Csrc.Ds) (hDsBound : Csrc.Ds ≤ Csrc.δ ^ (-Csrc.t))
    (hB : 1 ≤ B)
    (hn : Real.sqrt n ≤ B * Csrc.δ ^ (-Csrc.w))
    (hns : Real.sqrt ns ≤ B * Csrc.δ ^ (-Csrc.w))
    (hB₀ : 1 ≤ B₀) (hBpoly : 1 ≤ Bpoly)
    (hDcap : stepFactor m B ≤ 32 * B₀)
    (hBbound : B₀ ≤ Bpoly * (1 + y) ^ p)
    (hy1 : 1 ≤ y)
    (hyquad : 32 * (12 *
      ((AcceleratedLogConcave.Numerics.SourceSchedule.H K c Csch : ℝ) + 2) *
      (p : ℝ)) ^ 2 ≤ y)
    (hyconst : 2 * (12 * (Real.log 520 + 5 * Real.log (m : ℝ) +
      ((AcceleratedLogConcave.Numerics.SourceSchedule.H K c Csch : ℝ) + 2) *
      (Real.log 32 + Real.log Bpoly))) ≤ y) :
    2 * L * SourceMeanExecutable.rowBound (m := m)
      child.radius child.width Csrc.δ Csrc.t Csrc.w ≤ Csrc.δ ^ ((1 : ℝ) / 3) ∧
    2 * L * child.radius ^ 2 ≤ Csrc.δ ^ ((1 : ℝ) / 3) := by
  have hm2 : 2 ≤ m := by
    rw [hm]
    exact AcceleratedLogConcave.Numerics.SourceSchedule.m_ge_two K hc (by linarith) hCsch
  have hrank : precisionRank Csrc.t p₀.precision ≤
      AcceleratedLogConcave.Numerics.SourceSchedule.H K c Csch := by
    rw [ht]
    exact AcceleratedLogConcave.Numerics.SourceSchedule.rank_le_height K hc hCsch hq
  have hD : 0 < stepFactor m B := by
    have hstep := stepFactor_ge_three m B (by linarith)
    linarith
  have hpay := AcceleratedLogConcave.Numerics.SourceSchedule.recursive_tier_resolution
    m (AcceleratedLogConcave.Numerics.SourceSchedule.H K c Csch) p
    (precisionRank Csrc.t p₀.precision) hm2 hD hB₀ hBpoly
    hDcap hrank hBbound hy1 hyquad hyconst
  exact hp.source_schedule_scalar_smallness L B c Csch y hroot hc hc80
    hCsch (by linarith) hm hδ ht hw hR hq hL hr hσ hDs hDsBound hB hn hns hpay

end AcceleratedLogConcave.Oracle.RecursiveCall
