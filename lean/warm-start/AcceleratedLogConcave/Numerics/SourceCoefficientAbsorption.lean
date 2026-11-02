import AcceleratedLogConcave.Numerics.SourceScheduleFeasibility
import AcceleratedLogConcave.Numerics.SmoothInventoryGrowth

/-!
# Absorption of the literal scheduled numerical inventory

The threshold below involves only the fixed schedule parameters and the
dimension. In particular, the source order `m K c C` is independent of the
resolution parameter `y`. The dimension-zero case is included.
-/

noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.SourceCoefficientAbsorption

open SourceSchedule SmoothInventoryDimension

def polynomialOrderCap (K : ℕ) (c C : ℝ) : ℝ :=
  1 + 64 * C * ((K : ℝ) + 2) *
    (C * ((K : ℝ) + 2) + 2) *
    (C * (((K : ℝ) + 2) ^ 2) / c + 2) / c

/-- For fixed positive `c` and `C`, the scheduled order is bounded by a
degree-four polynomial in `K+2`. This bound contains no resolution parameter. -/
theorem order_polynomial_cap (K : ℕ) {c C : ℝ}
    (hc : 0 < c) (hC : 1 ≤ C) :
    (m K c C : ℝ) ≤ polynomialOrderCap K c C := by
  let q : ℝ := (K : ℝ) + 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hCq : 0 ≤ C * q := mul_nonneg (by linarith) hq.le
  have ht : t K c = c / q := rfl
  have htpos := t_pos K hc
  have hTpos : 0 < T K c C := lt_of_lt_of_le hq (T_ge_K_add_two K hC)
  have hw : w K c C = c / T K c C := rfl
  have hnp : (nP K C : ℝ) ≤ C * q + 1 := by
    unfold nP
    have h := Nat.ceil_lt_add_one hCq
    dsimp [q] at *
    linarith
  have hd : (d0 K C : ℝ) ≤ C * q + 2 := by
    unfold d0
    push_cast
    linarith
  have hHarg : C * q / t K c = C * q ^ 2 / c := by
    rw [ht]
    field_simp
  have hHarg0 : 0 ≤ C * q / t K c := div_nonneg hCq htpos.le
  have hH : ((H K c C : ℕ) : ℝ) + 1 ≤ C * q ^ 2 / c + 2 := by
    have h : (H K c C : ℝ) < C * q / t K c + 1 := by
      unfold H
      exact Nat.ceil_lt_add_one hHarg0
    rw [hHarg] at h
    linarith
  have hd0 : 0 ≤ (d0 K C : ℝ) := Nat.cast_nonneg _
  have hH0 : 0 ≤ ((H K c C : ℕ) : ℝ) + 1 := by positivity
  have hT : T K c C ≤
      64 * (C * q + 2) * (C * q ^ 2 / c + 2) := by
    unfold T
    have hprod : (d0 K C : ℝ) * ((H K c C : ℕ) + 1 : ℝ) ≤
        (C * q + 2) * (C * q ^ 2 / c + 2) := by
      gcongr
    nlinarith
  have hmarg : C * q / w K c C = C * q * T K c C / c := by
    rw [hw]
    field_simp
  have hmarg0 : 0 ≤ C * q / w K c C :=
    div_nonneg hCq (w_pos K hc hC).le
  have hm : (m K c C : ℝ) ≤ C * q * T K c C / c + 1 := by
    have h : (m K c C : ℝ) < C * q / w K c C + 1 := by
      unfold m
      exact Nat.ceil_lt_add_one hmarg0
    rw [hmarg] at h
    linarith
  have hmul : C * q * T K c C / c ≤
      64 * C * q * (C * q + 2) * (C * q ^ 2 / c + 2) / c := by
    apply (div_le_div_iff_of_pos_right hc).mpr
    nlinarith [mul_nonneg hCq (sub_nonneg.mpr hT)]
  dsimp [q, polynomialOrderCap] at *
  linarith

def orderLogBudget (K : ℕ) (c C : ℝ) : ℝ :=
  10200 * (((m K c C + 3 : ℕ) : ℝ)) *
    Real.log (((m K c C + 3 : ℕ) : ℝ))

def resolutionThreshold (D K : ℕ) (c C : ℝ) : ℝ :=
  2 * (orderLogBudget K c C + Real.log ((D : ℝ) + 1))

/-- An upper bound for the fixed threshold written entirely with the
degree-four polynomial order cap, rather than a scheduled ceiling. -/
theorem resolution_threshold_polynomial_cap (D K : ℕ) {c C : ℝ}
    (hc : 0 < c) (hC : 1 ≤ C) :
    resolutionThreshold D K c C ≤
      2 * (10200 * (polynomialOrderCap K c C + 3) *
        Real.log (polynomialOrderCap K c C + 3) +
        Real.log ((D : ℝ) + 1)) := by
  have hm := order_polynomial_cap K hc hC
  have hm3 : (1 : ℝ) ≤ ((m K c C + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ m K c C + 3 by omega)
  have hcap3 : (1 : ℝ) ≤ polynomialOrderCap K c C + 3 := by
    have hmn : (0 : ℝ) ≤ m K c C := Nat.cast_nonneg _
    linarith
  have hle : (((m K c C + 3 : ℕ) : ℝ)) ≤
      polynomialOrderCap K c C + 3 := by
    push_cast
    linarith
  have hlog : Real.log (((m K c C + 3 : ℕ) : ℝ)) ≤
      Real.log (polynomialOrderCap K c C + 3) :=
    Real.log_le_log (by linarith) hle
  have hlog0 : 0 ≤ Real.log (((m K c C + 3 : ℕ) : ℝ)) :=
    Real.log_nonneg hm3
  have hlogcap0 : 0 ≤ Real.log (polynomialOrderCap K c C + 3) :=
    Real.log_nonneg hcap3
  have hprod : (((m K c C + 3 : ℕ) : ℝ)) *
      Real.log (((m K c C + 3 : ℕ) : ℝ)) ≤
      (polynomialOrderCap K c C + 3) *
        Real.log (polynomialOrderCap K c C + 3) := by
    exact (mul_le_mul_of_nonneg_left hlog (by linarith)).trans
      (mul_le_mul_of_nonneg_right hle hlogcap0)
  unfold resolutionThreshold orderLogBudget
  nlinarith

private theorem sqrt_dimension_le (D : ℕ) :
    Real.sqrt (D : ℝ) ≤ (D : ℝ) + 1 := by
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    nlinarith

/-- A scalar absorption rule, with the logarithmic budget supplied separately. -/
theorem scalar_payment {u B N a y : ℝ}
    (hbound : u ≤ Real.exp B) (hN : 0 < N)
    (hpay : B + Real.log N ≤ a * y)
    {s : ℝ} (hs0 : 0 ≤ s) (hsN : s ≤ N) :
    u * s * δ y ^ a ≤ 1 := by
  have hproduct : u * s ≤ Real.exp B * N := by
    calc
      u * s ≤ Real.exp B * s := mul_le_mul_of_nonneg_right hbound hs0
      _ ≤ Real.exp B * N := mul_le_mul_of_nonneg_left hsN (Real.exp_pos B).le
  have hpositive : 0 < Real.exp B * N := mul_pos (Real.exp_pos B) hN
  have hlog : Real.log (Real.exp B * N) ≤ a * y := by
    rw [Real.log_mul (Real.exp_ne_zero B) hN.ne', Real.log_exp]
    exact hpay
  calc
    u * s * δ y ^ a ≤ (Real.exp B * N) * δ y ^ a :=
      mul_le_mul_of_nonneg_right hproduct (Real.rpow_nonneg (delta_pos y).le _)
    _ ≤ 1 := SourceSchedule.delta_power_payment hpositive hlog

/-- The actual `A(m)` and `√D` are jointly paid by one half-power of the
resolution. The threshold is explicit and has no `y` on its right-hand side. -/
theorem scheduled_inventory_half_payment (D K : ℕ) {c C y : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C)
    (hy : resolutionThreshold D K c C ≤ y) :
    A (m K c C) * Real.sqrt (D : ℝ) * δ y ^ ((1 : ℝ) / 2) ≤ 1 := by
  have hm : 1 ≤ m K c C := by
    exact le_trans (by decide : 1 ≤ 2) (SourceSchedule.m_ge_two K hc hc1 hC)
  have hA : A (m K c C) ≤ Real.exp (orderLogBudget K c C) :=
    (Real.le_exp_log _).trans
      (Real.exp_le_exp.mpr (by
        simpa only [orderLogBudget] using A_log_le (m K c C) hm))
  have hN : 0 < (D : ℝ) + 1 := by positivity
  have hbudget : orderLogBudget K c C + Real.log ((D : ℝ) + 1) ≤
      ((1 : ℝ) / 2) * y := by
    unfold resolutionThreshold at hy
    linarith
  exact scalar_payment hA hN hbudget
    (Real.sqrt_nonneg _) (sqrt_dimension_le D)

/-- Equivalent dimension cap, useful when dimension is chosen after `y`. -/
theorem scheduled_inventory_half_payment_of_dimension_cap (D K : ℕ) {c C y : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C)
    (hcap : (D : ℝ) + 1 ≤ Real.exp (y / 2 - orderLogBudget K c C)) :
    A (m K c C) * Real.sqrt (D : ℝ) * δ y ^ ((1 : ℝ) / 2) ≤ 1 := by
  have hN : 0 < (D : ℝ) + 1 := by positivity
  have hlog := Real.log_le_log hN hcap
  rw [Real.log_exp] at hlog
  apply scheduled_inventory_half_payment D K hc hc1 hC
  unfold resolutionThreshold
  linarith

/-- The numerical inventory contribution in the scheduled convergence
coefficient has one additional half-power of resolution available. -/
theorem scheduled_quadrature_payment (D K : ℕ) {c C y ell r : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C)
    (hell : 0 ≤ ell) (hr : 0 ≤ r)
    (hy : resolutionThreshold D K c C ≤ y) :
    (4 * ell * r * Real.sqrt (D : ℝ) * A (m K c C)) *
      δ y ^ (2 * (K : ℝ) + 20) ≤
      (4 * ell * r) * δ y ^ (2 * (K : ℝ) + 39 / 2) := by
  have hpay := scheduled_inventory_half_payment D K hc hc1 hC hy
  have hδ : 0 ≤ δ y ^ (2 * (K : ℝ) + 39 / 2) :=
    Real.rpow_nonneg (delta_pos y).le _
  rw [show (2 * (K : ℝ) + 20 : ℝ) = 1 / 2 + (2 * (K : ℝ) + 39 / 2) by ring,
    Real.rpow_add (delta_pos y)]
  nlinarith [mul_nonneg (show 0 ≤ 4 * ell * r by positivity)
    (mul_nonneg (sub_nonneg.mpr hpay) hδ)]

end AcceleratedLogConcave.Numerics.SourceCoefficientAbsorption
