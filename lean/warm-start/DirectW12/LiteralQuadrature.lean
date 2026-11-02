import AcceleratedLogConcave.Root.ClockSchedule

/-!

-/
noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockSchedule

/-- No division by the clock: zero clock and positive fixed inventory are allowed. -/
theorem source_sum_weight_sq_le {h : ℝ} (hh : 0 < h) (K : ℕ) (R : Clock) :
    (∑ i, (weight (sourceCells h) (sourceOrder K) R i)^2) ≤ (R : ℝ)^2 := by
  classical
  let w := weight (sourceCells h) (sourceOrder K) R
  have hw (i) : 0 ≤ w i := weight_nonneg _ _ _ _
  have hsum : ∑ i, w i = (R : ℝ) := sum_weight _ _ (sourceCells_pos hh) (sourceOrder_pos K) R
  have hi (i) : w i ≤ (R : ℝ) := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  calc
    _ ≤ ∑ i, w i * (R : ℝ) := Finset.sum_le_sum fun i _ => by
      simpa [pow_two] using mul_le_mul_of_nonneg_left (hi i) (hw i)
    _ = (R : ℝ)^2 := by rw [← Finset.sum_mul, hsum]; ring

/-- Literal coefficient in the exact-reference covariance integral. -/
theorem source_quadrature_C1 {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    (K : ℕ) (R : Clock) :
    2*h^4 * (∑ i, (weight (sourceCells h) (sourceOrder K) R i)^2 *
      (1-(node (sourceCells h) (sourceOrder K) (sourceCells_pos hh) R i : ℝ)^2) *
      (1 + Real.sqrt (2*h^2) * ((R : ℝ) -
        (node (sourceCells h) (sourceOrder K) (sourceCells_pos hh) R i : ℝ)) +
        (2*h^2) * ((R : ℝ)^2 -
          (node (sourceCells h) (sourceOrder K) (sourceCells_pos hh) R i : ℝ)^2)/2)^2)
      ≤ (25/32 : ℝ) * (2*h^2)^2 := by
  classical
  let w := weight (sourceCells h) (sourceOrder K) R
  let u := node (sourceCells h) (sourceOrder K) (sourceCells_pos hh) R
  let ell := Real.sqrt (2*h^2)
  have hA : 0 ≤ 2*h^2 := by positivity
  have hAhalf : 2*h^2 ≤ 1/2 := by nlinarith
  have he0 : 0 ≤ ell := Real.sqrt_nonneg _
  have he1 : ell ≤ 1 := by
    dsimp [ell]
    exact (Real.sqrt_le_one).mpr (by linarith)
  have hb (i) : (1-(u i : ℝ)^2) *
      (1+ell*((R : ℝ)-(u i : ℝ))+(2*h^2)*((R : ℝ)^2-(u i : ℝ)^2)/2)^2 ≤ 25/4 := by
    have hu := nodeValue_mem (sourceCells h) (sourceOrder K) (sourceCells_pos hh) R i
    change 0 ≤ (u i : ℝ) ∧ (u i : ℝ) ≤ (R : ℝ) at hu
    have hR0 := R.property.1
    have hR1 := R.property.2
    have hd0 : 0 ≤ (R : ℝ)^2-(u i : ℝ)^2 := by nlinarith
    have hd1 : (R : ℝ)^2-(u i : ℝ)^2 ≤ 1 := by nlinarith [sq_nonneg (u i : ℝ)]
    have hl : ell*((R : ℝ)-(u i : ℝ)) ≤ 1 :=
      (mul_le_mul he1 (by linarith : (R : ℝ)-(u i : ℝ) ≤ 1)
        (by linarith) zero_le_one).trans (by norm_num)
    have ha : (2*h^2)*((R : ℝ)^2-(u i : ℝ)^2)/2 ≤ 1/2 := by
      have := mul_le_mul hAhalf hd1 hd0 (by norm_num : (0:ℝ) ≤ 1/2)
      nlinarith
    have hc0 : 0 ≤ 1+ell*((R : ℝ)-(u i : ℝ))+
        (2*h^2)*((R : ℝ)^2-(u i : ℝ)^2)/2 :=
      add_nonneg (add_nonneg zero_le_one (mul_nonneg he0 (sub_nonneg.mpr hu.2)))
        (div_nonneg (mul_nonneg hA hd0) (by norm_num))
    have hc1 : 1+ell*((R : ℝ)-(u i : ℝ))+
        (2*h^2)*((R : ℝ)^2-(u i : ℝ)^2)/2 ≤ 5/2 := by linarith
    have hs : (1+ell*((R : ℝ)-(u i : ℝ))+
        (2*h^2)*((R : ℝ)^2-(u i : ℝ)^2)/2)^2 ≤ 25/4 := by nlinarith
    exact (mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [sq_nonneg (u i : ℝ)])).trans hs
  have hs := source_sum_weight_sq_le (hh := hh) (K := K) (R := R)
  have hs' : (∑ i, w i^2) ≤ 1/4 := by
    change (∑ i, w i^2) ≤ (R : ℝ)^2 at hs
    nlinarith [R.property.1, R.property.2]
  have hsum : (∑ i, w i^2 * (1-(u i : ℝ)^2) *
      (1+ell*((R : ℝ)-(u i : ℝ))+(2*h^2)*((R : ℝ)^2-(u i : ℝ)^2)/2)^2) ≤ 25/16 := by
    calc
      _ ≤ ∑ i, w i^2 * (25/4) := Finset.sum_le_sum fun i _ => by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hb i) (sq_nonneg (w i))
      _ = (∑ i, w i^2) * (25/4) := (Finset.sum_mul ..).symm
      _ ≤ 25/16 := by nlinarith
  change 2*h^4 * (∑ i, w i^2 * (1-(u i : ℝ)^2) *
      (1+ell*((R : ℝ)-(u i : ℝ))+(2*h^2)*((R : ℝ)^2-(u i : ℝ)^2)/2)^2) ≤ _
  calc
    _ ≤ 2*h^4*(25/16) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring
end AcceleratedLogConcave.Root.ClockSchedule
