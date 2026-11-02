/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic


/-!
# Constructed Gauss-Legendre quadrature and scalar rows

The order `n` is the number of nodes. The nodes are the increasing enumeration
of the actual roots of Mathlib's shifted Legendre polynomial, whose convention
is `Q_n(x) = P_n(1 - 2*x)`. We construct the cardinals and their integral weights,
then prove exactness for degree `< 2*n` and positivity of the weights.

The row estimates formalize the scalar value-quadrature assertions at
`sources/warm-start.tex:2131-2143`. Partial rows use signed interval integration
and only local AE hypotheses on their kernels. The derivative estimate holds
on the closed interpolation cell. Physical derivative rows scale by `1/h` for
`h > 0`. Order zero is the empty rule; mass one requires positive order.
-/


/- Base -/
section
open Polynomial

namespace AcceleratedLogConcave.Numerics.GaussLegendre

noncomputable def legendre (n : ℕ) : Polynomial ℝ :=
  (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)

@[simp] theorem degree_legendre (n : ℕ) : (legendre n).degree = n := by
  rw [legendre, Polynomial.degree_map_eq_of_injective Int.cast_injective]
  exact Polynomial.degree_shiftedLegendre n

@[simp] theorem natDegree_legendre (n : ℕ) : (legendre n).natDegree = n :=
  Polynomial.natDegree_eq_of_degree_eq_some (degree_legendre n)

theorem legendre_ne_zero (n : ℕ) : legendre n ≠ 0 := by
  intro h
  have := degree_legendre n
  simp [h] at this

@[simp] theorem legendre_eval_zero (n : ℕ) : (legendre n).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simp [legendre, Polynomial.coeff_shiftedLegendre]

@[simp] theorem legendre_eval_one (n : ℕ) : (legendre n).eval 1 = (-1 : ℝ)^n := by
  have h := Polynomial.shiftedLegendre_eval_symm n (1 : ℝ)
  have he (x : ℝ) : Polynomial.aeval x (Polynomial.shiftedLegendre n) =
      (legendre n).eval x := by
    simp only [Polynomial.aeval_def, legendre, Polynomial.eval_map]
    rfl
  rw [he, he] at h
  simpa using h

theorem factorial_mul_legendre_eq (n : ℕ) :
    (n.factorial : Polynomial ℝ) * legendre n =
      Polynomial.derivative^[n] (Polynomial.X ^ n * (1 - Polynomial.X) ^ n) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ))
    (Polynomial.factorial_mul_shiftedLegendre_eq n)
  simpa [legendre, ← Polynomial.iterate_derivative_map] using h

@[simp] theorem legendre_zero : legendre 0 = 1 := by
  simpa using factorial_mul_legendre_eq 0

@[simp] theorem legendre_one : legendre 1 = 1 - 2 * Polynomial.X := by
  have h := factorial_mul_legendre_eq 1
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, Function.iterate_one,
    pow_one, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_sub, Polynomial.derivative_one] at h
  rw [h]
  ring

end AcceleratedLogConcave.Numerics.GaussLegendre

end


/- Beta -/
section
/-!
Elementary Bernstein moments on the unit interval. The proof uses only the
polynomial derivative recurrence and the fundamental theorem of calculus.
-/

noncomputable section

open MeasureTheory

namespace AcceleratedLogConcave.Numerics.GaussLegendre

private theorem integral_eval_derivative (p : Polynomial ℝ) :
    (∫ x : ℝ in 0..1, p.derivative.eval x) = p.eval 1 - p.eval 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => p.hasDerivAt x) (p.derivative.continuous.intervalIntegrable 0 1)

/-- Every Bernstein basis polynomial of degree `n` has integral `1 / (n + 1)`. -/
theorem integral_bernsteinPolynomial (n k : ℕ) (hk : k ≤ n) :
    (∫ x : ℝ in 0..1, (bernsteinPolynomial ℝ n k).eval x) = 1 / (n + 1 : ℝ) := by
  induction k with
  | zero =>
      have h := integral_eval_derivative (bernsteinPolynomial ℝ (n + 1) 0)
      simp only [bernsteinPolynomial.derivative_zero, Nat.add_sub_cancel,
        Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_natCast,
        intervalIntegral.integral_const_mul, bernsteinPolynomial.eval_at_1,
        bernsteinPolynomial.eval_at_0] at h
      simp only [Ne.symm (Nat.succ_ne_zero n), ↓reduceIte,
        zero_sub, Nat.cast_add, Nat.cast_one] at h
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      apply (eq_div_iff hn).2
      nlinarith
  | succ k ih =>
      have hk' : k < n := by omega
      have h := integral_eval_derivative (bernsteinPolynomial ℝ (n + 1) (k + 1))
      simp only [bernsteinPolynomial.derivative_succ_aux, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_natCast, Polynomial.eval_one,
        Polynomial.eval_sub, intervalIntegral.integral_const_mul] at h
      rw [intervalIntegral.integral_sub
        ((bernsteinPolynomial ℝ n k).continuous.intervalIntegrable 0 1)
        ((bernsteinPolynomial ℝ n (k + 1)).continuous.intervalIntegrable 0 1)] at h
      simp only [bernsteinPolynomial.eval_at_1, bernsteinPolynomial.eval_at_0,
        show k + 1 ≠ n + 1 by omega, Nat.succ_ne_zero, ↓reduceIte, sub_self] at h
      have hn : (0 : ℝ) < n + 1 := by positivity
      rw [ih (by omega)] at h
      nlinarith

/-- The symmetric beta moment with its central binomial factor. -/
theorem integral_choose_mul_pow_mul_one_sub_pow (n : ℕ) :
    (∫ x : ℝ in 0..1, ((2 * n).choose n : ℝ) * x ^ n * (1 - x) ^ n) =
      1 / (2 * n + 1 : ℝ) := by
  simpa [bernsteinPolynomial, show 2 * n - n = n by omega] using
    integral_bernsteinPolynomial (2 * n) n (by omega)

/-- The integral of a beta monomial, for all natural exponents including zero. -/
theorem integral_pow_mul_one_sub_pow (a b : ℕ) :
    (∫ x : ℝ in 0..1, x ^ a * (1 - x) ^ b) =
      (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ) := by
  have h := integral_bernsteinPolynomial (a + b) a (by omega)
  simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
    Nat.add_sub_cancel_left, Nat.cast_add] at h
  simp only [mul_assoc, intervalIntegral.integral_const_mul] at h
  have hc : ((a + b).choose a : ℝ) * a.factorial * b.factorial = (a + b).factorial := by
    exact_mod_cast (by simpa using
      Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega))
  have hd : ((a + b + 1).factorial : ℝ) ≠ 0 := by positivity
  have hab : (a + b + 1 : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hd).2
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_one, ← hc]
  calc
    (∫ x : ℝ in 0..1, x ^ a * (1 - x) ^ b) *
        ((a + b + 1) * (((a + b).choose a : ℝ) * a.factorial * b.factorial)) =
        ((a + b + 1) * (((a + b).choose a : ℝ) *
          (∫ x : ℝ in 0..1, x ^ a * (1 - x) ^ b))) *
            (a.factorial * b.factorial) := by ring
    _ = (a.factorial : ℝ) * b.factorial := by rw [h]; field_simp

/-- Symmetric beta moment in factorial form. -/
theorem integral_pow_mul_one_sub_pow_self (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n * (1 - x) ^ n) =
      (n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ) := by
  simpa [two_mul, pow_two] using integral_pow_mul_one_sub_pow n n

end AcceleratedLogConcave.Numerics.GaussLegendre
end

end


/- Orthogonality -/
section
noncomputable section
open Polynomial MeasureTheory
open scoped Interval

namespace AcceleratedLogConcave.Numerics.GaussLegendre

/-- Polynomial integration by parts when the differentiated factor vanishes at both endpoints. -/
theorem integral_derivative_mul_eq_neg (q p : Polynomial ℝ)
    (h0 : q.eval 0 = 0) (h1 : q.eval 1 = 0) :
    (∫ x in (0 : ℝ)..1, q.derivative.eval x * p.eval x) =
      -(∫ x in (0 : ℝ)..1, q.eval x * p.derivative.eval x) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    p.continuous.continuousOn q.continuous.continuousOn
    (fun x _ => p.hasDerivAt x) (fun x _ => q.hasDerivAt x)
    (p.derivative.continuous.intervalIntegrable 0 1)
    (q.derivative.continuous.intervalIntegrable 0 1)
  simpa only [h0, h1, mul_zero, zero_mul, sub_zero, zero_sub, mul_comm] using h

/-- Repeated integration by parts, with all boundary terms stated explicitly. -/
theorem integral_iterate_derivative_mul (q p : Polynomial ℝ) (n : ℕ)
    (h0 : ∀ k < n, (derivative^[k] q).eval 0 = 0)
    (h1 : ∀ k < n, (derivative^[k] q).eval 1 = 0) :
    (∫ x in (0 : ℝ)..1, (derivative^[n] q).eval x * p.eval x) =
      (-1 : ℝ)^n * ∫ x in (0 : ℝ)..1, q.eval x * (derivative^[n] p).eval x := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [integral_derivative_mul_eq_neg _ _ (h0 n (by omega)) (h1 n (by omega))]
      rw [ih p.derivative (fun k hk => h0 k (by omega)) (fun k hk => h1 k (by omega))]
      rw [Function.iterate_succ_apply]
      rw [pow_succ]
      ring

/-- The Rodrigues polynomial has the required vanishing derivatives at zero. -/
theorem rodrigues_iterate_derivative_eval_zero (n k : ℕ) (hk : k < n) :
    (derivative^[k] ((X : Polynomial ℝ)^n * (1-X)^n)).eval 0 = 0 := by
  have hd : (X : Polynomial ℝ)^(n-k) ∣
      derivative^[k] ((X : Polynomial ℝ)^n * (1-X)^n) :=
    pow_sub_dvd_iterate_derivative_of_pow_dvd k (dvd_mul_right _ _)
  obtain ⟨s, hs⟩ := hd
  rw [hs, eval_mul, eval_pow, eval_X, zero_pow (by omega : n-k ≠ 0), zero_mul]

/-- The Rodrigues polynomial has the required vanishing derivatives at one. -/
theorem rodrigues_iterate_derivative_eval_one (n k : ℕ) (hk : k < n) :
    (derivative^[k] ((X : Polynomial ℝ)^n * (1-X)^n)).eval 1 = 0 := by
  have hd : (1-X : Polynomial ℝ)^(n-k) ∣
      derivative^[k] ((X : Polynomial ℝ)^n * (1-X)^n) :=
    pow_sub_dvd_iterate_derivative_of_pow_dvd k (dvd_mul_left _ _)
  obtain ⟨s, hs⟩ := hd
  rw [hs, eval_mul, eval_pow, eval_sub, eval_one, eval_X, sub_self,
    zero_pow (by omega : n-k ≠ 0), zero_mul]


/-- Rodrigues orthogonality against every polynomial of degree below the order. -/
theorem integral_legendre_mul_eq_zero (n : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < n) :
    (∫ x in (0 : ℝ)..1, (legendre n).eval x * p.eval x) = 0 := by
  have h := integral_iterate_derivative_mul ((X : Polynomial ℝ)^n * (1-X)^n) p n
    (rodrigues_iterate_derivative_eval_zero n) (rodrigues_iterate_derivative_eval_one n)
  rw [← factorial_mul_legendre_eq, iterate_derivative_eq_zero_of_degree_lt hp] at h
  simp only [eval_mul, eval_natCast, eval_zero, mul_zero, intervalIntegral.integral_zero,
    mul_assoc, intervalIntegral.integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)

/-- The highest nonzero derivative, with the shifted Legendre sign convention. -/
theorem iterate_derivative_legendre_self (n : ℕ) :
    derivative^[n] (legendre n) =
      C ((n.factorial : ℝ) * (-1 : ℝ)^n * ((2*n).choose n : ℝ)) := by
  have hd : (derivative^[n] (legendre n)).natDegree ≤ 0 := by
    simpa using natDegree_iterate_derivative (legendre n) n
  rw [eq_C_of_natDegree_le_zero hd]
  congr 1
  rw [coeff_iterate_derivative]
  simp [legendre, coeff_shiftedLegendre, nsmul_eq_mul, ← two_mul, mul_assoc, Nat.descFactorial_self]

/-- Exact squared norm on the unweighted unit interval. -/
theorem integral_legendre_sq (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ((legendre n).eval x)^2) = 1 / (2*n+1 : ℝ) := by
  have h := integral_iterate_derivative_mul ((X : Polynomial ℝ)^n * (1-X)^n)
    (legendre n) n (rodrigues_iterate_derivative_eval_zero n)
    (rodrigues_iterate_derivative_eval_one n)
  rw [← factorial_mul_legendre_eq, iterate_derivative_legendre_self] at h
  simp only [eval_mul, eval_natCast, eval_C, eval_pow, eval_X, eval_sub, eval_one,
    mul_assoc, intervalIntegral.integral_const_mul] at h
  simp_rw [← mul_assoc, intervalIntegral.integral_mul_const] at h
  have hs : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
    rw [← mul_pow]
    norm_num
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hb := integral_choose_mul_pow_mul_one_sub_pow n
  simp only [mul_assoc, intervalIntegral.integral_const_mul] at hb
  apply mul_left_cancel₀ hf
  calc
    (n.factorial : ℝ) * (∫ x in (0 : ℝ)..1, ((legendre n).eval x)^2) =
        (-1 : ℝ)^n * ((∫ x in (0 : ℝ)..1, x^n * (1-x)^n) *
          ((n.factorial : ℝ) * ((-1 : ℝ)^n * ((2*n).choose n : ℝ)))) := by
      simpa only [pow_two, mul_assoc] using h
    _ = (n.factorial : ℝ) * (((2*n).choose n : ℝ) *
        (∫ x in (0 : ℝ)..1, x^n * (1-x)^n)) := by
      calc
        _ = ((-1 : ℝ)^n * (-1 : ℝ)^n) * ((n.factorial : ℝ) *
          (((2*n).choose n : ℝ) * (∫ x in (0 : ℝ)..1, x^n * (1-x)^n))) := by ring
        _ = _ := by rw [hs, one_mul]
    _ = _ := by rw [hb]

/-- Distinct orders are orthogonal, independent of their ordering. -/
theorem integral_legendre_mul_legendre (n k : ℕ) (hkn : k ≠ n) :
    (∫ x in (0 : ℝ)..1, (legendre n).eval x * (legendre k).eval x) = 0 := by
  rcases lt_or_gt_of_ne hkn with h | h
  · exact integral_legendre_mul_eq_zero n (legendre k) (by simpa)
  · simpa only [mul_comm] using
      integral_legendre_mul_eq_zero k (legendre n) (by simpa)

end AcceleratedLogConcave.Numerics.GaussLegendre
end

end


/- Roots -/
section
/-!
Interior roots for shifted Legendre polynomials by Rodrigues and repeated Rolle.
-/

noncomputable section

open Polynomial

namespace AcceleratedLogConcave.Numerics.GaussLegendre

private def interiorRoots (p : ℝ[X]) : Finset ℝ :=
  p.roots.toFinset.filter (fun x ↦ 0 < x ∧ x < 1)

private theorem mem_interiorRoots {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ} :
    x ∈ interiorRoots p ↔ p.eval x = 0 ∧ 0 < x ∧ x < 1 := by
  classical
  simp [interiorRoots, Polynomial.mem_roots hp, Polynomial.IsRoot.def]

private theorem card_interiorRoots_succ (p : ℝ[X]) (hp : p ≠ 0)
    (hpd : p.derivative ≠ 0) (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 0) :
    (interiorRoots p).card + 1 ≤ (interiorRoots p.derivative).card := by
  classical
  let s := insert (0 : ℝ) (insert 1 (interiorRoots p))
  have hs : ∀ x ∈ s, 0 ≤ x ∧ x ≤ 1 ∧ p.eval x = 0 := by
    intro x hx
    simp only [s, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨le_rfl, zero_le_one, h0⟩
    · exact ⟨zero_le_one, le_rfl, h1⟩
    · obtain ⟨hr, hx0, hx1⟩ := (mem_interiorRoots hp).mp hx
      exact ⟨hx0.le, hx1.le, hr⟩
  have hcount : s.card ≤ (interiorRoots p.derivative).card + 1 := by
    apply Finset.card_le_of_interleaved
    intro a ha b hb hab _
    obtain ⟨c, hc, hcr⟩ := exists_hasDerivAt_eq_zero hab p.continuous.continuousOn
      ((hs a ha).2.2.trans (hs b hb).2.2.symm)
      (fun x _ ↦ p.hasDerivAt x)
    exact ⟨c, (mem_interiorRoots hpd).mpr
      ⟨hcr, (hs a ha).1.trans_lt hc.1, hc.2.trans_le (hs b hb).2.1⟩, hc⟩
  have hz : (0 : ℝ) ∉ interiorRoots p := by simp [interiorRoots]
  have ho : (1 : ℝ) ∉ interiorRoots p := by simp [interiorRoots]
  have hzi : (0 : ℝ) ∉ insert 1 (interiorRoots p) := by simp [hz]
  dsimp [s] at hcount
  rw [Finset.card_insert_of_notMem hzi, Finset.card_insert_of_notMem ho] at hcount
  omega

private theorem card_interiorRoots_iterate_derivative (p : ℝ[X]) (n : ℕ)
    (hnonzero : (Polynomial.derivative^[n] p) ≠ 0)
    (hendpoints : ∀ k < n,
      (Polynomial.derivative^[k] p).eval 0 = 0 ∧
      (Polynomial.derivative^[k] p).eval 1 = 0) :
    n ≤ (interiorRoots (Polynomial.derivative^[n] p)).card := by
  have hne (k : ℕ) (hk : k ≤ n) : Polynomial.derivative^[k] p ≠ 0 := by
    intro hkzero
    apply hnonzero
    rw [← Nat.sub_add_cancel hk, Function.iterate_add_apply, hkzero,
      Polynomial.iterate_derivative_zero]
  have hcard (k : ℕ) (hk : k ≤ n) :
      k ≤ (interiorRoots (Polynomial.derivative^[k] p)).card := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hkn : k < n := by omega
      have hstep := card_interiorRoots_succ (Polynomial.derivative^[k] p)
        (hne k hkn.le) (by simpa [Function.iterate_succ_apply'] using hne (k + 1) hk)
        (hendpoints k hkn).1 (hendpoints k hkn).2
      have hprev := ih hkn.le
      simpa [Function.iterate_succ_apply'] using (Nat.add_le_add_right hprev 1).trans hstep
  exact hcard n le_rfl

private theorem rodriguesSeed_endpoints (n k : ℕ) (hk : k < n) :
    (Polynomial.derivative^[k] ((X : ℝ[X]) ^ n * (1 - X) ^ n)).eval 0 = 0 ∧
    (Polynomial.derivative^[k] ((X : ℝ[X]) ^ n * (1 - X) ^ n)).eval 1 = 0 := by
  have hrepr : bernsteinPolynomial ℝ (n + n) n =
      ((n + n).choose n : ℝ[X]) * ((X : ℝ[X]) ^ n * (1 - X) ^ n) := by
    simp [bernsteinPolynomial, mul_assoc]
  have hc : (((n + n).choose n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show n ≤ n + n by omega)).ne'
  have h0 := bernsteinPolynomial.iterate_derivative_at_0_eq_zero_of_lt ℝ (n + n) hk
  have h1 := bernsteinPolynomial.iterate_derivative_at_1_eq_zero_of_lt ℝ (n + n)
    (ν := n) (k := k) (by omega)
  rw [hrepr, Polynomial.iterate_derivative_natCast_mul, eval_mul, eval_natCast] at h0 h1
  exact ⟨(mul_eq_zero.mp h0).resolve_left hc, (mul_eq_zero.mp h1).resolve_left hc⟩

private theorem legendre_interiorRoots_card_lower (n : ℕ) :
    n ≤ (interiorRoots (legendre n)).card := by
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnonzero : Polynomial.derivative^[n] ((X : ℝ[X]) ^ n * (1 - X) ^ n) ≠ 0 := by
    rw [← factorial_mul_legendre_eq]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) (legendre_ne_zero n)
  have hroots : (Polynomial.derivative^[n] ((X : ℝ[X]) ^ n * (1 - X) ^ n)).roots =
      (legendre n).roots := by
    rw [← factorial_mul_legendre_eq]
    simpa only [map_natCast] using Polynomial.roots_C_mul (legendre n) hf
  have hcard := card_interiorRoots_iterate_derivative
    ((X : ℝ[X]) ^ n * (1 - X) ^ n) n hnonzero (rodriguesSeed_endpoints n)
  simpa only [interiorRoots, hroots] using hcard

private theorem roots_legendre_eq_interiorRoots (n : ℕ) :
    (legendre n).roots = (interiorRoots (legendre n)).val := by
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    exact ((mem_interiorRoots (legendre_ne_zero n)).mp hx).1
  · simpa only [natDegree_legendre] using legendre_interiorRoots_card_lower n
  · exact legendre_ne_zero n

/-- Shifted Legendre roots are all simple, including the empty order-zero case. -/
theorem roots_legendre_nodup (n : ℕ) : (legendre n).roots.Nodup := by
  rw [roots_legendre_eq_interiorRoots]
  exact Finset.nodup _

/-- There are exactly `n` real roots of the order-`n` shifted Legendre polynomial. -/
theorem card_roots_legendre (n : ℕ) : (legendre n).roots.card = n := by
  apply le_antisymm
  · simpa only [natDegree_legendre] using (legendre n).card_roots'
  · rw [roots_legendre_eq_interiorRoots]
    exact legendre_interiorRoots_card_lower n

/-- Every real shifted Legendre root lies strictly inside the unit interval. -/
theorem mem_roots_legendre_Ioo {n : ℕ} {x : ℝ} (hx : x ∈ (legendre n).roots) :
    x ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [roots_legendre_eq_interiorRoots] at hx
  exact ((mem_interiorRoots (legendre_ne_zero n)).mp hx).2

/-- Every shifted Legendre root has multiplicity one. -/
theorem rootMultiplicity_legendre {n : ℕ} {x : ℝ} (hx : x ∈ (legendre n).roots) :
    (legendre n).rootMultiplicity x = 1 := by
  rw [← Polynomial.count_roots]
  exact Multiset.count_eq_one_of_mem (roots_legendre_nodup n) hx

theorem roots_legendre_card (n : ℕ) : (legendre n).roots.toFinset.card = n := by
  rw [Multiset.toFinset_card_of_nodup (roots_legendre_nodup n), card_roots_legendre]

theorem roots_legendre_mem_Ioo (n : ℕ) :
    ∀ x ∈ (legendre n).roots.toFinset, x ∈ Set.Ioo (0 : ℝ) 1 := by
  intro x hx
  exact mem_roots_legendre_Ioo (Multiset.mem_toFinset.mp hx)

/-- Canonical increasing enumeration of the actual shifted Legendre roots. -/
def node (n : ℕ) : Fin n → ℝ :=
  (legendre n).roots.toFinset.orderEmbOfFin (roots_legendre_card n)

theorem node_strictMono (n : ℕ) : StrictMono (node n) :=
  ((legendre n).roots.toFinset.orderEmbOfFin (roots_legendre_card n)).strictMono

theorem node_injective (n : ℕ) : Function.Injective (node n) :=
  (node_strictMono n).injective

theorem node_mem_roots (n : ℕ) (i : Fin n) : node n i ∈ (legendre n).roots := by
  exact Multiset.mem_toFinset.mp
    ((legendre n).roots.toFinset.orderEmbOfFin_mem (roots_legendre_card n) i)

theorem node_mem_Ioo (n : ℕ) (i : Fin n) : node n i ∈ Set.Ioo (0 : ℝ) 1 :=
  mem_roots_legendre_Ioo (node_mem_roots n i)

@[simp]
theorem legendre_eval_node (n : ℕ) (i : Fin n) : (legendre n).eval (node n i) = 0 :=
  Polynomial.isRoot_of_mem_roots (node_mem_roots n i)

theorem range_node (n : ℕ) : Set.range (node n) = (legendre n).roots.toFinset :=
  (legendre n).roots.toFinset.range_orderEmbOfFin (roots_legendre_card n)

theorem legendre_isRoot_iff (n : ℕ) (x : ℝ) :
    (legendre n).eval x = 0 ↔ ∃ i : Fin n, node n i = x := by
  constructor
  · intro hx
    have hm : x ∈ (legendre n).roots.toFinset :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (legendre_ne_zero n)).mpr hx)
    change x ∈ Set.range (node n)
    rw [range_node]
    exact hm
  · rintro ⟨i, rfl⟩
    exact legendre_eval_node n i

end AcceleratedLogConcave.Numerics.GaussLegendre
end

end


/- Cardinal -/
section
open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section
namespace AcceleratedLogConcave.Numerics.GaussLegendre

def cardinal (n : ℕ) (i : Fin n) : Polynomial ℝ :=
  Lagrange.basis Finset.univ (node n) i

def weight (n : ℕ) (i : Fin n) : ℝ :=
  ∫ x in (0 : ℝ)..1, (cardinal n i).eval x

@[simp] theorem cardinal_eval_node (n : ℕ) (i j : Fin n) :
    (cardinal n i).eval (node n j) = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [cardinal, Lagrange.eval_basis_self (node_injective n).injOn]
  · simp [cardinal, h, Lagrange.eval_basis_of_ne h]

theorem degree_cardinal_lt (n : ℕ) (i : Fin n) : (cardinal n i).degree < n := by
  rw [cardinal, Lagrange.degree_basis (node_injective n).injOn (Finset.mem_univ i)]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_lt]
  exact_mod_cast Nat.sub_lt (Fin.pos i) zero_lt_one

theorem sum_cardinal (n : ℕ) (hn : 0 < n) : ∑ i : Fin n, cardinal n i = 1 := by
  classical
  exact Lagrange.sum_basis (node_injective n).injOn ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem interpolate_eq (n : ℕ) (p : Polynomial ℝ) (hp : p.degree < n) :
    p = ∑ i : Fin n, Polynomial.C (p.eval (node n i)) * cardinal n i := by
  classical
  simpa [Lagrange.interpolate_apply, cardinal] using
    (Lagrange.eq_interpolate (node_injective n).injOn
      (show p.degree < (Finset.univ : Finset (Fin n)).card by simpa using hp))

theorem integral_eq_sum_of_degree_lt (n : ℕ) (p : Polynomial ℝ) (hp : p.degree < n) :
    (∫ x in (0 : ℝ)..1, p.eval x) =
      ∑ i : Fin n, weight n i * p.eval (node n i) := by
  classical
  conv_lhs => rw [interpolate_eq n p hp]
  simp only [eval_finsetSum, eval_mul, eval_C]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
    exact mul_comm _ _
  · intro i _
    exact ((cardinal n i).continuous.const_mul _).intervalIntegrable _ _

end AcceleratedLogConcave.Numerics.GaussLegendre
end

end


/- Exact -/
section
open Polynomial MeasureTheory
open scoped BigOperators

noncomputable section
namespace AcceleratedLogConcave.Numerics.GaussLegendre

private theorem degree_div_legendre_lt (n : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < (2*n : ℕ)) : (p / legendre n).degree < n := by
  by_cases hz : p / legendre n = 0
  · simp [hz]
  have hpne : p ≠ 0 := by intro h; simp [h] at hz
  have hle : (legendre n).degree ≤ p.degree :=
    le_of_not_gt (fun h => hz ((Polynomial.div_eq_zero_iff (legendre_ne_zero n)).mpr h))
  have hd := Polynomial.degree_add_div (legendre_ne_zero n) hle
  rw [degree_legendre, degree_eq_natDegree hz, degree_eq_natDegree hpne] at hd
  have hdn : n + (p / legendre n).natDegree = p.natDegree := by exact_mod_cast hd
  rw [degree_eq_natDegree hpne] at hp
  have hpn : p.natDegree < 2*n := by exact_mod_cast hp
  rw [← natDegree_lt_iff_degree_lt hz]
  omega

/-- Exact Gauss integration for degree strictly below twice the number of nodes. -/
theorem integral_eq_sum (n : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < (2*n : ℕ)) :
    (∫ x in (0 : ℝ)..1, p.eval x) =
      ∑ i : Fin n, weight n i * p.eval (node n i) := by
  have hr : (p % legendre n).degree < n := by
    simpa using Polynomial.degree_mod_lt p (legendre_ne_zero n)
  have hq := integral_legendre_mul_eq_zero n (p / legendre n)
    (degree_div_legendre_lt n p hp)
  have he : p = legendre n * (p / legendre n) + p % legendre n :=
    (EuclideanDomain.div_add_mod p (legendre n)).symm
  have hqi : IntervalIntegrable
      (fun x => (legendre n).eval x * (p / legendre n).eval x) volume 0 1 :=
    ((legendre n).continuous.mul (p / legendre n).continuous).intervalIntegrable 0 1
  have hri : IntervalIntegrable (fun x => (p % legendre n).eval x) volume 0 1 :=
    (p % legendre n).continuous.intervalIntegrable 0 1
  calc
    (∫ x in (0 : ℝ)..1, p.eval x) =
        ∫ x in (0 : ℝ)..1, (p % legendre n).eval x := by
      conv_lhs => rw [he]
      simp only [eval_add, eval_mul]
      rw [intervalIntegral.integral_add hqi hri, hq, zero_add]
    _ = ∑ i : Fin n, weight n i * (p % legendre n).eval (node n i) :=
      integral_eq_sum_of_degree_lt n _ hr
    _ = ∑ i : Fin n, weight n i * p.eval (node n i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hv := congrArg (Polynomial.eval (node n i)) he
      simpa using congrArg (weight n i * ·) hv.symm

theorem integral_cardinal_mul (n : ℕ) (i j : Fin n) :
    (∫ x in (0 : ℝ)..1, (cardinal n i).eval x * (cardinal n j).eval x) =
      if i = j then weight n i else 0 := by
  classical
  have hd : (cardinal n i * cardinal n j).degree < (2*n : ℕ) := by
    rw [degree_mul, cardinal, cardinal,
      Lagrange.degree_basis (node_injective n).injOn (Finset.mem_univ i),
      Lagrange.degree_basis (node_injective n).injOn (Finset.mem_univ j)]
    simp only [Finset.card_univ, Fintype.card_fin]
    have h : n-1+(n-1) < 2*n := by have := Fin.pos i; omega
    exact_mod_cast h
  have h := integral_eq_sum n (cardinal n i * cardinal n j) hd
  simp only [eval_mul, cardinal_eval_node] at h
  by_cases hij : i = j
  · subst j
    simpa using h
  · simpa [hij] using h

theorem weight_eq_integral_sq (n : ℕ) (i : Fin n) :
    weight n i = ∫ x in (0 : ℝ)..1, ((cardinal n i).eval x)^2 := by
  simpa only [ite_true, pow_two] using (integral_cardinal_mul n i i).symm

theorem weight_pos (n : ℕ) (i : Fin n) : 0 < weight n i := by
  rw [weight_eq_integral_sq]
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0:ℝ) < 1) continuous_const.continuousOn
    ((cardinal n i).continuous.pow 2).continuousOn
    (fun x _ => sq_nonneg ((cardinal n i).eval x))
    ⟨node n i, ⟨(node_mem_Ioo n i).1.le, (node_mem_Ioo n i).2.le⟩,
      by simp⟩
  simpa using h

theorem sum_weight (n : ℕ) (hn : 0 < n) : ∑ i : Fin n, weight n i = 1 := by
  have h := integral_eq_sum_of_degree_lt n (1 : Polynomial ℝ) (by simpa using hn)
  simpa using h.symm

end AcceleratedLogConcave.Numerics.GaussLegendre
end

end


/- Uniform -/
section
noncomputable section
open Polynomial Set

namespace AcceleratedLogConcave.Numerics.GaussLegendre

private theorem iterateD_add (n : ℕ) (p q : Polynomial ℝ) :
    derivative^[n] (p + q) = derivative^[n] p + derivative^[n] q := by
  simp only [← Module.End.pow_apply, map_add]

private theorem power_seed_ode (n : ℕ) :
    let H : Polynomial ℝ := (X - X ^ 2) ^ n
    H.derivative.derivative * X - H.derivative.derivative * X ^ 2 +
      C (1 - (n : ℝ)) * (H.derivative - C 2 * (H.derivative * X)) +
      C (2 * (n : ℝ)) * H = 0 := by
  dsimp only
  have hfirst : (((X - X ^ 2) ^ n : Polynomial ℝ).derivative) * (X - X ^ 2) =
      C (n : ℝ) * (1 - C 2 * X) * (X - X ^ 2) ^ n := by
    cases n with
    | zero => simp
    | succ n =>
      simp only [derivative_pow, derivative_sub, derivative_X,
        Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, C_add, C_1]
      ring
  have hsecond := congrArg Polynomial.derivative hfirst
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_X_pow,
    derivative_C, derivative_one, zero_mul, zero_add, mul_one] at hsecond
  simp only [C_sub, C_mul, C_1]
  norm_num at hsecond ⊢
  linear_combination hsecond

private theorem iterate_seed_ode (n : ℕ) :
    let Q : Polynomial ℝ := derivative^[n] ((X - X ^ 2) ^ n)
    X * (1 - X) * Q.derivative.derivative + (1 - C 2 * X) * Q.derivative +
      C ((n : ℝ) * ((n : ℝ) + 1)) * Q = 0 := by
  let H : Polynomial ℝ := (X - X ^ 2) ^ n
  have h := congrArg (Polynomial.derivative^[n]) (power_seed_ode n)
  change derivative^[n]
    (H.derivative.derivative * X - H.derivative.derivative * X ^ 2 +
      C (1 - (n : ℝ)) * (H.derivative - C 2 * (H.derivative * X)) +
      C (2 * (n : ℝ)) * H) = derivative^[n] 0 at h
  simp only [iterateD_add, iterate_derivative_sub, iterate_derivative_C_mul,
    iterate_derivative_zero] at h
  rw [iterate_derivative_derivative_mul_X,
    show H.derivative.derivative = derivative^[2] H by rfl,
    iterate_derivative_derivative_mul_X_sq,
    iterate_derivative_derivative_mul_X] at h
  simp only [← Function.iterate_succ_apply] at h
  have h1 : derivative^[n + 1] H = (derivative^[n] H).derivative :=
    Function.iterate_succ_apply' _ _ _
  have h2 : derivative^[n + 2] H = (derivative^[n] H).derivative.derivative := by
    rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply', h1]
  rw [h1, h2] at h
  change X * (1 - X) * (derivative^[n] H).derivative.derivative +
    (1 - C 2 * X) * (derivative^[n] H).derivative +
    C ((n : ℝ) * ((n : ℝ) + 1)) * derivative^[n] H = 0
  cases n with
  | zero => simp [H]
  | succ n =>
    simp only [Nat.succ_sub_one, nsmul_eq_mul] at h
    norm_num [C_sub, C_mul, C_add] at h ⊢
    simp only [C_ofNat] at h ⊢
    linear_combination h

/-- The genuine shifted Legendre differential equation, from Rodrigues. -/
theorem legendre_ode (n : ℕ) :
    X * (1 - X) * (legendre n).derivative.derivative +
      (1 - C 2 * X) * (legendre n).derivative +
      C ((n : ℝ) * ((n : ℝ) + 1)) * legendre n = 0 := by
  have h := iterate_seed_ode n
  have hrod : derivative^[n] (((X : Polynomial ℝ) - X ^ 2) ^ n) =
      C (n.factorial : ℝ) * legendre n := by
    rw [show (X - X ^ 2 : Polynomial ℝ) = X * (1 - X) by ring, mul_pow]
    exact (factorial_mul_legendre_eq n).symm
  dsimp only at h
  rw [hrod] at h
  simp only [derivative_C_mul] at h
  have hfact : C (n.factorial : ℝ) ≠ (0 : Polynomial ℝ) := by
    simp only [ne_eq, C_eq_zero]
    exact_mod_cast n.factorial_ne_zero
  apply (mul_eq_zero.mp (show C (n.factorial : ℝ) *
    (X * (1 - X) * (legendre n).derivative.derivative +
      (1 - C 2 * X) * (legendre n).derivative +
      C ((n : ℝ) * ((n : ℝ) + 1)) * legendre n) = 0 by
        linear_combination h)).resolve_left hfact

/-- Pointwise form of the shifted Legendre equation. -/
theorem legendre_ode_eval (n : ℕ) (x : ℝ) :
    x * (1 - x) * (legendre n).derivative.derivative.eval x +
      (1 - 2 * x) * (legendre n).derivative.eval x +
      (n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval x = 0 := by
  have h := congrArg (Polynomial.eval x) (legendre_ode n)
  simpa only [eval_add, eval_mul, eval_sub, eval_X, eval_one, eval_C, eval_zero] using h

private def legendreEnergy (n : ℕ) : Polynomial ℝ :=
  C ((n : ℝ) * ((n : ℝ) + 1)) * legendre n ^ 2 +
    X * (1 - X) * (legendre n).derivative ^ 2

private theorem legendreEnergy_derivative (n : ℕ) :
    (legendreEnergy n).derivative = (C 2 * X - 1) * (legendre n).derivative ^ 2 := by
  dsimp [legendreEnergy]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_pow,
    derivative_X, derivative_sub, derivative_one, zero_mul, zero_add, one_mul,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  simp only [C_ofNat]
  have h := legendre_ode n
  simp only [C_ofNat] at h
  linear_combination (2 * (legendre n).derivative) * h

private theorem legendreEnergy_eval_zero (n : ℕ) :
    (legendreEnergy n).eval 0 = (n : ℝ) * ((n : ℝ) + 1) := by
  simp [legendreEnergy]

private theorem legendreEnergy_eval_one (n : ℕ) :
    (legendreEnergy n).eval 1 = (n : ℝ) * ((n : ℝ) + 1) := by
  have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  simp [legendreEnergy, hs]

private theorem hasDerivAt_legendreEnergy (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y ↦ (legendreEnergy n).eval y)
      ((2 * x - 1) * ((legendre n).derivative.eval x) ^ 2) x := by
  convert (legendreEnergy n).hasDerivAt x using 1
  rw [legendreEnergy_derivative]
  simp

private theorem legendreEnergy_le_endpoints (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (legendreEnergy n).eval x ≤ (n : ℝ) * ((n : ℝ) + 1) := by
  have hleft : AntitoneOn (fun y ↦ (legendreEnergy n).eval y)
      (Set.Icc (0 : ℝ) (1 / 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (1 / 2))
      (legendreEnergy n).continuous.continuousOn
      (fun y _ ↦ (hasDerivAt_legendreEnergy n y).hasDerivWithinAt)
    intro y hy
    have hy' := interior_subset hy
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hy'.2]) (sq_nonneg _)
  have hright : MonotoneOn (fun y ↦ (legendreEnergy n).eval y)
      (Set.Icc (1 / 2 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (1 / 2) 1)
      (legendreEnergy n).continuous.continuousOn
      (fun y _ ↦ (hasDerivAt_legendreEnergy n y).hasDerivWithinAt)
    intro y hy
    have hy' := interior_subset hy
    exact mul_nonneg (by linarith [hy'.1]) (sq_nonneg _)
  by_cases hhalf : x ≤ 1 / 2
  · exact (hleft (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2))
      ⟨hx.1, hhalf⟩ hx.1).trans_eq (legendreEnergy_eval_zero n)
  · exact (hright ⟨(lt_of_not_ge hhalf).le, hx.2⟩
      (by norm_num : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1) hx.2).trans_eq
        (legendreEnergy_eval_one n)

/-- Shifted Legendre polynomials have absolute value at most one on the closed cell.
The zero-degree case is separated before cancelling the energy coefficient. -/
theorem legendre_eval_abs_le_one (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |(legendre n).eval x| ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hN : 0 < (n : ℝ) * ((n : ℝ) + 1) := mul_pos hnpos (by positivity)
  have hnonneg : 0 ≤ x * (1 - x) * ((legendre n).derivative.eval x) ^ 2 :=
    mul_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (sq_nonneg _)
  have hbound := legendreEnergy_le_endpoints n x hx
  simp only [legendreEnergy, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    eval_sub, eval_one] at hbound
  have hs : ((legendre n).eval x) ^ 2 ≤ 1 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

end AcceleratedLogConcave.Numerics.GaussLegendre
end

end


/- Affine -/
section
/-! Affine images of the constructed Gauss–Legendre rule and derivative rows. -/

noncomputable section

open Polynomial MeasureTheory
open scoped BigOperators

namespace AcceleratedLogConcave.Numerics.GaussLegendre

def cellNode (n : ℕ) (a h : ℝ) (i : Fin n) : ℝ := a + h * node n i

def cellWeight (n : ℕ) (h : ℝ) (i : Fin n) : ℝ := h * weight n i

def derivativeRow (n : ℕ) (a h y : ℝ) (i : Fin n) : ℝ :=
  h⁻¹ * (cardinal n i).derivative.eval ((y - a) / h)

theorem cellNode_strictMono (n : ℕ) (a h : ℝ) (hh : 0 < h) :
    StrictMono (cellNode n a h) := by
  intro i j hij
  simpa only [cellNode, add_comm] using
    add_lt_add_left (mul_lt_mul_of_pos_left (node_strictMono n hij) hh) a

theorem cellNode_mem_Ioo (n : ℕ) (a h : ℝ) (hh : 0 < h) (i : Fin n) :
    cellNode n a h i ∈ Set.Ioo a (a + h) := by
  obtain ⟨hi0, hi1⟩ := node_mem_Ioo n i
  constructor
  · exact lt_add_of_pos_right a (mul_pos hh hi0)
  · simpa only [cellNode, add_comm, mul_one] using
      add_lt_add_left (mul_lt_mul_of_pos_left hi1 hh) a

theorem cellWeight_pos (n : ℕ) (i : Fin n) (h : ℝ) (hh : 0 < h) :
    0 < cellWeight n h i := mul_pos hh (weight_pos n i)

theorem cellWeight_nonneg (n : ℕ) (i : Fin n) (h : ℝ) (hh : 0 ≤ h) :
    0 ≤ cellWeight n h i := mul_nonneg hh (weight_pos n i).le

theorem sum_cellWeight (n : ℕ) (hn : 0 < n) (h : ℝ) :
    ∑ i : Fin n, cellWeight n h i = h := by
  simp only [cellWeight, ← Finset.mul_sum, sum_weight n hn, mul_one]

@[simp] theorem cellNode_zero (n : ℕ) (a : ℝ) (i : Fin n) :
    cellNode n a 0 i = a := by simp [cellNode]

@[simp] theorem cellWeight_zero (n : ℕ) (i : Fin n) :
    cellWeight n 0 i = 0 := by simp [cellWeight]

@[simp] theorem node_one (i : Fin 1) : node 1 i = 1 / 2 := by
  have h := legendre_eval_node 1 i
  simp only [legendre_one, eval_sub, eval_one, eval_mul, eval_ofNat, eval_X] at h
  linarith

@[simp] theorem cardinal_one (i : Fin 1) : cardinal 1 i = 1 := by
  fin_cases i
  simp [cardinal, Lagrange.basis]

@[simp] theorem weight_one (i : Fin 1) : weight 1 i = 1 := by
  simp [weight]

@[simp] theorem cellNode_one (a h : ℝ) (i : Fin 1) :
    cellNode 1 a h i = a + h / 2 := by simp [cellNode, div_eq_mul_inv]

@[simp] theorem cellWeight_one (h : ℝ) (i : Fin 1) : cellWeight 1 h i = h := by
  simp [cellWeight]

@[simp] theorem derivativeRow_one (a h y : ℝ) (i : Fin 1) :
    derivativeRow 1 a h y i = 0 := by simp [derivativeRow]

theorem degree_comp_cell (p : ℝ[X]) (a h : ℝ) (hh : h ≠ 0) :
    (p.comp (C a + C h * X)).degree = p.degree := by
  have hd : (C a + C h * X : ℝ[X]).degree = 1 := by
    simpa only [add_comm] using (Polynomial.degree_linear (b := a) hh)
  rw [Polynomial.degree_comp (by rw [hd]; norm_num), hd, mul_one]

/-- Gaussian exactness transported to a positive-length physical cell. -/
theorem integral_cell_eq_sum (n : ℕ) (a h : ℝ) (hh : 0 < h)
    (p : ℝ[X]) (hp : p.degree < (2 * n : ℕ)) :
    (∫ y in a..(a + h), p.eval y) =
      ∑ i : Fin n, cellWeight n h i * p.eval (cellNode n a h i) := by
  let q := p.comp (C a + C h * X)
  have hq : q.degree < (2 * n : ℕ) := by
    simpa [q, degree_comp_cell p a h hh.ne'] using hp
  have he := intervalIntegral.smul_integral_comp_add_mul
    (fun y ↦ p.eval y) (a := 0) (b := 1) h a
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul] at he
  calc
    (∫ y in a..(a + h), p.eval y) = h * ∫ x in (0 : ℝ)..1, q.eval x := by
      simpa only [q, eval_comp, eval_add, eval_C, eval_mul, eval_X] using he.symm
    _ = h * ∑ i : Fin n, weight n i * q.eval (node n i) :=
      congrArg (h * ·) (integral_eq_sum n q hq)
    _ = ∑ i : Fin n, cellWeight n h i * p.eval (cellNode n a h i) := by
      simp only [q, eval_comp, eval_add, eval_C, eval_mul, eval_X,
        cellWeight, cellNode, Finset.mul_sum, mul_assoc]

/-- Interpolation after pulling a physical point back to the reference cell. -/
theorem interpolate_cell_eval (n : ℕ) (a h y : ℝ) (hh : 0 < h)
    (p : ℝ[X]) (hp : p.degree < n) :
    p.eval y = ∑ i : Fin n, p.eval (cellNode n a h i) *
      (cardinal n i).eval ((y - a) / h) := by
  let q := p.comp (C a + C h * X)
  have hq : q.degree < n := by simpa [q, degree_comp_cell p a h hh.ne'] using hp
  have he := congrArg (fun r : ℝ[X] ↦ r.eval ((y - a) / h)) (interpolate_eq n q hq)
  have hy : a + h * ((y - a) / h) = y := by field_simp; ring
  simpa only [q, eval_comp, eval_add, eval_C, eval_mul, eval_X,
    hy, eval_finsetSum, cellNode] using he

/-- Derivative interpolation has the physical reciprocal-length scaling. -/
theorem derivativeRow_reproduces (n : ℕ) (a h y : ℝ) (hh : 0 < h)
    (p : ℝ[X]) (hp : p.degree < n) :
    p.derivative.eval y =
      ∑ i : Fin n, derivativeRow n a h y i * p.eval (cellNode n a h i) := by
  let q := p.comp (C a + C h * X)
  have hq : q.degree < n := by simpa [q, degree_comp_cell p a h hh.ne'] using hp
  have he := congrArg (fun r : ℝ[X] ↦ r.derivative.eval ((y - a) / h))
    (interpolate_eq n q hq)
  have hy : a + h * ((y - a) / h) = y := by field_simp; ring
  have he' : h * p.derivative.eval y =
      ∑ i : Fin n, p.eval (cellNode n a h i) *
        (cardinal n i).derivative.eval ((y - a) / h) := by
    simpa only [q, derivative_comp, derivative_add, derivative_C, derivative_C_mul_X,
      zero_add, derivative_sum, derivative_C_mul, eval_finsetSum,
      eval_mul, eval_C, eval_comp, eval_add, eval_X, derivative_X, eval_one, mul_one,
      hy, cellNode] using he
  calc
    p.derivative.eval y = h⁻¹ * (h * p.derivative.eval y) := by
      rw [← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
    _ = h⁻¹ * ∑ i : Fin n, p.eval (cellNode n a h i) *
        (cardinal n i).derivative.eval ((y - a) / h) := congrArg (h⁻¹ * ·) he'
    _ = ∑ i : Fin n, derivativeRow n a h y i * p.eval (cellNode n a h i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [derivativeRow]
      ring

theorem sum_derivativeRow (n : ℕ) (a h y : ℝ) (hh : 0 < h) :
    ∑ i : Fin n, derivativeRow n a h y i = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have he := derivativeRow_reproduces (n + 1) a h y hh (1 : ℝ[X])
      (by rw [degree_one]; exact_mod_cast Nat.succ_pos n)
    simpa using he.symm

theorem sum_derivativeRow_mul_cellNode (n : ℕ) (hn : 2 ≤ n)
    (a h y : ℝ) (hh : 0 < h) :
    ∑ i : Fin n, derivativeRow n a h y i * cellNode n a h i = 1 := by
  have hp : (X : ℝ[X]).degree < n := by
    rw [degree_X]
    exact_mod_cast (show 1 < n by omega)
  have he := derivativeRow_reproduces n a h y hh X hp
  simpa using he.symm

theorem derivativeRow_affine (n : ℕ) (a h x : ℝ) (hh : 0 < h) (i : Fin n) :
    derivativeRow n a h (a + h * x) i = h⁻¹ * (cardinal n i).derivative.eval x := by
  have he : (a + h * x - a) / h = x := by field_simp; ring
  simp only [derivativeRow, he]

@[simp] theorem derivativeRow_unit (n : ℕ) (x : ℝ) (i : Fin n) :
    derivativeRow n 0 1 x i = (cardinal n i).derivative.eval x := by
  simp [derivativeRow]

theorem sum_abs_derivativeRow_eq (n : ℕ) (a h y : ℝ) (hh : 0 < h) :
    (∑ i : Fin n, |derivativeRow n a h y i|) =
      h⁻¹ * ∑ i : Fin n, |(cardinal n i).derivative.eval ((y - a) / h)| := by
  simp only [derivativeRow, abs_mul, abs_inv, abs_of_pos hh, Finset.mul_sum]

end AcceleratedLogConcave.Numerics.GaussLegendre
end

end


/- Rows -/
section
/-! Scalar row estimates from an already proved finite diagonal Gram identity.
These helpers do not postulate Bessel's inequality or row absolute mass. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace AcceleratedLogConcave.Numerics.GaussLegendre

variable {ι : Type*} [Fintype ι]

def gramRow (μ : Measure ℝ) (l : ι → ℝ → ℝ) (g : ℝ → ℝ) (i : ι) : ℝ :=
  ∫ x, g x * l i x ∂μ

def gramProjection (μ : Measure ℝ) (l : ι → ℝ → ℝ) (w : ι → ℝ)
    (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i, (gramRow μ l g i / w i) * l i x

theorem memLp_gramProjection (μ : Measure ℝ) (l : ι → ℝ → ℝ) (w : ι → ℝ)
    (hl : ∀ i, MemLp (l i) 2 μ) (g : ℝ → ℝ) :
    MemLp (gramProjection μ l w g) 2 μ := by
  exact memLp_finsetSum _ (fun i _ ↦ (hl i).const_mul _)

theorem integral_mul_finite_gram_sum (μ : Measure ℝ) (l : ι → ℝ → ℝ)
    (hl : ∀ i, MemLp (l i) 2 μ) {g : ℝ → ℝ} (hg : MemLp g 2 μ)
    (c : ι → ℝ) :
    (∫ x, g x * (∑ i, c i * l i x) ∂μ) =
      ∑ i, c i * gramRow μ l g i := by
  simp_rw [Finset.mul_sum, ← mul_assoc, mul_comm (g _) (c _), mul_assoc]
  rw [integral_finsetSum (f := fun i x ↦ c i * (g x * l i x)) Finset.univ
    (fun i _ ↦ (hg.integrable_mul (hl i)).const_mul (c i))]
  simp only [integral_const_mul, gramRow]

variable [DecidableEq ι]

theorem gramRow_projection (μ : Measure ℝ) (l : ι → ℝ → ℝ) (w : ι → ℝ)
    (hl : ∀ i, MemLp (l i) 2 μ) (hw : ∀ i, 0 < w i)
    (hgram : ∀ i j, (∫ x, l i x * l j x ∂μ) = if i = j then w i else 0)
    (g : ℝ → ℝ) (j : ι) :
    gramRow μ l (gramProjection μ l w g) j = gramRow μ l g j := by
  classical
  unfold gramRow gramProjection
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum
    (f := fun i x ↦ (gramRow μ l g i / w i) * (l i x * l j x)) Finset.univ
    (fun i _ ↦ ((hl i).integrable_mul (hl j)).const_mul _)]
  simp_rw [integral_const_mul, hgram]
  simp [gramRow, (hw j).ne']

/-- The actual projection residual integral equals energy minus row energy. -/
theorem integral_gramProjection_residual_sq (μ : Measure ℝ)
    (l : ι → ℝ → ℝ) (w : ι → ℝ)
    (hl : ∀ i, MemLp (l i) 2 μ) (hw : ∀ i, 0 < w i)
    (hgram : ∀ i j, (∫ x, l i x * l j x ∂μ) = if i = j then w i else 0)
    {g : ℝ → ℝ} (hg : MemLp g 2 μ) :
    (∫ x, (g x - gramProjection μ l w g x) ^ 2 ∂μ) =
      (∫ x, (g x) ^ 2 ∂μ) - ∑ i, (gramRow μ l g i) ^ 2 / w i := by
  let q := gramProjection μ l w g
  have hq : MemLp q 2 μ := memLp_gramProjection μ l w hl g
  have hgq : (∫ x, g x * q x ∂μ) = ∑ i, (gramRow μ l g i) ^ 2 / w i := by
    rw [show q = fun x ↦ ∑ i, (gramRow μ l g i / w i) * l i x from rfl,
      integral_mul_finite_gram_sum μ l hl hg]
    congr 1
    ext i
    ring
  have hqq : (∫ x, q x * q x ∂μ) = ∑ i, (gramRow μ l g i) ^ 2 / w i := by
    conv_lhs => arg 2; ext x; arg 2; change ∑ i, (gramRow μ l g i / w i) * l i x
    rw [integral_mul_finite_gram_sum μ l hl hq]
    simp_rw [show q = gramProjection μ l w g from rfl,
      gramRow_projection μ l w hl hw hgram]
    congr 1
    ext i
    ring
  have hp (x : ℝ) : (g x - q x) ^ 2 =
      (g x) ^ 2 - 2 * (g x * q x) + q x * q x := by ring
  simp_rw [show gramProjection μ l w g = q from rfl, hp]
  rw [integral_add (f := fun x ↦ (g x)^2 - 2*(g x*q x)) (g := fun x ↦ q x*q x)
      (hg.integrable_sq.sub ((hg.integrable_mul hq).const_mul 2)) (hq.integrable_mul hq),
    integral_sub (f := fun x ↦ (g x)^2) (g := fun x ↦ 2*(g x*q x))
      hg.integrable_sq ((hg.integrable_mul hq).const_mul 2),
    integral_const_mul, hgq, hqq]
  ring

/-- Bessel's row inequality follows from nonnegativity of the actual residual square. -/
theorem gramRow_sq_div_weight_le (μ : Measure ℝ) (l : ι → ℝ → ℝ) (w : ι → ℝ)
    (hl : ∀ i, MemLp (l i) 2 μ) (hw : ∀ i, 0 < w i)
    (hgram : ∀ i j, (∫ x, l i x * l j x ∂μ) = if i = j then w i else 0)
    {g : ℝ → ℝ} (hg : MemLp g 2 μ) :
    (∑ i, (gramRow μ l g i) ^ 2 / w i) ≤ ∫ x, (g x) ^ 2 ∂μ := by
  have h : 0 ≤ ∫ x, (g x - gramProjection μ l w g x) ^ 2 ∂μ :=
    integral_nonneg (fun x ↦ sq_nonneg (g x - gramProjection μ l w g x))
  rw [integral_gramProjection_residual_sq μ l w hl hw hgram hg] at h
  linarith

/-- Positive mass-one Gram weights turn row energy into absolute row mass. -/
theorem sum_abs_gramRow_le (μ : Measure ℝ) (l : ι → ℝ → ℝ) (w : ι → ℝ)
    (hl : ∀ i, MemLp (l i) 2 μ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hgram : ∀ i j, (∫ x, l i x * l j x ∂μ) = if i = j then w i else 0)
    {g : ℝ → ℝ} (hg : MemLp g 2 μ) :
    (∑ i, |gramRow μ l g i|) ≤ Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  have hc := Finset.sq_sum_div_le_sum_sq_div Finset.univ
    (fun i ↦ |gramRow μ l g i|) (fun i _ ↦ hw i)
  simp only [hsum, div_one, sq_abs] at hc
  have he := gramRow_sq_div_weight_le μ l w hl hw hgram hg
  exact (Real.le_sqrt (Finset.sum_nonneg (fun i _ ↦ abs_nonneg _))
    (integral_nonneg (fun x ↦ sq_nonneg (g x)))).mpr (hc.trans he)

/-- Squared absolute row mass, without normalizing the total Gram weight. -/
theorem sum_abs_gramRow_sq_le (μ : Measure ℝ) (l : ι → ℝ → ℝ) (w : ι → ℝ)
    (hl : ∀ i, MemLp (l i) 2 μ) (hw : ∀ i, 0 < w i)
    (hgram : ∀ i j, (∫ x, l i x * l j x ∂μ) = if i = j then w i else 0)
    {g : ℝ → ℝ} (hg : MemLp g 2 μ) :
    (∑ i, |gramRow μ l g i|)^2 ≤ (∑ i, w i) * ∫ x, (g x)^2 ∂μ := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := fun i ↦ (gramRow μ l g i)^2 / w i) (g := w)
    (r := fun i ↦ |gramRow μ l g i|)
    (fun i _ ↦ div_nonneg (sq_nonneg _) (hw i).le)
    (fun i _ ↦ (hw i).le)
    (fun i _ ↦ by rw [sq_abs, div_mul_cancel₀ _ (hw i).ne'])
  have he := mul_le_mul_of_nonneg_right (gramRow_sq_div_weight_le μ l w hl hw hgram hg)
    (show 0 ≤ ∑ i, w i from Finset.sum_nonneg (fun i _ ↦ (hw i).le))
  simpa only [mul_comm] using hc.trans he

omit [Fintype ι] [DecidableEq ι] in
theorem memLp_two_restrict_Ioc_of_continuous {f : ℝ → ℝ}
    (hf : Continuous f) (a b : ℝ) : MemLp f 2 (volume.restrict (Ioc a b)) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  exact ((hf.pow 2).intervalIntegrable a b).1

omit [Fintype ι] in
/-- Physical-cell Gram identity under the actual affine pullback. -/
theorem integral_affine_gram (l : ι → ℝ → ℝ) (w : ι → ℝ)
    (hgram : ∀ i j, (∫ x in (0 : ℝ)..1, l i x * l j x) =
      if i = j then w i else 0)
    (a h : ℝ) (hh : 0 < h) (i j : ι) :
    (∫ y, l i ((y-a)/h) * l j ((y-a)/h) ∂volume.restrict (Ioc a (a+h))) =
      if i = j then h * w i else 0 := by
  rw [← intervalIntegral.integral_of_le (by linarith : a ≤ a+h)]
  have he := intervalIntegral.smul_integral_comp_add_mul
    (fun y ↦ l i ((y-a)/h) * l j ((y-a)/h)) (a := 0) (b := 1) h a
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul] at he
  have heq (x : ℝ) : (a+h*x-a)/h = x := by field_simp; ring
  simp_rw [heq] at he
  rw [← he, hgram]
  split_ifs <;> simp

/-- A signed row on a physical subinterval, for an actual continuous reference family. -/
def affineGramPartialRow (l : ι → ℝ → ℝ) (a h u v : ℝ)
    (k : ℝ → ℝ) (i : ι) : ℝ :=
  ∫ y in (a+h*u)..(a+h*v), k y * l i ((y-a)/h)

omit [Fintype ι] [DecidableEq ι] in
theorem affineGramPartialRow_swap (l : ι → ℝ → ℝ) (a h u v : ℝ)
    (k : ℝ → ℝ) (i : ι) :
    affineGramPartialRow l a h v u k i = -affineGramPartialRow l a h u v k i :=
  intervalIntegral.integral_symm _ _

omit [Fintype ι] [DecidableEq ι] in
/-- The exact signed affine scaling formula; no absolute values replace the row. -/
theorem affineGramPartialRow_scale (l : ι → ℝ → ℝ) (a h u v : ℝ) (hh : h ≠ 0)
    (k : ℝ → ℝ) (i : ι) :
    affineGramPartialRow l a h u v k i =
      h * ∫ x in u..v, k (a+h*x) * l i x := by
  have he := intervalIntegral.smul_integral_comp_add_mul
    (fun y ↦ k y * l i ((y-a)/h)) (a := u) (b := v) h a
  have heq (x : ℝ) : (a+h*x-a)/h = x := by field_simp; ring
  simpa only [affineGramPartialRow, smul_eq_mul, heq] using he.symm

omit [Fintype ι] [DecidableEq ι] in
theorem affineGramPartialRow_full_one (l : ι → ℝ → ℝ) (a h : ℝ) (hh : h ≠ 0)
    (i : ι) : affineGramPartialRow l a h 0 1 (fun _ ↦ 1) i =
      h * ∫ x in (0 : ℝ)..1, l i x := by
  rw [affineGramPartialRow_scale l a h 0 1 hh]
  simp only [one_mul]

/-- Partial row absolute mass. Local AE data suffice; orientation is retained
in the row and removed only when taking its absolute value. -/
theorem sum_abs_affineGramPartialRow_le
    (l : ι → ℝ → ℝ) (w : ι → ℝ) (hl : ∀ i, Continuous (l i))
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hgram : ∀ i j, (∫ x in (0 : ℝ)..1, l i x * l j x) =
      if i = j then w i else 0)
    (a h u v : ℝ) (hh : 0 < h) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (k : ℝ → ℝ)
    (hk : AEStronglyMeasurable k (volume.restrict (uIoc (a+h*u) (a+h*v))))
    (hbound : ∀ᵐ y ∂volume.restrict (uIoc (a+h*u) (a+h*v)), |k y| ≤ 1) :
    (∑ i, |affineGramPartialRow l a h u v k i|) ≤ h * Real.sqrt |v-u| := by
  let A := Ioc a (a+h)
  let s := uIoc (a+h*u) (a+h*v)
  let μ : Measure ℝ := volume.restrict A
  let g := s.indicator k
  let f : ι → ℝ → ℝ := fun i y ↦ l i ((y-a)/h)
  let : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr (by simp [s])
  have hsm : MeasurableSet s := measurableSet_uIoc
  have hsA : s ⊆ A := by
    intro y hy
    change min (a+h*u) (a+h*v) < y ∧ y ≤ max (a+h*u) (a+h*v) at hy
    have hu0 : a ≤ a+h*u := by nlinarith [mul_nonneg hh.le hu.1]
    have hv0 : a ≤ a+h*v := by nlinarith [mul_nonneg hh.le hv.1]
    have hu1 : a+h*u ≤ a+h := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hu.2)]
    have hv1 : a+h*v ≤ a+h := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hv.2)]
    exact ⟨(le_min hu0 hv0).trans_lt hy.1, hy.2.trans (max_le hu1 hv1)⟩
  have hk2 : MemLp k 2 (volume.restrict s) :=
    MemLp.of_bound hk 1 (by simpa only [Real.norm_eq_abs] using hbound)
  have hg : MemLp g 2 μ := by
    rw [show g = s.indicator k from rfl, memLp_indicator_iff_restrict hsm]
    change MemLp k 2 ((volume.restrict A).restrict s)
    rw [Measure.restrict_restrict_of_subset hsA]
    exact hk2
  have hf (i : ι) : MemLp (f i) 2 μ :=
    memLp_two_restrict_Ioc_of_continuous ((hl i).comp (by fun_prop)) a (a+h)
  have hfgram (i j : ι) : (∫ y, f i y * f j y ∂μ) =
      if i = j then h*w i else 0 := integral_affine_gram l w hgram a h hh i j
  have hwsum : (∑ i, h*w i) = h := by rw [← Finset.mul_sum, hsum, mul_one]
  have henergy : (∫ y, (g y)^2 ∂μ) ≤ h * |v-u| := by
    have hind : (fun y ↦ (g y)^2) = s.indicator (fun y ↦ (k y)^2) := by
      ext y
      by_cases hy : y ∈ s <;> simp [g, hy]
    rw [hind, integral_indicator hsm]
    change (∫ y, (k y)^2 ∂(volume.restrict A).restrict s) ≤ _
    rw [Measure.restrict_restrict_of_subset hsA]
    have hb : ∀ᵐ y ∂volume.restrict s, (k y)^2 ≤ (1 : ℝ) := by
      filter_upwards [hbound] with y hy
      nlinarith [sq_abs (k y), abs_nonneg (k y)]
    calc
      _ ≤ ∫ _y : ℝ, (1 : ℝ) ∂volume.restrict s :=
        integral_mono_ae hk2.integrable_sq (integrable_const 1) hb
      _ = h * |v-u| := by
        simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
          Measure.restrict_apply_univ, s, Real.volume_uIoc, ENNReal.toReal_ofReal (abs_nonneg _)]
        rw [show a+h*v-(a+h*u) = h*(v-u) by ring, abs_mul, abs_of_pos hh]
  have hrow (i : ι) : gramRow μ f g i =
      ∫ y in s, k y * l i ((y-a)/h) := by
    unfold gramRow
    change (∫ y, s.indicator k y * l i ((y-a)/h) ∂μ) = _
    simp_rw [← Set.indicator_mul_left s k (fun y ↦ l i ((y-a)/h))]
    rw [integral_indicator hsm]
    change (∫ y, k y * l i ((y-a)/h) ∂(volume.restrict A).restrict s) = _
    rw [Measure.restrict_restrict_of_subset hsA]
  have habs (i : ι) : |affineGramPartialRow l a h u v k i| = |gramRow μ f g i| := by
    rw [affineGramPartialRow, intervalIntegral.abs_integral_eq_abs_integral_uIoc, hrow]
  simp_rw [habs]
  have hsq := sum_abs_gramRow_sq_le μ f (fun i ↦ h*w i) hf
    (fun i ↦ mul_pos hh (hw i)) hfgram hg
  rw [hwsum] at hsq
  have hsq' := hsq.trans (mul_le_mul_of_nonneg_left henergy hh.le)
  have hsqrt := Real.sq_sqrt (abs_nonneg (v-u))
  have hnonneg := mul_nonneg hh.le (Real.sqrt_nonneg |v-u|)
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun i _ ↦ abs_nonneg (gramRow μ f g i)))
    hnonneg).mp
  calc
    _ ≤ h*(h*|v-u|) := hsq'
    _ = (h * Real.sqrt |v-u|)^2 := by rw [mul_pow, hsqrt]; ring

/-- The source's full-cell mass bound follows from the sharper partial-cell bound. -/
theorem sum_abs_affineGramPartialRow_le_length
    (l : ι → ℝ → ℝ) (w : ι → ℝ) (hl : ∀ i, Continuous (l i))
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hgram : ∀ i j, (∫ x in (0 : ℝ)..1, l i x * l j x) =
      if i = j then w i else 0)
    (a h u v : ℝ) (hh : 0 < h) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (k : ℝ → ℝ)
    (hk : AEStronglyMeasurable k (volume.restrict (uIoc (a+h*u) (a+h*v))))
    (hbound : ∀ᵐ y ∂volume.restrict (uIoc (a+h*u) (a+h*v)), |k y| ≤ 1) :
    (∑ i, |affineGramPartialRow l a h u v k i|) ≤ h := by
  have habs : |v-u| ≤ (1 : ℝ) := abs_le.mpr ⟨by linarith [hu.2, hv.1],
    by linarith [hu.1, hv.2]⟩
  have hs : Real.sqrt |v-u| ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using habs⟩
  exact (sum_abs_affineGramPartialRow_le l w hl hw hsum hgram a h u v hh hu hv k hk hbound).trans
    ((mul_le_mul_of_nonneg_left hs hh.le).trans_eq (mul_one h))

end AcceleratedLogConcave.Numerics.GaussLegendre
end

-- Concrete wrappers below use only the constructed nodes, cardinals, and weights.
namespace AcceleratedLogConcave.Numerics.GaussLegendre
open Polynomial MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable def integrationRow (n : ℕ) (g : ℝ → ℝ) (i : Fin n) : ℝ :=
  ∫ x in (0 : ℝ)..1, g x * (cardinal n i).eval x

theorem integrationRow_eq_gramRow (n : ℕ) (g : ℝ → ℝ) (i : Fin n) :
    integrationRow n g i =
      gramRow (volume.restrict (Ioc (0 : ℝ) 1)) (fun j x ↦ (cardinal n j).eval x) g i :=
  intervalIntegral.integral_of_le zero_le_one

theorem integrationRow_reproduces (n : ℕ) (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (p : Polynomial ℝ) (hp : p.degree < n) :
    (∫ x in (0 : ℝ)..1, g x * p.eval x) =
      ∑ i : Fin n, integrationRow n g i * p.eval (node n i) := by
  have hi (x : ℝ) : p.eval x = ∑ i : Fin n, p.eval (node n i) * (cardinal n i).eval x := by
    simpa only [eval_finsetSum, eval_mul, eval_C] using congrArg (eval x) (interpolate_eq n p hp)
  rw [intervalIntegral.integral_of_le zero_le_one]
  conv_lhs => arg 2; ext x; rw [hi x]
  rw [integral_mul_finite_gram_sum _ _
    (fun i ↦ memLp_two_restrict_Ioc_of_continuous (cardinal n i).continuous 0 1) hg]
  apply Finset.sum_congr rfl
  intro i _
  rw [integrationRow_eq_gramRow]
  ring

theorem integrationRow_sq_div_weight_le (n : ℕ) (_hn : 0 < n)
    (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    (∑ i : Fin n, (integrationRow n g i)^2 / weight n i) ≤
      ∫ x in (0 : ℝ)..1, (g x)^2 := by
  simp_rw [integrationRow_eq_gramRow]
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact gramRow_sq_div_weight_le _ _ (weight n)
    (fun i ↦ memLp_two_restrict_Ioc_of_continuous (cardinal n i).continuous 0 1)
    (weight_pos n)
    (fun i j ↦ by simpa only [intervalIntegral.integral_of_le zero_le_one]
      using integral_cardinal_mul n i j) hg

theorem sum_abs_integrationRow_le (n : ℕ) (hn : 0 < n)
    (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    (∑ i : Fin n, |integrationRow n g i|) ≤
      Real.sqrt (∫ x in (0 : ℝ)..1, (g x)^2) := by
  simp_rw [integrationRow_eq_gramRow]
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact sum_abs_gramRow_le _ _ (weight n)
    (fun i ↦ memLp_two_restrict_Ioc_of_continuous (cardinal n i).continuous 0 1)
    (weight_pos n) (sum_weight n hn)
    (fun i j ↦ by simpa only [intervalIntegral.integral_of_le zero_le_one]
      using integral_cardinal_mul n i j) hg

noncomputable def partialRow (n : ℕ) (a h u v : ℝ) (k : ℝ → ℝ) (i : Fin n) : ℝ :=
  ∫ y in (a+h*u)..(a+h*v), k y * (cardinal n i).eval ((y-a)/h)

theorem partialRow_swap (n : ℕ) (a h u v : ℝ) (k : ℝ → ℝ) (i : Fin n) :
    partialRow n a h v u k i = -partialRow n a h u v k i :=
  affineGramPartialRow_swap (fun j x ↦ (cardinal n j).eval x) a h u v k i

theorem partialRow_scale (n : ℕ) (a h u v : ℝ) (hh : h ≠ 0)
    (k : ℝ → ℝ) (i : Fin n) :
    partialRow n a h u v k i =
      h * ∫ x in u..v, k (a+h*x) * (cardinal n i).eval x :=
  affineGramPartialRow_scale (fun j x ↦ (cardinal n j).eval x) a h u v hh k i

@[simp] theorem partialRow_self (n : ℕ) (a h u : ℝ) (k : ℝ → ℝ) (i : Fin n) :
    partialRow n a h u u k i = 0 := by simp [partialRow]

@[simp] theorem partialRow_zero_length (n : ℕ) (a u v : ℝ) (k : ℝ → ℝ) (i : Fin n) :
    partialRow n a 0 u v k i = 0 := by simp [partialRow]

theorem partialRow_full_one (n : ℕ) (a h : ℝ) (hh : 0 < h) (i : Fin n) :
    partialRow n a h 0 1 (fun _ ↦ 1) i = cellWeight n h i :=
  affineGramPartialRow_full_one (fun j x ↦ (cardinal n j).eval x) a h hh.ne' i

theorem partialRow_reproduces (n : ℕ) (a h u v : ℝ) (hh : 0 < h)
    (k : ℝ → ℝ) (hk : IntervalIntegrable k volume (a+h*u) (a+h*v))
    (p : Polynomial ℝ) (hp : p.degree < n) :
    (∫ y in (a+h*u)..(a+h*v), k y * p.eval y) =
      ∑ i : Fin n, partialRow n a h u v k i * p.eval (cellNode n a h i) := by
  have hi (i : Fin n) : IntervalIntegrable
      (fun y ↦ k y * (cardinal n i).eval ((y-a)/h)) volume (a+h*u) (a+h*v) :=
    hk.mul_continuousOn (((cardinal n i).continuous.comp (by fun_prop)).continuousOn)
  calc
    _ = ∫ y in (a+h*u)..(a+h*v), ∑ i : Fin n,
        (k y * (cardinal n i).eval ((y-a)/h)) * p.eval (cellNode n a h i) := by
      apply intervalIntegral.integral_congr
      intro y _
      change k y * p.eval y = ∑ i : Fin n,
        (k y * (cardinal n i).eval ((y-a)/h)) * p.eval (cellNode n a h i)
      rw [interpolate_cell_eval n a h y hh p hp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin n, partialRow n a h u v k i * p.eval (cellNode n a h i) := by
      rw [intervalIntegral.integral_finsetSum (fun i _ ↦ (hi i).mul_const _)]
      simp only [intervalIntegral.integral_mul_const, partialRow]

theorem sum_abs_partialRow_le (n : ℕ) (hn : 0 < n) (a h u v : ℝ)
    (hh : 0 < h) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (k : ℝ → ℝ)
    (hk : AEStronglyMeasurable k (volume.restrict (uIoc (a+h*u) (a+h*v))))
    (hbound : ∀ᵐ y ∂volume.restrict (uIoc (a+h*u) (a+h*v)), |k y| ≤ 1) :
    (∑ i : Fin n, |partialRow n a h u v k i|) ≤ h * Real.sqrt |v-u| :=
  sum_abs_affineGramPartialRow_le (fun i x ↦ (cardinal n i).eval x) (weight n)
    (fun i ↦ (cardinal n i).continuous) (weight_pos n) (sum_weight n hn)
    (integral_cardinal_mul n) a h u v hh hu hv k hk hbound

theorem sum_abs_partialRow_le_length (n : ℕ) (hn : 0 < n) (a h u v : ℝ)
    (hh : 0 < h) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (k : ℝ → ℝ)
    (hk : AEStronglyMeasurable k (volume.restrict (uIoc (a+h*u) (a+h*v))))
    (hbound : ∀ᵐ y ∂volume.restrict (uIoc (a+h*u) (a+h*v)), |k y| ≤ 1) :
    (∑ i : Fin n, |partialRow n a h u v k i|) ≤ h :=
  sum_abs_affineGramPartialRow_le_length (fun i x ↦ (cardinal n i).eval x) (weight n)
    (fun i ↦ (cardinal n i).continuous) (weight_pos n) (sum_weight n hn)
    (integral_cardinal_mul n) a h u v hh hu hv k hk hbound

end AcceleratedLogConcave.Numerics.GaussLegendre

end


/- Derivative -/
section
noncomputable section
open Polynomial MeasureTheory Set
open scoped BigOperators

namespace AcceleratedLogConcave.Numerics.GaussLegendre

private def legendreSequence : Polynomial.Sequence ℝ where
  elems' := legendre
  degree_eq' := degree_legendre

theorem exists_legendre_expansion (n : ℕ) (p : Polynomial ℝ) (hp : p.degree < n) :
    ∃ c : Fin n → ℝ, p = ∑ k : Fin n, c k • legendre k := by
  have hspan := legendreSequence.span_degreeLT (m := n)
    (fun k _ => isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (legendre_ne_zero k)))
  have hrange : Set.range (fun k : Fin n => legendre k) = legendreSequence '' Set.Iio n := by
    ext p
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.isLt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hmem : p ∈ Submodule.span ℝ (Set.range (fun k : Fin n => legendre k)) := by
    rw [hrange, hspan, Polynomial.mem_degreeLT]
    exact hp
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  exact ⟨c, hc.symm⟩

theorem integral_legendre_gram (k j : ℕ) :
    (∫ x in (0 : ℝ)..1, (legendre k).eval x * (legendre j).eval x) =
      if k = j then 1 / (2*k+1 : ℝ) else 0 := by
  by_cases h : k = j
  · subst j
    simpa [pow_two] using integral_legendre_sq k
  · simp only [h, ite_false]
    exact integral_legendre_mul_legendre k j (Ne.symm h)

theorem integral_legendre_expansion_mul (n : ℕ) (c : Fin n → ℝ) (j : Fin n) :
    (∫ x in (0 : ℝ)..1,
      (∑ k : Fin n, c k • legendre k).eval x * (legendre j).eval x) =
      c j / (2*(j : ℕ)+1 : ℝ) := by
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [mul_assoc, intervalIntegral.integral_const_mul, integral_legendre_gram]
    simp [Fin.val_inj, mul_ite, div_eq_mul_inv]
  · intro k _
    exact (((legendre k).continuous.const_mul (c k)).mul
      (legendre j).continuous).intervalIntegrable _ _

theorem legendre_expansion (n : ℕ) (p : Polynomial ℝ) (hp : p.degree < n) :
    p = ∑ k : Fin n,
      ((2*(k : ℕ)+1 : ℝ) *
        (∫ x in (0 : ℝ)..1, p.eval x * (legendre k).eval x)) • legendre k := by
  obtain ⟨c, hc⟩ := exists_legendre_expansion n p hp
  have hcoeff (k : Fin n) :
      (2*(k : ℕ)+1 : ℝ) * (∫ x in (0 : ℝ)..1, p.eval x * (legendre k).eval x) =
        c k := by
    rw [hc, integral_legendre_expansion_mul]
    field_simp
  simp_rw [hcoeff]
  exact hc

@[simp] theorem legendre_derivative_eval_zero (n : ℕ) :
    (legendre n).derivative.eval 0 = -(n : ℝ) * (n+1 : ℝ) := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative]
  simp [legendre, coeff_shiftedLegendre, Nat.choose_succ_self_right]

theorem integral_legendre_derivative_mul (n k : ℕ) (hk : k < n) :
    (∫ x in (0 : ℝ)..1, (legendre n).derivative.eval x * (legendre k).eval x) =
      (-1 : ℝ)^(n+k) - 1 := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => (legendre k).hasDerivAt x)
    (fun x _ => (legendre n).hasDerivAt x)
    ((legendre k).derivative.continuous.intervalIntegrable (0 : ℝ) 1)
    ((legendre n).derivative.continuous.intervalIntegrable (0 : ℝ) 1)
  have hz := integral_legendre_mul_eq_zero n (legendre k).derivative
    (lt_of_le_of_lt degree_derivative_le (by simpa))
  simpa only [legendre_eval_one, legendre_eval_zero, one_mul,
    mul_comm, ← pow_add, hz, sub_zero, Nat.add_comm] using hibp

theorem legendre_derivative_expansion (n : ℕ) :
    (legendre n).derivative = ∑ k : Fin n,
      ((2*(k : ℕ)+1 : ℝ) * ((-1 : ℝ)^(n+(k : ℕ)) - 1)) • legendre k := by
  have h := legendre_expansion n (legendre n).derivative
    (by simpa using degree_derivative_lt (legendre_ne_zero n))
  simp_rw [integral_legendre_derivative_mul n _ (Fin.isLt _)] at h
  exact h

theorem legendre_derivative_coefficient_nonpos (n k : ℕ) :
    (2*k+1 : ℝ) * ((-1 : ℝ)^(n+k) - 1) ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  have h : (-1 : ℝ)^(n+k) ≤ 1 :=
    (le_abs_self _).trans (by rw [abs_neg_one_pow])
  linarith

theorem sum_abs_legendre_derivative_coefficients (n : ℕ) :
    (∑ k : Fin n, |(2*(k : ℕ)+1 : ℝ) * ((-1 : ℝ)^(n+(k : ℕ))-1)|) =
      (n : ℝ) * (n+1 : ℝ) := by
  have h := congrArg (Polynomial.eval 0) (legendre_derivative_expansion n)
  simp only [legendre_derivative_eval_zero, eval_finsetSum, eval_smul, smul_eq_mul,
    legendre_eval_zero, mul_one] at h
  simp_rw [abs_of_nonpos (legendre_derivative_coefficient_nonpos n _)]
  rw [Finset.sum_neg_distrib, ← h]
  ring

/-- The sharp endpoint derivative bound is uniform on the closed unit interval. -/
theorem legendre_derivative_eval_abs_le (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |(legendre n).derivative.eval x| ≤ (n : ℝ) * (n+1 : ℝ) := by
  rw [legendre_derivative_expansion]
  simp only [eval_finsetSum, eval_smul, smul_eq_mul]
  calc
    _ ≤ ∑ k : Fin n,
        |((2*(k : ℕ)+1 : ℝ) * ((-1 : ℝ)^(n+(k : ℕ))-1)) *
          (legendre k).eval x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, |(2*(k : ℕ)+1 : ℝ) * ((-1 : ℝ)^(n+(k : ℕ))-1)| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (legendre_eval_abs_le_one k x hx)
    _ = _ := sum_abs_legendre_derivative_coefficients n

theorem sum_legendre_dimensions (n : ℕ) :
    (∑ k : Fin n, (2*(k : ℕ)+1 : ℝ)) = (n : ℝ)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [ih]
    ring

/-- A coarse square bound sufficient for the manuscript's cubic derivative row. -/
theorem sum_legendre_derivative_sq_le (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑ k : Fin n, (2*(k : ℕ)+1 : ℝ) * ((legendre k).derivative.eval x)^2) ≤
      (n : ℝ)^6 := by
  have hk (k : Fin n) : |(legendre k).derivative.eval x| ≤ (n : ℝ)^2 := by
    have hn0 : (0 : ℝ) ≤ k := by positivity
    have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
    have hbound := legendre_derivative_eval_abs_le k x hx
    nlinarith
  calc
    _ ≤ ∑ k : Fin n, (2*(k : ℕ)+1 : ℝ) * (n : ℝ)^4 := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h := sq_le_sq₀ (abs_nonneg ((legendre k).derivative.eval x))
        (sq_nonneg (n : ℝ)) |>.mpr (hk k)
      simpa only [sq_abs, ← pow_mul] using h
    _ = _ := by rw [← Finset.sum_mul, sum_legendre_dimensions]; ring

theorem integral_poly_mul_legendre_expansion (n : ℕ) (p : Polynomial ℝ)
    (c : Fin n → ℝ) :
    (∫ y in (0 : ℝ)..1, p.eval y * (∑ k : Fin n, c k • legendre k).eval y) =
      ∑ k : Fin n, c k * ∫ y in (0 : ℝ)..1, p.eval y * (legendre k).eval y := by
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [show (fun y => p.eval y * (c k * (legendre k).eval y)) =
      (fun y => c k * (p.eval y * (legendre k).eval y)) by ext y; ring,
      intervalIntegral.integral_const_mul]
  · intro k _
    exact (p.continuous.mul ((legendre k).continuous.const_mul (c k))).intervalIntegrable _ _

/-- The finite polynomial representing differentiation in the Legendre inner product. -/
def derivativeKernel (n : ℕ) (x : ℝ) : Polynomial ℝ :=
  ∑ k : Fin n, ((2*(k : ℕ)+1 : ℝ) * (legendre k).derivative.eval x) • legendre k

theorem derivative_eq_integral_derivativeKernel (n : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < n) (x : ℝ) :
    p.derivative.eval x =
      ∫ y in (0 : ℝ)..1, (derivativeKernel n x).eval y * p.eval y := by
  have h := congrArg (fun q : Polynomial ℝ => q.derivative.eval x) (legendre_expansion n p hp)
  simp only [derivative_sum, derivative_smul, eval_finsetSum, eval_smul, smul_eq_mul] at h
  rw [h]
  conv_rhs => arg 1; ext y; rw [mul_comm]
  rw [derivativeKernel, integral_poly_mul_legendre_expansion]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem integral_derivativeKernel_sq (n : ℕ) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, ((derivativeKernel n x).eval y)^2) =
      ∑ k : Fin n, (2*(k : ℕ)+1 : ℝ) * ((legendre k).derivative.eval x)^2 := by
  simp only [pow_two]
  rw [show (fun y => (derivativeKernel n x).eval y * (derivativeKernel n x).eval y) =
    (fun y => (derivativeKernel n x).eval y *
      (∑ k : Fin n, ((2*(k : ℕ)+1 : ℝ) * (legendre k).derivative.eval x) • legendre k).eval y)
      from rfl, integral_poly_mul_legendre_expansion]
  apply Finset.sum_congr rfl
  intro k _
  rw [derivativeKernel, integral_legendre_expansion_mul]
  have hpos : (0 : ℝ) < 2*(k : ℕ)+1 := by positivity
  field_simp

theorem integral_derivativeKernel_sq_le (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y in (0 : ℝ)..1, ((derivativeKernel n x).eval y)^2) ≤ (n : ℝ)^6 := by
  rw [integral_derivativeKernel_sq]
  exact sum_legendre_derivative_sq_le n x hx

/-- Differentiated cardinal values are genuine integral rows of the derivative kernel. -/
theorem cardinal_derivative_eq_integrationRow (n : ℕ) (x : ℝ) (i : Fin n) :
    (cardinal n i).derivative.eval x =
      integrationRow n (fun y => (derivativeKernel n x).eval y) i :=
  derivative_eq_integral_derivativeKernel n (cardinal n i) (degree_cardinal_lt n i) x

/-- The manuscript's cubic derivative row estimate holds on the closed unit cell. -/
theorem sum_abs_cardinal_derivative_le (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i : Fin n, |(cardinal n i).derivative.eval x|) ≤ (n : ℝ)^3 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp_rw [cardinal_derivative_eq_integrationRow]
    apply (sum_abs_integrationRow_le n hn (fun y => (derivativeKernel n x).eval y)
      (memLp_two_restrict_Ioc_of_continuous (derivativeKernel n x).continuous 0 1)).trans
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    simpa only [← pow_mul] using integral_derivativeKernel_sq_le n x hx

/-- Physical derivative row mass includes precisely one reciprocal cell length. -/
theorem sum_abs_derivativeRow_le (n : ℕ) (a h y : ℝ) (hh : 0 < h)
    (hy : y ∈ Set.Icc a (a+h)) :
    (∑ i : Fin n, |derivativeRow n a h y i|) ≤ (n : ℝ)^3 / h := by
  have hx : (y-a)/h ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hy.1) hh.le
    · apply (div_le_one hh).mpr
      linarith [hy.2]
  rw [sum_abs_derivativeRow_eq n a h y hh]
  calc
    _ ≤ h⁻¹ * (n : ℝ)^3 :=
      mul_le_mul_of_nonneg_left (sum_abs_cardinal_derivative_le n _ hx)
        (inv_nonneg.mpr hh.le)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

end AcceleratedLogConcave.Numerics.GaussLegendre
end

end
