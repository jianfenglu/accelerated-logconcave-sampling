/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import AcceleratedLogConcave.Numerics.GaussLegendre
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Reciprocal-square Gauss–Legendre quadrature and kernel value coefficients

This file proves the scalar claims behind `sources/warm-start.tex:2173–2180`
for the actual constructed Gauss–Legendre rule. The endpoint moment uses the
polynomial `(1 - Q_n) / X`, with `Q_n(x) = P_n(1 - 2*x)`. Positive later cells
use an explicitly constructed polynomial below the reciprocal square.

The generic finite-partition theorem preserves the full signed coefficient at
zero, `-1/b - sum (w/rho^2)`. Its source constant `40*n^2/h₀` has the explicit
first-cell hypothesis `h₀/4 ≤ meshCellLength mesh 0`. This file does not construct
the manuscript's logarithmic mesh or prove that hypothesis for it. RMS defects,
affine graphs, compiler accuracy and work bounds are outside its scope.
-/

noncomputable section

/- ReciprocalMoment -/

open Polynomial MeasureTheory
open scoped BigOperators


namespace AcceleratedLogConcave.Numerics.ReciprocalQuadrature
open AcceleratedLogConcave.Numerics.GaussLegendre

/-- The actual polynomial quotient from the source reciprocal-node identity. -/
noncomputable def endpointQuotient (n : ℕ) : Polynomial ℝ :=
  (1 - legendre n) / Polynomial.X

theorem X_mul_endpointQuotient (n : ℕ) :
    Polynomial.X * endpointQuotient n = 1 - legendre n := by
  unfold endpointQuotient
  apply EuclideanDomain.mul_div_cancel' Polynomial.X_ne_zero
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
  simp

theorem degree_endpointQuotient_lt (n : ℕ) :
    (endpointQuotient n).degree < n := by
  by_cases hn : n = 0
  · simp [hn, endpointQuotient]
  have hd : (1 - legendre n).degree = n := by
    rw [degree_sub_eq_right_of_degree_lt]
    · exact degree_legendre n
    · rw [degree_one, degree_legendre]
      exact_mod_cast Nat.pos_of_ne_zero hn
  have hne : 1 - legendre n ≠ 0 := by
    intro h
    simp [h] at hd
  exact (Polynomial.degree_div_lt hne (by simp : 0 < (X : ℝ[X]).degree)).trans_eq hd

theorem endpointQuotient_eval_zero (n : ℕ) :
    (endpointQuotient n).eval 0 = (n : ℝ) * (n + 1 : ℝ) := by
  have h := congrArg (fun p : ℝ[X] ↦ p.derivative.eval 0) (X_mul_endpointQuotient n)
  simp [derivative_mul] at h
  nlinarith

theorem endpointQuotient_eval_of_ne_zero (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    (endpointQuotient n).eval x = (1 - (legendre n).eval x) / x := by
  apply (eq_div_iff hx).mpr
  have h := congrArg (Polynomial.eval x) (X_mul_endpointQuotient n)
  simpa only [eval_mul, eval_X, eval_sub, eval_one, mul_comm] using h

theorem integral_endpointQuotient_sq (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ((endpointQuotient n).eval x)^2) =
      2 * (n : ℝ) * (n + 1 : ℝ) := by
  let R := endpointQuotient n
  let F : ℝ[X] := 2 * R - X * R^2
  have hXR : X * R = 1 - legendre n := X_mul_endpointQuotient n
  have hF : F.derivative = 2 * legendre n * R.derivative - R^2 := by
    simp only [F, derivative_sub, derivative_mul, derivative_ofNat, derivative_X,
      derivative_pow, zero_mul, one_mul, zero_add, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, C_ofNat]
    linear_combination -(2 * R.derivative) * hXR
  have hF0 : F.eval 0 = 2 * (n : ℝ) * (n + 1 : ℝ) := by
    simp [F, R, endpointQuotient_eval_zero]
    ring
  have hR1 : R.eval 1 = 1 - (-1 : ℝ)^n := by
    simpa using congrArg (Polynomial.eval 1) hXR
  have hs : ((-1 : ℝ)^n)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have hF1 : F.eval 1 = 0 := by
    simp only [F, eval_sub, eval_mul, eval_ofNat, eval_X, eval_pow, one_mul, hR1]
    nlinarith
  have horth : (∫ x in (0 : ℝ)..1,
      (legendre n).eval x * R.derivative.eval x) = 0 :=
    integral_legendre_mul_eq_zero n R.derivative
      (degree_derivative_le.trans_lt (degree_endpointQuotient_lt n))
  have hi : IntervalIntegrable
      (fun x ↦ (legendre n).eval x * R.derivative.eval x) volume 0 1 :=
    ((legendre n).continuous.mul R.derivative.continuous).intervalIntegrable 0 1
  have hFTC : (∫ x in (0 : ℝ)..1, F.derivative.eval x) = F.eval 1 - F.eval 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ F.hasDerivAt x)
      (F.derivative.continuous.intervalIntegrable 0 1)
  rw [hF] at hFTC
  simp only [eval_sub, eval_mul, eval_ofNat, eval_pow, mul_assoc] at hFTC
  rw [intervalIntegral.integral_sub
      (f := fun x ↦ 2 * ((legendre n).eval x * R.derivative.eval x))
      (g := fun x ↦ (R.eval x)^2) (hi.const_mul 2)
      ((R.continuous.pow 2).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, horth, hF1, hF0] at hFTC
  dsimp only [R] at hFTC
  linarith

theorem sum_weight_div_node_sq (n : ℕ) :
    (∑ i : Fin n, weight n i / (node n i)^2) =
      2 * (n : ℝ) * (n + 1 : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hrne : endpointQuotient n ≠ 0 := by
    intro h
    have he := endpointQuotient_eval_zero n
    rw [h, eval_zero] at he
    have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    nlinarith
  have hd : ((endpointQuotient n)^2).degree < (2*n : ℕ) := by
    rw [degree_pow, degree_eq_natDegree hrne, two_nsmul]
    have hnat : (endpointQuotient n).natDegree < n :=
      (natDegree_lt_iff_degree_lt hrne).mpr (degree_endpointQuotient_lt n)
    exact_mod_cast (show (endpointQuotient n).natDegree +
      (endpointQuotient n).natDegree < 2*n by omega)
  have h := integral_eq_sum n ((endpointQuotient n)^2) hd
  have hv (i : Fin n) : (endpointQuotient n).eval (node n i) = 1 / node n i := by
    rw [endpointQuotient_eval_of_ne_zero n _ (node_mem_Ioo n i).1.ne', legendre_eval_node]
    simp
  simp only [eval_pow, integral_endpointQuotient_sq, hv, div_pow, one_pow] at h
  simpa only [div_eq_mul_inv, one_mul] using h.symm

end AcceleratedLogConcave.Numerics.ReciprocalQuadrature

/- ReciprocalCertificate -/

/-!
# A polynomial certificate below the reciprocal square

For any finite family of positive nodes, a polynomial of degree less than twice
the family size interpolates the reciprocal square and lies below it on the
positive half-line. Repeated nodes are allowed. The construction normalizes the
nodal product to one at zero and removes the constant and linear coefficients
before dividing by `X^2`.
-/

open Polynomial
open scoped BigOperators

namespace AcceleratedLogConcave.Numerics.ReciprocalQuadrature

private theorem natDegree_one_sub_C_mul_X_le (r : ℝ) :
    (1 - C r * X : Polynomial ℝ).natDegree ≤ 1 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · simpa using (natDegree_C_mul_X_pow_le r 1)

/-- An actual polynomial certificate for reciprocal-square underintegration.
No separation or ordering of the positive nodes is required. -/
private theorem exists_reciprocal_sq_certificate {n : ℕ} (t : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) :
    ∃ H : Polynomial ℝ, H.degree < (2 * n : ℕ) ∧
      (∀ i, H.eval (t i) = 1 / (t i)^2) ∧
      (∀ x : ℝ, 0 < x → H.eval x ≤ 1 / x^2) := by
  classical
  rcases n.eq_zero_or_pos with rfl | hn
  · refine ⟨0, by simp, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro x hx
      simp only [eval_zero]
      positivity
  let L : Polynomial ℝ := ∏ i : Fin n, (1 - C (1 / t i) * X)
  have hL0 : L.eval 0 = 1 := by simp [L, eval_prod]
  have hLt (i : Fin n) : L.eval (t i) = 0 := by
    dsimp [L]
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [(ht i).ne']
  let s : ℝ := L.derivative.eval 0
  have hs_eq : s = -(∑ i : Fin n, 1 / t i) := by
    simp [s, L, derivative_prod_finset, derivative_mul, eval_finsetSum, eval_prod,
      Finset.sum_neg_distrib]
  have hs : s ≤ 0 := by
    rw [hs_eq]
    exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ => (one_div_pos.mpr (ht i)).le)
  let N : Polynomial ℝ := 1 - L^2 * (1 - C (2 * s) * X)
  have hN0 : N.eval 0 = 0 := by simp [N, hL0]
  have hNd0 : N.derivative.eval 0 = 0 := by
    simp [N, derivative_mul, derivative_pow, hL0, s]
  have hdvd : (X : Polynomial ℝ)^2 ∣ N := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    interval_cases k
    · simpa only [coeff_zero_eq_eval_zero] using hN0
    · simpa only [← coeff_zero_eq_eval_zero, coeff_derivative, Nat.cast_zero, Nat.cast_one,
        zero_add, mul_one] using hNd0
  let H : Polynomial ℝ := N /ₘ X^2
  have hH : N = X^2 * H := by
    obtain ⟨p, hp⟩ := hdvd
    dsimp [H]
    rw [hp, mul_divByMonic_cancel_left p (monic_X.pow 2)]
  have hdegL : L.natDegree ≤ n := by
    calc
      L.natDegree ≤ ∑ i : Fin n, (1 - C (1 / t i) * X : Polynomial ℝ).natDegree :=
        natDegree_prod_le Finset.univ _
      _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => natDegree_one_sub_C_mul_X_le _
      _ = n := by simp
  have hdegN : N.natDegree ≤ 2 * n + 1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact natDegree_mul_le.trans (add_le_add
        (natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hdegL))
        (natDegree_one_sub_C_mul_X_le (2 * s)))
  have hdegH : H.natDegree < 2 * n := by
    dsimp [H]
    rw [natDegree_divByMonic N (monic_X.pow 2), natDegree_X_pow]
    omega
  have heval (x : ℝ) : x^2 * H.eval x = 1 - (L.eval x)^2 * (1 - 2 * s * x) := by
    have he := congrArg (Polynomial.eval x) hH.symm
    simpa [N] using he
  refine ⟨H, degree_le_natDegree.trans_lt (by exact_mod_cast hdegH), ?_, ?_⟩
  · intro i
    have he := heval (t i)
    rw [hLt, zero_pow (by decide : 2 ≠ 0)] at he
    have ht2 : (t i)^2 ≠ 0 := pow_ne_zero _ (ht i).ne'
    apply (eq_div_iff ht2).mpr
    nlinarith [he]
  · intro x hx
    have hcoef : 0 ≤ 1 - 2 * s * x := by nlinarith [mul_nonpos_of_nonpos_of_nonneg hs hx.le]
    have herr : 0 ≤ (L.eval x)^2 * (1 - 2 * s * x) := mul_nonneg (sq_nonneg _) hcoef
    apply (le_div_iff₀ (sq_pos_of_pos hx)).mpr
    nlinarith [heval x]

end AcceleratedLogConcave.Numerics.ReciprocalQuadrature

/- ReciprocalCell -/

open Polynomial MeasureTheory
open scoped BigOperators

namespace AcceleratedLogConcave.Numerics.ReciprocalQuadrature
open AcceleratedLogConcave.Numerics.GaussLegendre

/-- The actual signed Gauss-Legendre coefficient mass on a physical cell. -/
noncomputable def reciprocalCellMass (n : ℕ) (a h : ℝ) : ℝ :=
  ∑ i : Fin n, cellWeight n h i / (cellNode n a h i)^2

private theorem inverse_sq_intervalIntegrable (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    IntervalIntegrable (fun x : ℝ ↦ 1 / x^2) volume a (a + h) := by
  apply intervalIntegral.intervalIntegrable_one_div
  · intro x hx
    rw [Set.uIcc_of_le (by linarith : a ≤ a + h)] at hx
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le ha hx.1))
  · exact (continuous_id.pow 2).continuousOn

/-- The integral is finite because the whole physical cell lies strictly above zero. -/
private theorem integral_inverse_sq (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    (∫ x in a..a+h, 1 / x^2) = 1 / a - 1 / (a + h) := by
  have hd : ∀ x ∈ Set.uIcc a (a + h),
      HasDerivAt (fun y : ℝ ↦ -y⁻¹) (1 / x^2) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : a ≤ a + h)] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
    convert! (hasDerivAt_inv hx0).neg using 1
    simp [one_div]
  calc
    (∫ x in a..a+h, 1 / x^2) = -(a + h)⁻¹ - -a⁻¹ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (inverse_sq_intervalIntegrable a h ha hh)
    _ = 1 / a - 1 / (a + h) := by simp only [one_div]; ring

private theorem reciprocalCellMass_le_integral_of_certificate (n : ℕ) (a h : ℝ)
    (ha : 0 < a) (hh : 0 < h) (H : Polynomial ℝ)
    (hdeg : H.degree < (2 * n : ℕ))
    (hnodes : ∀ i, H.eval (cellNode n a h i) = 1 / (cellNode n a h i)^2)
    (hbound : ∀ x : ℝ, 0 < x → H.eval x ≤ 1 / x^2) :
    reciprocalCellMass n a h ≤ ∫ ρ in a..a+h, 1 / ρ^2 := by
  have hmass : reciprocalCellMass n a h = ∫ ρ in a..a+h, H.eval ρ := by
    rw [integral_cell_eq_sum n a h hh H hdeg]
    simp only [reciprocalCellMass, hnodes, mul_one_div]
  rw [hmass]
  apply intervalIntegral.integral_mono_on (by linarith : a ≤ a + h)
    (H.continuous.intervalIntegrable a (a + h)) (inverse_sq_intervalIntegrable a h ha hh)
  intro x hx
  exact hbound x (lt_of_lt_of_le ha hx.1)

/-- On a cell strictly above zero, Gauss-Legendre underintegrates the reciprocal square.
The minorant is constructed from the actual positive physical nodes. -/
theorem reciprocalCellMass_le_integral (n : ℕ) (a h : ℝ)
    (ha : 0 < a) (hh : 0 < h) :
    reciprocalCellMass n a h ≤ ∫ ρ in a..a+h, 1 / ρ^2 := by
  have hnodes : ∀ i : Fin n, 0 < cellNode n a h i := by
    intro i
    exact lt_trans ha (cellNode_mem_Ioo n a h hh i).1
  obtain ⟨H, hdeg, hvalues, hbound⟩ :=
    exists_reciprocal_sq_certificate (cellNode n a h) hnodes
  exact reciprocalCellMass_le_integral_of_certificate n a h ha hh H hdeg hvalues hbound

/-- The inverse-square integral telescopes to the difference of the endpoint reciprocals. -/
theorem reciprocalCellMass_le_reciprocal_difference (n : ℕ) (a h : ℝ)
    (ha : 0 < a) (hh : 0 < h) :
    reciprocalCellMass n a h ≤ 1 / a - 1 / (a + h) := by
  rw [← integral_inverse_sq a h ha hh]
  exact reciprocalCellMass_le_integral n a h ha hh

end AcceleratedLogConcave.Numerics.ReciprocalQuadrature

/- ReciprocalFirst -/

open Polynomial MeasureTheory
open scoped BigOperators

namespace AcceleratedLogConcave.Numerics.ReciprocalQuadrature
open AcceleratedLogConcave.Numerics.GaussLegendre

theorem reciprocalCellMass_first (n : ℕ) (h : ℝ) (hh : 0 < h) :
    reciprocalCellMass n 0 h = 2 * (n : ℝ) * (n + 1 : ℝ) / h := by
  unfold reciprocalCellMass
  calc
    (∑ i : Fin n, cellWeight n h i / (cellNode n 0 h i)^2) =
        (∑ i : Fin n, weight n i / (node n i)^2) / h := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [cellWeight, cellNode]
      field_simp [ne_of_gt hh, ne_of_gt (node_mem_Ioo n i).1]
      ring
    _ = 2 * (n : ℝ) * (n + 1 : ℝ) / h := by rw [sum_weight_div_node_sq]

end AcceleratedLogConcave.Numerics.ReciprocalQuadrature

/- ReciprocalMesh -/

open Polynomial MeasureTheory
open scoped BigOperators

namespace AcceleratedLogConcave.Numerics.ReciprocalQuadrature
open AcceleratedLogConcave.Numerics.GaussLegendre

def meshCellLeft {k : ℕ} (mesh : Fin (k + 2) → ℝ) (c : Fin (k + 1)) : ℝ :=
  mesh c.castSucc

def meshCellLength {k : ℕ} (mesh : Fin (k + 2) → ℝ) (c : Fin (k + 1)) : ℝ :=
  mesh c.succ - mesh c.castSucc

def meshHorizon {k : ℕ} (mesh : Fin (k + 2) → ℝ) : ℝ :=
  mesh (Fin.last (k + 1))

noncomputable def kernelNodeCoefficient (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ) (z : Fin (k + 1) × Fin n) : ℝ :=
  cellWeight n (meshCellLength mesh z.1) z.2 /
    (cellNode n (meshCellLeft mesh z.1) (meshCellLength mesh z.1) z.2)^2

noncomputable def kernelValueLocation (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ) : Option (Fin (k + 1) × Fin n) → ℝ
  | none => 0
  | some z => cellNode n (meshCellLeft mesh z.1) (meshCellLength mesh z.1) z.2

noncomputable def kernelValueCoefficient (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ) : Option (Fin (k + 1) × Fin n) → ℝ
  | none => -1 / meshHorizon mesh - ∑ z, kernelNodeCoefficient n mesh z
  | some z => kernelNodeCoefficient n mesh z

private theorem meshCellLength_pos {k : ℕ} (mesh : Fin (k + 2) → ℝ)
    (hmesh : StrictMono mesh) (c : Fin (k + 1)) :
    0 < meshCellLength mesh c :=
  sub_pos.mpr (hmesh c.castSucc_lt_succ)

private theorem meshCellLeft_nonneg {k : ℕ} (mesh : Fin (k + 2) → ℝ)
    (hmesh : StrictMono mesh) (hzero : mesh 0 = 0) (c : Fin (k + 1)) :
    0 ≤ meshCellLeft mesh c := by
  rw [meshCellLeft, ← hzero]
  exact hmesh.monotone (Fin.zero_le _)

private theorem meshHorizon_pos {k : ℕ} (mesh : Fin (k + 2) → ℝ)
    (hmesh : StrictMono mesh) (hzero : mesh 0 = 0) :
    0 < meshHorizon mesh := by
  rw [meshHorizon, ← hzero]
  exact hmesh (by change (0 : ℕ) < k + 1; omega)

private theorem meshCellLeft_succ_pos {k : ℕ} (mesh : Fin (k + 2) → ℝ)
    (hmesh : StrictMono mesh) (hzero : mesh 0 = 0) (c : Fin k) :
    0 < meshCellLeft mesh c.succ := by
  rw [meshCellLeft, ← hzero]
  exact hmesh (by change (0 : ℕ) < c.val + 1; omega)

private theorem meshNode_pos (n : ℕ) {k : ℕ} (mesh : Fin (k + 2) → ℝ)
    (hmesh : StrictMono mesh) (hzero : mesh 0 = 0)
    (c : Fin (k + 1)) (i : Fin n) :
    0 < cellNode n (meshCellLeft mesh c) (meshCellLength mesh c) i :=
  lt_of_le_of_lt (meshCellLeft_nonneg mesh hmesh hzero c)
    (cellNode_mem_Ioo n _ _ (meshCellLength_pos mesh hmesh c) i).1

private theorem meshNode_lt_of_cell_lt (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ) (hmesh : StrictMono mesh)
    {c d : Fin (k + 1)} (hcd : c < d) (i j : Fin n) :
    cellNode n (meshCellLeft mesh c) (meshCellLength mesh c) i <
      cellNode n (meshCellLeft mesh d) (meshCellLength mesh d) j := by
  have hi := (cellNode_mem_Ioo n (meshCellLeft mesh c) _
    (meshCellLength_pos mesh hmesh c) i).2
  have hj := (cellNode_mem_Ioo n (meshCellLeft mesh d) _
    (meshCellLength_pos mesh hmesh d) j).1
  have hbd : mesh c.succ ≤ mesh d.castSucc := by
    apply hmesh.monotone
    change c.val + 1 ≤ d.val
    exact hcd
  simp only [meshCellLeft, meshCellLength] at hi hj ⊢
  linarith

private theorem meshNode_injective (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ) (hmesh : StrictMono mesh) :
    Function.Injective (fun z : Fin (k + 1) × Fin n =>
      cellNode n (meshCellLeft mesh z.1) (meshCellLength mesh z.1) z.2) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ he
  have hcd : c = d := by
    rcases lt_trichotomy c d with h | h | h
    · have hn := meshNode_lt_of_cell_lt n mesh hmesh h i j
      exact False.elim ((ne_of_lt hn) he)
    · exact h
    · have hn := meshNode_lt_of_cell_lt n mesh hmesh h j i
      exact False.elim ((ne_of_lt hn) he.symm)
  subst d
  have hij := (cellNode_strictMono n _ _ (meshCellLength_pos mesh hmesh c)).injective he
  change i = j at hij
  subst j
  rfl

theorem kernelValueLocation_injective (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ)
    (hmesh : StrictMono mesh) (hzero : mesh 0 = 0) :
  Function.Injective (kernelValueLocation n mesh) := by
  intro x y he
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some z =>
          have hp := meshNode_pos n mesh hmesh hzero z.1 z.2
          change 0 = cellNode n (meshCellLeft mesh z.1) (meshCellLength mesh z.1) z.2 at he
          exact False.elim ((ne_of_gt hp) he.symm)
  | some z =>
      cases y with
      | none =>
          have hp := meshNode_pos n mesh hmesh hzero z.1 z.2
          exact False.elim ((ne_of_gt hp) he)
      | some w =>
          exact congrArg some (meshNode_injective n mesh hmesh he)

theorem kernelValueCoefficient_apply (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ) (f : ℝ → ℝ) :
  (∑ z, kernelValueCoefficient n mesh z * f (kernelValueLocation n mesh z)) =
    -f 0 / meshHorizon mesh +
      ∑ z, kernelNodeCoefficient n mesh z *
        (f (kernelValueLocation n mesh (some z)) - f 0) := by
  rw [Fintype.sum_option]
  simp only [kernelValueCoefficient, kernelValueLocation, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  ring

private theorem kernelNodeCoefficient_nonneg (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ) (hmesh : StrictMono mesh)
    (z : Fin (k + 1) × Fin n) : 0 ≤ kernelNodeCoefficient n mesh z := by
  exact div_nonneg (cellWeight_nonneg n _ _ (meshCellLength_pos mesh hmesh z.1).le)
    (sq_nonneg _)

theorem sum_abs_kernelValueCoefficient_eq (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ)
    (hmesh : StrictMono mesh) (hzero : mesh 0 = 0) :
  (∑ z, |kernelValueCoefficient n mesh z|) =
    1 / meshHorizon mesh + 2 * ∑ z, kernelNodeCoefficient n mesh z := by
  have hb := meshHorizon_pos mesh hmesh hzero
  have hs : 0 ≤ ∑ z, kernelNodeCoefficient n mesh z :=
    Finset.sum_nonneg (fun z _ => kernelNodeCoefficient_nonneg n mesh hmesh z)
  have hnone : -1 / meshHorizon mesh - ∑ z, kernelNodeCoefficient n mesh z ≤ 0 := by
    have hi : 0 < 1 / meshHorizon mesh := one_div_pos.mpr hb
    rw [neg_div]
    linarith
  rw [Fintype.sum_option]
  simp only [kernelValueCoefficient, abs_of_nonpos hnone,
    abs_of_nonneg (kernelNodeCoefficient_nonneg n mesh hmesh _)]
  ring

private theorem sum_adjacent_sub {k : ℕ} (f : Fin (k + 1) → ℝ) :
    (∑ i : Fin k, (f i.castSucc - f i.succ)) = f 0 - f (Fin.last k) := by
  have hfirst := Fin.sum_univ_succ f
  have hlast := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib]
  linarith

private theorem sum_later_reciprocal_difference {k : ℕ}
    (mesh : Fin (k + 2) → ℝ) (hzero : mesh 0 = 0) :
    (∑ c : Fin k, (1 / meshCellLeft mesh c.succ -
      1 / (meshCellLeft mesh c.succ + meshCellLength mesh c.succ))) =
      1 / meshCellLength mesh 0 - 1 / meshHorizon mesh := by
  have h := sum_adjacent_sub (fun i : Fin (k + 1) => 1 / mesh i.succ)
  simpa [meshCellLeft, meshCellLength, meshHorizon, Fin.castSucc_succ, hzero] using h

theorem sum_kernelNodeCoefficient_le (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ)
    (hmesh : StrictMono mesh) (hzero : mesh 0 = 0) :
  (∑ z, kernelNodeCoefficient n mesh z) ≤
    (2 * (n : ℝ) * (n + 1 : ℝ) + 1) / meshCellLength mesh 0 -
      1 / meshHorizon mesh := by
  have hfirst : reciprocalCellMass n (meshCellLeft mesh 0) (meshCellLength mesh 0) =
      2 * (n : ℝ) * (n + 1 : ℝ) / meshCellLength mesh 0 := by
    have hz : meshCellLeft mesh 0 = 0 := hzero
    rw [hz]
    exact reciprocalCellMass_first n _ (meshCellLength_pos mesh hmesh 0)
  have hlater :
      (∑ c : Fin k, reciprocalCellMass n (meshCellLeft mesh c.succ)
        (meshCellLength mesh c.succ)) ≤
      1 / meshCellLength mesh 0 - 1 / meshHorizon mesh := by
    calc
      _ ≤ ∑ c : Fin k, (1 / meshCellLeft mesh c.succ -
          1 / (meshCellLeft mesh c.succ + meshCellLength mesh c.succ)) := by
        apply Finset.sum_le_sum
        intro c _
        exact reciprocalCellMass_le_reciprocal_difference n _ _
          (meshCellLeft_succ_pos mesh hmesh hzero c)
          (meshCellLength_pos mesh hmesh c.succ)
      _ = _ := sum_later_reciprocal_difference mesh hzero
  rw [Fintype.sum_prod_type]
  change (∑ c : Fin (k + 1), reciprocalCellMass n (meshCellLeft mesh c)
    (meshCellLength mesh c)) ≤ _
  rw [Fin.sum_univ_succ, hfirst]
  calc
    _ ≤ 2 * (n : ℝ) * (n + 1 : ℝ) / meshCellLength mesh 0 +
        (1 / meshCellLength mesh 0 - 1 / meshHorizon mesh) := by linarith
    _ = _ := by ring

theorem sum_abs_kernelValueCoefficient_le_firstCell (n : ℕ) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ)
    (hmesh : StrictMono mesh) (hzero : mesh 0 = 0) :
  (∑ z, |kernelValueCoefficient n mesh z|) ≤
    (4 * (n : ℝ) * (n + 1 : ℝ) + 2) / meshCellLength mesh 0 -
      1 / meshHorizon mesh := by
  rw [sum_abs_kernelValueCoefficient_eq n mesh hmesh hzero]
  have hs := sum_kernelNodeCoefficient_le n mesh hmesh hzero
  calc
    _ ≤ 1 / meshHorizon mesh +
        2 * ((2 * (n : ℝ) * (n + 1 : ℝ) + 1) / meshCellLength mesh 0 -
          1 / meshHorizon mesh) := by linarith
    _ = _ := by ring

private theorem first_length_mass_bound (n : ℕ) (hn : 2 ≤ n) {ell b h₀ : ℝ}
    (hb : 0 < b) (hh₀ : 0 < h₀) (hfirst : h₀ / 4 ≤ ell) :
    (4 * (n : ℝ) * (n + 1 : ℝ) + 2) / ell - 1 / b ≤ 40 * (n : ℝ)^2 / h₀ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnum : 0 ≤ 4 * (n : ℝ) * (n + 1 : ℝ) + 2 := by positivity
  have hsmall : 0 < h₀ / 4 := by positivity
  calc
    (4 * (n : ℝ) * (n + 1 : ℝ) + 2) / ell - 1 / b ≤
        (4 * (n : ℝ) * (n + 1 : ℝ) + 2) / ell :=
      sub_le_self _ (one_div_nonneg.mpr hb.le)
    _ ≤ (4 * (n : ℝ) * (n + 1 : ℝ) + 2) / (h₀ / 4) :=
      div_le_div_of_nonneg_left hnum hsmall hfirst
    _ = (16 * (n : ℝ) * (n + 1 : ℝ) + 8) / h₀ := by ring
    _ ≤ 40 * (n : ℝ)^2 / h₀ := by
      apply div_le_div_of_nonneg_right _ hh₀.le
      nlinarith

theorem sum_abs_kernelValueCoefficient_le (n : ℕ) (hn : 2 ≤ n) {k : ℕ}
    (mesh : Fin (k + 2) → ℝ)
    (hmesh : StrictMono mesh) (hzero : mesh 0 = 0)
    (h₀ : ℝ) (hh₀ : 0 < h₀)
    (hfirst : h₀ / 4 ≤ meshCellLength mesh 0) :
  (∑ z, |kernelValueCoefficient n mesh z|) ≤ 40 * (n : ℝ)^2 / h₀ := by
  exact le_trans (sum_abs_kernelValueCoefficient_le_firstCell n mesh hmesh hzero)
    (first_length_mass_bound n hn (meshHorizon_pos mesh hmesh hzero) hh₀ hfirst)

end AcceleratedLogConcave.Numerics.ReciprocalQuadrature

end
