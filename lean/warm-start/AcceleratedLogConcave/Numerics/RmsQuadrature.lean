import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

/-!
# Banach / RMS Taylor remainder and oriented value quadrature
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace AcceleratedLogConcave.Numerics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual degree-at-most `m-1` Taylor polynomial. -/
def taylorPolynomial (f : ℝ → E) (m : ℕ) (a x : ℝ) : E :=
  ∑ k ∈ Finset.range m, ((x-a)^k / (k.factorial : ℝ)) • iteratedDeriv k f a

private theorem integral_one_sub_pow (n : ℕ) :
    (∫ t : ℝ in 0..1, (1-t)^n) = 1 / (n+1 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^n) 1]
  simp [integral_pow]

/-- Sharp Banach Taylor estimate with the source's exact `m!` denominator.
Smoothness is at every point of the deterministic cell, including endpoints. -/
theorem norm_sub_taylorPolynomial_le {f : ℝ → E} {a b x D : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hx : x ∈ Icc a b)
    (hf : ∀ t ∈ Icc a b, ContDiffAt ℝ m f t)
    (hD : ∀ t ∈ Icc a b, ‖iteratedDeriv m f t‖ ≤ D) :
    ‖f x - taylorPolynomial f m a x‖ ≤ D * (x-a)^m / (m.factorial : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hxa : 0 ≤ x-a := sub_nonneg.mpr hx.1
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t*(x-a) ∈ Icc a b := by
    intro t ht
    constructor
    · nlinarith [mul_nonneg ht.1 hxa]
    · calc
        a + t*(x-a) ≤ a + 1*(x-a) := add_le_add_right (mul_le_mul_of_nonneg_right ht.2 hxa) _
        _ = x := by ring
        _ ≤ b := hx.2
  have hexp := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := a) (y := x-a) (n := n)
    (fun t ht => hf _ (by simpa [smul_eq_mul] using hseg t ht))
  have heq : f x = taylorPolynomial f (n+1) a x +
      (n.factorial : ℝ)⁻¹ • ∫ t : ℝ in 0..1,
        (1-t)^n • ((x-a)^(n+1) • iteratedDeriv (n+1) f (a+t*(x-a))) := by
    simpa [taylorPolynomial, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      smul_smul, div_eq_mul_inv, mul_comm, smul_eq_mul] using hexp
  have hi : ‖∫ t : ℝ in 0..1,
        (1-t)^n • ((x-a)^(n+1) • iteratedDeriv (n+1) f (a+t*(x-a)))‖ ≤
      (∫ t : ℝ in 0..1, (1-t)^n * ((x-a)^(n+1)*D)) := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · filter_upwards [] with t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) n),
        abs_of_nonneg (pow_nonneg hxa (n+1))]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hD _ (hseg t ht')) (pow_nonneg hxa _))
        (pow_nonneg (sub_nonneg.mpr ht.2) _)
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        (1-t)^n * ((x-a)^(n+1)*D))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_mul_const, integral_one_sub_pow] at hi
  rw [heq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < n.factorial))]
  calc
    (n.factorial : ℝ)⁻¹ * ‖∫ t : ℝ in 0..1,
        (1-t)^n • ((x-a)^(n+1) • iteratedDeriv (n+1) f (a+t*(x-a)))‖
      ≤ (n.factorial : ℝ)⁻¹ * ((1/(n+1 : ℝ))*((x-a)^(n+1)*D)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = D*(x-a)^(n+1)/((n+1).factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
      


/-- An actual oriented finite value row. Its coefficients need not be positive. -/
structure ValueRow (ι : Type*) where
  node : ι → ℝ
  weight : ι → ℝ
  start : ℝ
  finish : ℝ

namespace ValueRow
variable {ι : Type*} [Fintype ι]

/-- The actual finite linear combination of sampled values. -/
def evaluate (row : ValueRow ι) (f : ℝ → E) : E := ∑ j, row.weight j • f (row.node j)

def mass (row : ValueRow ι) : ℝ := ∑ j, |row.weight j|

/-- Scalar monomial reproduction, an independently checkable rule interface. -/
def Exact (row : ValueRow ι) (kernel : ℝ → ℝ) (a : ℝ) (m : ℕ) : Prop :=
  ∀ k < m, (∫ t in row.start..row.finish, kernel t * (t-a)^k) =
    ∑ j, row.weight j * (row.node j-a)^k

def reverse (row : ValueRow ι) : ValueRow ι :=
  ⟨row.node, fun j => -row.weight j, row.finish, row.start⟩

@[simp] theorem mass_reverse (row : ValueRow ι) : row.reverse.mass = row.mass := by
  simp [mass, reverse]

omit [CompleteSpace E] in
@[simp] theorem evaluate_reverse (row : ValueRow ι) (f : ℝ → E) :
    row.reverse.evaluate f = -row.evaluate f := by simp [evaluate, reverse]

theorem exact_reverse (row : ValueRow ι) {kernel : ℝ → ℝ} {a : ℝ} {m : ℕ}
    (h : row.Exact kernel a m) : row.reverse.Exact kernel a m := by
  intro k hk
  change (∫ t in row.finish..row.start, kernel t * (t-a)^k) =
    ∑ j, (-row.weight j) * (row.node j-a)^k
  rw [intervalIntegral.integral_symm, h k hk]
  simp only [neg_mul, Finset.sum_neg_distrib]

/-- Monomial reproduction extends to genuine Banach-valued polynomials. -/
theorem exact_polynomial (row : ValueRow ι) {kernel : ℝ → ℝ} {a : ℝ} {m : ℕ}
    (h : row.Exact kernel a m)
    (hi : IntervalIntegrable kernel volume row.start row.finish) (c : ℕ → E) :
    (∫ t in row.start..row.finish, kernel t • (∑ k ∈ Finset.range m, (t-a)^k • c k)) =
      row.evaluate (fun t => ∑ k ∈ Finset.range m, (t-a)^k • c k) := by
  simp only [Finset.smul_sum, smul_smul, evaluate]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (hi.mul_continuousOn (show ContinuousOn (fun t : ℝ => (t-a)^k) _ by fun_prop)).smul_continuousOn
      (show ContinuousOn (fun _ : ℝ => c k) _ from continuousOn_const))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_smul_const, h k (Finset.mem_range.mp hk), Finset.sum_smul]


/-- In particular, the actual Taylor polynomial cancels exactly. -/
theorem exact_taylorPolynomial (row : ValueRow ι) {kernel : ℝ → ℝ} {a : ℝ} {m : ℕ}
    (h : row.Exact kernel a m)
    (hi : IntervalIntegrable kernel volume row.start row.finish) (f : ℝ → E) :
    (∫ t in row.start..row.finish, kernel t • taylorPolynomial f m a t) =
      row.evaluate (taylorPolynomial f m a) := by
  simpa [evaluate, taylorPolynomial, div_eq_mul_inv, mul_smul] using
    row.exact_polynomial h hi (fun k => (k.factorial : ℝ)⁻¹ • iteratedDeriv k f a)

omit [CompleteSpace E] in
/-- Absolute coefficient mass controls the actual sampled-value linear map. -/
theorem norm_evaluate_le (row : ValueRow ι) {f : ℝ → E} {M : ℝ}
    (hf : ∀ j, ‖f (row.node j)‖ ≤ M) : ‖row.evaluate f‖ ≤ row.mass * M := by
  calc
    ‖row.evaluate f‖ ≤ ∑ j, ‖row.weight j • f (row.node j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, |row.weight j| * M := Finset.sum_le_sum (fun j _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf j) (abs_nonneg _))
    _ = row.mass * M := by rw [mass, Finset.sum_mul]

omit [CompleteSpace E] in
/-- A polynomial cancellation estimate for the actual oriented integral.
The later Taylor theorem supplies the remainder bound from derivatives. -/
theorem norm_defect_le_of_remainder (row : ValueRow ι)
    {kernel : ℝ → ℝ} {f P : ℝ → E} {a b M : ℝ}
    (hu : row.start ∈ Icc a b) (hv : row.finish ∈ Icc a b)
    (hn : ∀ j, row.node j ∈ Icc a b)
    (hk : ∀ t ∈ uIcc row.start row.finish, |kernel t| ≤ 1)
    (hmass : row.mass ≤ b-a) (hM : 0 ≤ M)
    (hf : IntervalIntegrable (fun t => kernel t • f t) volume row.start row.finish)
    (hP : IntervalIntegrable (fun t => kernel t • P t) volume row.start row.finish)
    (hex : (∫ t in row.start..row.finish, kernel t • P t) = row.evaluate P)
    (hrem : ∀ t ∈ Icc a b, ‖f t-P t‖ ≤ M) :
    ‖(∫ t in row.start..row.finish, kernel t • f t) - row.evaluate f‖ ≤
      2*(b-a)*M := by
  have hseg : uIcc row.start row.finish ⊆ Icc a b := by
    intro t ht
    exact ⟨(le_min hu.1 hv.1).trans ht.1, ht.2.trans (max_le hu.2 hv.2)⟩
  have hlength : |row.finish-row.start| ≤ b-a := abs_sub_le_iff.mpr
    ⟨by linarith [hv.2, hu.1], by linarith [hu.2, hv.1]⟩
  have hInt : ‖∫ t in row.start..row.finish, kernel t • (f t-P t)‖ ≤ M*(b-a) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans
      (mul_le_mul_of_nonneg_left hlength hM)
    intro t ht
    have ht' : t ∈ uIcc row.start row.finish := ⟨le_of_lt ht.1, ht.2⟩
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hk t ht') (norm_nonneg _)).trans
      (by simpa using hrem t (hseg ht'))
  have hrow : ‖row.evaluate (fun t => f t-P t)‖ ≤ (b-a)*M :=
    (row.norm_evaluate_le (fun j => hrem _ (hn j))).trans
      (mul_le_mul_of_nonneg_right hmass hM)
  have heq : (∫ t in row.start..row.finish, kernel t • f t) - row.evaluate f =
      (∫ t in row.start..row.finish, kernel t • (f t-P t)) -
        row.evaluate (fun t => f t-P t) := by
    simp only [smul_sub, intervalIntegral.integral_sub hf hP,
      evaluate, Finset.sum_sub_distrib] at hex ⊢
    rw [hex]
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith)


/-- The source's cellwise value-quadrature estimate, derived from the actual
m-th Banach derivative. The interval can have either orientation and can be a
proper subinterval of the full interpolation cell. -/
theorem norm_defect_le (row : ValueRow ι) {kernel : ℝ → ℝ} {f : ℝ → E}
    {a b D : ℝ} {m : ℕ} (hm : 1 ≤ m) (hD0 : 0 ≤ D)
    (hu : row.start ∈ Icc a b) (hv : row.finish ∈ Icc a b)
    (hn : ∀ j, row.node j ∈ Icc a b)
    (hk : ∀ t ∈ uIcc row.start row.finish, |kernel t| ≤ 1)
    (hi : IntervalIntegrable kernel volume row.start row.finish)
    (hmass : row.mass ≤ b-a) (hex : row.Exact kernel a m)
    (hf : ∀ t ∈ Icc a b, ContDiffAt ℝ m f t)
    (hD : ∀ t ∈ Icc a b, ‖iteratedDeriv m f t‖ ≤ D) :
    ‖(∫ t in row.start..row.finish, kernel t • f t) - row.evaluate f‖ ≤
      2*(b-a)^(m+1)*D / (m.factorial : ℝ) := by
  have hab : a ≤ b := hu.1.trans hu.2
  have hseg : uIcc row.start row.finish ⊆ Icc a b := by
    intro t ht
    exact ⟨(le_min hu.1 hv.1).trans ht.1, ht.2.trans (max_le hu.2 hv.2)⟩
  have hc : ContinuousOn f (uIcc row.start row.finish) :=
    fun t ht => (hf t (hseg ht)).continuousAt.continuousWithinAt
  have hp : Continuous (taylorPolynomial f m a) := by
    unfold taylorPolynomial
    fun_prop
  have hrem (t : ℝ) (ht : t ∈ Icc a b) :
      ‖f t-taylorPolynomial f m a t‖ ≤ D*(b-a)^m/(m.factorial : ℝ) := by
    apply (norm_sub_taylorPolynomial_le hm ht hf hD).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sub_nonneg.mpr ht.1) (sub_le_sub_right ht.2 a) m) hD0
  have h := row.norm_defect_le_of_remainder hu hv hn hk hmass
    (by positivity : 0 ≤ D*(b-a)^m/(m.factorial : ℝ))
    (hi.smul_continuousOn hc) (hi.smul_continuousOn hp.continuousOn)
    (row.exact_taylorPolynomial hex hi f) hrem
  convert h using 1
  ring

omit [CompleteSpace E] in
/-- Reversal negates both the exact integral and the evaluated row. -/
theorem norm_defect_reverse (row : ValueRow ι) (kernel : ℝ → ℝ) (f : ℝ → E) :
    ‖(∫ t in row.reverse.start..row.reverse.finish, kernel t • f t) -
      row.reverse.evaluate f‖ =
    ‖(∫ t in row.start..row.finish, kernel t • f t) - row.evaluate f‖ := by
  rw [evaluate_reverse]
  change ‖(∫ t in row.finish..row.start, kernel t • f t) - (-row.evaluate f)‖ = _
  rw [intervalIntegral.integral_symm, neg_sub_neg, norm_sub_rev]

end ValueRow

/-- A deterministic finite maximum of actual L2 defects has the same bound.
The hypothesis concerns the L2 norm at each deterministic time, never the L2
norm of a random maximum. No row-count factor is introduced. -/
theorem max_rms_defect_le {Ω J ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (s : Finset J) (hs : s.Nonempty)
    (rows : J → ValueRow ι) (kernel : J → ℝ → ℝ) (f : J → ℝ → Lp E 2 μ)
    {a b D : ℝ} {m : ℕ} (hm : 1 ≤ m) (hD0 : 0 ≤ D)
    (hu : ∀ j ∈ s, (rows j).start ∈ Icc a b)
    (hv : ∀ j ∈ s, (rows j).finish ∈ Icc a b)
    (hn : ∀ j ∈ s, ∀ i, (rows j).node i ∈ Icc a b)
    (hk : ∀ j ∈ s, ∀ t ∈ uIcc (rows j).start (rows j).finish, |kernel j t| ≤ 1)
    (hi : ∀ j ∈ s, IntervalIntegrable (kernel j) volume (rows j).start (rows j).finish)
    (hmass : ∀ j ∈ s, (rows j).mass ≤ b-a)
    (hex : ∀ j ∈ s, (rows j).Exact (kernel j) a m)
    (hf : ∀ j ∈ s, ∀ t ∈ Icc a b, ContDiffAt ℝ m (f j) t)
    (hD : ∀ j ∈ s, ∀ t ∈ Icc a b, ‖iteratedDeriv m (f j) t‖ ≤ D) :
    s.sup' hs (fun j =>
      ‖(∫ t in (rows j).start..(rows j).finish, kernel j t • f j t) -
        (rows j).evaluate (f j)‖) ≤ 2*(b-a)^(m+1)*D/(m.factorial : ℝ) := by
  apply Finset.sup'_le
  intro j hj
  exact (rows j).norm_defect_le hm hD0 (hu j hj) (hv j hj) (hn j hj)
    (hk j hj) (hi j hj) (hmass j hj) (hex j hj) (hf j hj) (hD j hj)

end AcceleratedLogConcave.Numerics
