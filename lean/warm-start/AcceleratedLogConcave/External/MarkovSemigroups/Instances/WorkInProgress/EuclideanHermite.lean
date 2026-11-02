/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hermite-IBP discharge of `ouSemigroup_contDiff`

This file proves `ouSemigroup_contDiff_bounded` — the C^∞ smoothing of the
Ornstein-Uhlenbeck semigroup on bounded inputs — via the Hermite
integration-by-parts identity, without reducing to a Lebesgue convolution.

## Key identity

For `f` with `ContDiff ℝ ⊤` and `f, f'` both bounded, the iterated
derivatives of `P_t f` (for `t > 0`) satisfy

  `iteratedDeriv n (P_t f) x = (a/b)^n · ∫ y, H_n(y) · f(a·x + b·y) ∂γ`

where `a = e^{-t}`, `b = √(1 − e^{-2t})`, and `H_n = aeval _ (Polynomial.hermite n)`
are the probabilist's Hermite polynomials. The proof is by induction on `n`,
each step combining
* parametric integral differentiation
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
* the Hermite integration-by-parts lemma against the Gaussian density
  (`hermite_ibp_gaussian`),
which together push the derivative from `f` onto the Hermite weight.

## Boundary cases

* `t = 0`: `b = 0`, so `P_0 f = f` and the claim is trivial.
* `t < 0`: `b = 0` (Real.sqrt of negative is 0), so `P_t f(x) = f(e^{-t}·x)`,
  trivially `C^∞`.

## References

* Bakry-Gentil-Ledoux, §2.7.1 (Mehler kernel).
* Mathlib `Polynomial.hermite`, `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`.
-/

import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.Euclidean
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open MeasureTheory Filter Set Real ProbabilityTheory Polynomial Topology

open scoped ContDiff

noncomputable section

namespace Gaussian1D

/-! ## Hermite polynomial real-valued evaluation -/

/-- Probabilist's Hermite polynomial as a function `ℝ → ℝ`. -/
def hermiteFun (n : ℕ) : ℝ → ℝ := fun y => aeval y (hermite n)

@[simp] lemma hermiteFun_zero : hermiteFun 0 = fun _ => 1 := by
  ext y; simp [hermiteFun, hermite_zero]

@[simp] lemma hermiteFun_one : hermiteFun 1 = fun y => y := by
  ext y; simp [hermiteFun]

/-- `hermiteFun n` is a polynomial function, hence `C^∞`. -/
lemma hermiteFun_contDiff (n : ℕ) : ContDiff ℝ ⊤ (hermiteFun n) :=
  Polynomial.contDiff_aeval _ _

/-- `hermiteFun n` is differentiable everywhere. -/
lemma hermiteFun_differentiable (n : ℕ) : Differentiable ℝ (hermiteFun n) :=
  (hermiteFun_contDiff n).differentiable (by simp)

/-- `hermiteFun n` is continuous. -/
lemma hermiteFun_continuous (n : ℕ) : Continuous (hermiteFun n) :=
  (hermiteFun_contDiff n).continuous

/-- `hermiteFun n` is measurable. -/
lemma hermiteFun_measurable (n : ℕ) : Measurable (hermiteFun n) :=
  (hermiteFun_continuous n).measurable

/-- The Hermite recurrence as functions: `H_{n+1}(y) = y · H_n(y) − H_n'(y)`. -/
lemma hermiteFun_succ (n : ℕ) (y : ℝ) :
    hermiteFun (n + 1) y = y * hermiteFun n y - deriv (hermiteFun n) y := by
  unfold hermiteFun
  rw [hermite_succ]
  simp [Polynomial.deriv_aeval]

/-- `deriv (hermiteFun n)` is itself a polynomial function, hence everywhere
defined and matches `aeval _ (derivative (hermite n))`. -/
lemma deriv_hermiteFun (n : ℕ) (y : ℝ) :
    deriv (hermiteFun n) y = aeval y (Polynomial.derivative (hermite n)) := by
  exact Polynomial.deriv_aeval (hermite n)

/-! ## Hermite × Gaussian PDF: derivative identity (Rodrigues) -/

/-- The standard Gaussian density `pdf(y) = (2π)^{-1/2} · exp(−y²/2)` —
short alias matching `EuclideanStein.lean`. -/
private noncomputable def pdf : ℝ → ℝ := gaussianPDFReal 0 1

private lemma pdf_def : pdf = gaussianPDFReal 0 1 := rfl

private lemma pdf_nonneg (y : ℝ) : 0 ≤ pdf y := gaussianPDFReal_nonneg _ _ _

private lemma pdf_measurable : Measurable pdf := measurable_gaussianPDFReal _ _

/-- ODE for the standard Gaussian: `pdf'(y) = −y · pdf(y)`. -/
private lemma hasDerivAt_pdf (y : ℝ) : HasDerivAt pdf (-y * pdf y) y := by
  unfold pdf gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hsq : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-y) y := by
    have h₁ : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    have h₃ : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-(2 * y) / 2) y :=
      h₁.neg.div_const 2
    convert h₃ using 1; ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2))
      (Real.exp (-(y ^ 2) / 2) * (-y)) y := hsq.exp
  have hpdf : HasDerivAt (fun x : ℝ => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2))
      ((√(2 * π))⁻¹ * (Real.exp (-(y ^ 2) / 2) * (-y))) y := hexp.const_mul _
  convert hpdf using 1; ring

/-- **Rodrigues-type derivative identity.** PROVED.

For all `n` and all `y`,
  `d/dy [H_n(y) · pdf(y)] = −H_{n+1}(y) · pdf(y)`.

Equivalently, `H_n · pdf = (−1)^n · pdf^{(n)}`, so each derivative drops
the sign. The proof uses the product rule, the Gaussian ODE
`pdf' = −y · pdf`, and the Hermite recurrence
`H_{n+1}(y) = y · H_n(y) − H_n'(y)`. -/
lemma hasDerivAt_hermiteFun_mul_pdf (n : ℕ) (y : ℝ) :
    HasDerivAt (fun z => hermiteFun n z * pdf z)
      (-(hermiteFun (n + 1) y) * pdf y) y := by
  have hH : HasDerivAt (hermiteFun n) (deriv (hermiteFun n) y) y :=
    (hermiteFun_differentiable n y).hasDerivAt
  have hP : HasDerivAt pdf (-y * pdf y) y := hasDerivAt_pdf y
  have h_prod : HasDerivAt (fun z => hermiteFun n z * pdf z)
      (deriv (hermiteFun n) y * pdf y + hermiteFun n y * (-y * pdf y)) y :=
    hH.mul hP
  convert h_prod using 1
  -- Show: -H_{n+1}(y) · pdf(y) = H_n'(y) · pdf(y) − y · H_n(y) · pdf(y)
  have hrec : hermiteFun (n + 1) y = y * hermiteFun n y - deriv (hermiteFun n) y :=
    hermiteFun_succ n y
  rw [hrec]; ring

/-! ## Decay and integrability of `hermiteFun n · pdf` -/

/-- `|y|^n · pdf(y) → 0` at `+∞`. Uses `exp(-y²/2) ≤ exp(-y/2)` for `y ≥ 1`
plus `tendsto_pow_mul_exp_neg_atTop_nhds_zero`. -/
lemma tendsto_pow_mul_pdf_atTop (n : ℕ) :
    Tendsto (fun y : ℝ => y ^ n * pdf y) atTop (𝓝 0) := by
  -- Step 1: y^n * exp(-y/2) tends to 0 as y → ∞, via composition with `y/2`.
  have hhalf : Tendsto (fun y : ℝ => y / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hpow_exp : Tendsto (fun y : ℝ => y ^ n * Real.exp (-(y / 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => u ^ n * Real.exp (-u)) atTop (𝓝 0) :=
      tendsto_pow_mul_exp_neg_atTop_nhds_zero n
    have h2 : Tendsto (fun y : ℝ => (y / 2) ^ n * Real.exp (-(y / 2))) atTop (𝓝 0) :=
      h1.comp hhalf
    have h3 : Tendsto (fun y : ℝ => (2 : ℝ) ^ n * ((y / 2) ^ n * Real.exp (-(y / 2))))
        atTop (𝓝 ((2 : ℝ) ^ n * 0)) :=
      tendsto_const_nhds.mul h2
    rw [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards with y
    have h2ne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)
    rw [div_pow]
    field_simp
  -- Step 2: multiply by constant (√(2π))⁻¹.
  set c : ℝ := (Real.sqrt (2 * π))⁻¹ with hc_def
  have hc_nonneg : 0 ≤ c := by
    have : 0 ≤ Real.sqrt (2 * π) := Real.sqrt_nonneg _
    positivity
  have hconst : Tendsto (fun y : ℝ => c * (y ^ n * Real.exp (-(y / 2)))) atTop
      (𝓝 (c * 0)) := tendsto_const_nhds.mul hpow_exp
  rw [mul_zero] at hconst
  -- Step 3: For y ≥ 1, 0 ≤ y^n * pdf y ≤ c * y^n * exp(-y/2). Use squeeze.
  refine squeeze_zero' (f := fun y : ℝ => y ^ n * pdf y)
    (g := fun y : ℝ => c * (y ^ n * Real.exp (-(y / 2)))) ?_ ?_ hconst
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy
    exact mul_nonneg (pow_nonneg hy n) (pdf_nonneg y)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy
    have hy_pos : 0 ≤ y := le_trans zero_le_one hy
    have hyn_nonneg : 0 ≤ y ^ n := pow_nonneg hy_pos n
    -- pdf y = c * exp(-y²/2)
    have hpdf_eq : pdf y = c * Real.exp (-(y ^ 2) / 2) := by
      show gaussianPDFReal 0 1 y = c * Real.exp (-(y ^ 2) / 2)
      unfold gaussianPDFReal
      simp [hc_def]
    -- y² ≥ y for y ≥ 1
    have hy_sq : y ≤ y ^ 2 := by
      have h : y * 1 ≤ y * y := mul_le_mul_of_nonneg_left hy hy_pos
      simpa [pow_two] using h
    -- exp(-y²/2) ≤ exp(-y/2)
    have hexp_le : Real.exp (-(y ^ 2) / 2) ≤ Real.exp (-(y / 2)) := by
      apply Real.exp_le_exp.mpr
      have h_neg : -(y ^ 2) ≤ -y := by linarith
      linarith
    rw [hpdf_eq]
    calc y ^ n * (c * Real.exp (-(y ^ 2) / 2))
        = c * (y ^ n * Real.exp (-(y ^ 2) / 2)) := by ring
      _ ≤ c * (y ^ n * Real.exp (-(y / 2))) := by
          apply mul_le_mul_of_nonneg_left _ hc_nonneg
          exact mul_le_mul_of_nonneg_left hexp_le hyn_nonneg

/-- `pdf` is even: `pdf(-y) = pdf(y)`. -/
private lemma pdf_neg (y : ℝ) : pdf (-y) = pdf y := by
  show gaussianPDFReal 0 1 (-y) = gaussianPDFReal 0 1 y
  unfold gaussianPDFReal
  simp

/-- `|y|^n · pdf(y) → 0` at `-∞`. Reduce to `atTop` via `y ↦ -y`. -/
lemma tendsto_pow_mul_pdf_atBot (n : ℕ) :
    Tendsto (fun y : ℝ => y ^ n * pdf y) atBot (𝓝 0) := by
  -- Substitute y ↦ -y. `(-y)^n * pdf(-y) = (-1)^n * y^n * pdf y`.
  have h_top : Tendsto (fun y : ℝ => y ^ n * pdf y) atTop (𝓝 0) :=
    tendsto_pow_mul_pdf_atTop n
  -- Composed with Neg.neg : ℝ → ℝ which takes atBot to atTop.
  have hneg : Tendsto (fun y : ℝ => -y) atBot atTop := tendsto_neg_atBot_atTop
  have h_comp : Tendsto (fun y : ℝ => (-y) ^ n * pdf (-y)) atBot (𝓝 0) :=
    h_top.comp hneg
  -- (-y)^n * pdf(-y) = (-1)^n * (y^n * pdf y)
  have hrewrite : ∀ y : ℝ, (-y) ^ n * pdf (-y) = (-1) ^ n * (y ^ n * pdf y) := by
    intro y; rw [pdf_neg, neg_pow]; ring
  have h_comp' : Tendsto (fun y : ℝ => (-1 : ℝ) ^ n * (y ^ n * pdf y)) atBot (𝓝 0) := by
    refine h_comp.congr ?_
    intro y; exact hrewrite y
  -- Multiply by (-1)^n to recover y^n * pdf y.
  have h_const : Tendsto (fun y : ℝ => (-1 : ℝ) ^ n * ((-1) ^ n * (y ^ n * pdf y)))
      atBot (𝓝 ((-1 : ℝ) ^ n * 0)) :=
    tendsto_const_nhds.mul h_comp'
  rw [mul_zero] at h_const
  refine h_const.congr ?_
  intro y
  rw [← mul_assoc, ← pow_add, ← two_mul]
  have : ((-1 : ℝ)) ^ (2 * n) = 1 := by
    rw [pow_mul]; simp
  rw [this, one_mul]

/-- Polynomial expansion: `hermiteFun n y = ∑ i ∈ range (deg+1), c_i * y^i`,
where `c_i := ((hermite n).coeff i : ℝ)`. -/
private lemma hermiteFun_eq_sum (n : ℕ) (y : ℝ) :
    hermiteFun n y =
      ∑ i ∈ Finset.range ((hermite n).natDegree + 1),
        ((hermite n).coeff i : ℝ) * y ^ i := by
  unfold hermiteFun
  rw [aeval_eq_sum_range (R := ℤ) (S := ℝ) (p := hermite n) y]
  apply Finset.sum_congr rfl
  intros i _
  rw [Algebra.smul_def]
  simp

/-- Every Hermite polynomial × pdf tends to zero at `+∞`. -/
lemma tendsto_hermiteFun_mul_pdf_atTop (n : ℕ) :
    Tendsto (fun y : ℝ => hermiteFun n y * pdf y) atTop (𝓝 0) := by
  have h_sum_tendsto : Tendsto
      (fun y : ℝ => ∑ i ∈ Finset.range ((hermite n).natDegree + 1),
          ((hermite n).coeff i : ℝ) * (y ^ i * pdf y))
      atTop (𝓝 (∑ i ∈ Finset.range ((hermite n).natDegree + 1),
          ((hermite n).coeff i : ℝ) * (0 : ℝ))) := by
    refine tendsto_finsetSum _ (fun i _ => ?_)
    exact tendsto_const_nhds.mul (tendsto_pow_mul_pdf_atTop i)
  have hzero : (∑ i ∈ Finset.range ((hermite n).natDegree + 1),
      ((hermite n).coeff i : ℝ) * (0 : ℝ)) = 0 := by simp
  rw [hzero] at h_sum_tendsto
  refine h_sum_tendsto.congr ?_
  intro y
  rw [hermiteFun_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intros; ring

lemma tendsto_hermiteFun_mul_pdf_atBot (n : ℕ) :
    Tendsto (fun y : ℝ => hermiteFun n y * pdf y) atBot (𝓝 0) := by
  have h_sum_tendsto : Tendsto
      (fun y : ℝ => ∑ i ∈ Finset.range ((hermite n).natDegree + 1),
          ((hermite n).coeff i : ℝ) * (y ^ i * pdf y))
      atBot (𝓝 (∑ i ∈ Finset.range ((hermite n).natDegree + 1),
          ((hermite n).coeff i : ℝ) * (0 : ℝ))) := by
    refine tendsto_finsetSum _ (fun i _ => ?_)
    exact tendsto_const_nhds.mul (tendsto_pow_mul_pdf_atBot i)
  have hzero : (∑ i ∈ Finset.range ((hermite n).natDegree + 1),
      ((hermite n).coeff i : ℝ) * (0 : ℝ)) = 0 := by simp
  rw [hzero] at h_sum_tendsto
  refine h_sum_tendsto.congr ?_
  intro y
  rw [hermiteFun_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intros; ring

/-- Each monomial `y^i` is γ-integrable. -/
private lemma integrable_pow_gamma (i : ℕ) : Integrable (fun y : ℝ => y ^ i) γ := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp only [pow_zero]
    exact integrable_const _
  -- For i ≥ 1, use MemLp id i and integrable_norm_pow.
  have hmem : MemLp (id : ℝ → ℝ) (i : NNReal) γ :=
    memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) (i : NNReal)
  have h_int_norm : Integrable (fun y : ℝ => ‖y‖ ^ i) γ :=
    hmem.integrable_norm_pow (p := i) hi.ne'
  -- |y^i| = ‖y‖^i, so y^i is integrable.
  have h_meas : AEStronglyMeasurable (fun y : ℝ => y ^ i) γ :=
    (continuous_pow i).aestronglyMeasurable
  refine (integrable_norm_iff h_meas).mp ?_
  refine h_int_norm.congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only [norm_pow]

/-- `hermiteFun n` is γ-integrable. -/
lemma integrable_hermiteFun_gamma (n : ℕ) : Integrable (hermiteFun n) γ := by
  -- hermiteFun n y = ∑ i, c_i * y^i. Each y^i is integrable; sum of integrables is integrable.
  have h_rewrite : (hermiteFun n) =
      fun y => ∑ i ∈ Finset.range ((hermite n).natDegree + 1),
        ((hermite n).coeff i : ℝ) * y ^ i := by
    ext y; exact hermiteFun_eq_sum n y
  rw [h_rewrite]
  apply integrable_finsetSum
  intros i _
  exact (integrable_pow_gamma i).const_mul _

/-- `hermiteFun n` is Lebesgue × pdf-integrable. -/
lemma integrable_hermiteFun_mul_pdf (n : ℕ) :
    Integrable (fun y => hermiteFun n y * pdf y) := by
  -- Use: Integrable f γ ↔ Integrable (fun y => pdf y * f y) volume, then multiplication commutes.
  have h_gamma : Integrable (hermiteFun n) γ := integrable_hermiteFun_gamma n
  -- γ = volume.withDensity (gaussianPDF 0 1)
  have hγ_eq : (γ : Measure ℝ) = (volume : Measure ℝ).withDensity (gaussianPDF 0 1) := by
    show gaussianReal 0 1 = _
    have h1ne : ((1 : NNReal)) ≠ 0 := one_ne_zero
    exact gaussianReal_of_var_ne_zero _ h1ne
  rw [hγ_eq] at h_gamma
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at h_gamma
  refine h_gamma.congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  show (gaussianPDF 0 1 y).toReal • hermiteFun n y = hermiteFun n y * pdf y
  rw [smul_eq_mul, mul_comm]
  congr 1
  -- pdf y = (gaussianPDF 0 1 y).toReal
  show (ENNReal.ofReal (gaussianPDFReal 0 1 y)).toReal = pdf y
  rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  rfl

/-! ## Hermite integration by parts against the Gaussian -/

/-- **Hermite IBP against the standard Gaussian.** PROVED.

For all `n` and all `F : ℝ → ℝ` that is `C¹` with `F, F'` bounded,
  `∫ H_n(y) · F'(y) dγ(y) = ∫ H_{n+1}(y) · F(y) dγ(y)`.

Proof outline: let `G(y) := H_n(y) · F(y) · pdf(y)`. The product rule
combined with `(H_n · pdf)' = −H_{n+1} · pdf` (hasDerivAt_hermiteFun_mul_pdf)
gives
  `G'(y) = H_n(y) · F'(y) · pdf(y) − H_{n+1}(y) · F(y) · pdf(y)`.
`G → 0` at `±∞` since `|G| ≤ |H_n| · M · pdf` and polynomial × Gaussian → 0.
FTC (`integral_of_hasDerivAt_of_tendsto`) gives `∫_ℝ G' = 0`, equivalently
the claim after Lebesgue ↔ γ conversion.

This is the n = 1 case generalization of `stein_identity_standard`. -/
lemma hermite_ibp_gaussian (n : ℕ) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    {M : ℝ} (hF_bd : ∀ y, |F y| ≤ M) (hF'_bd : ∀ y, |deriv F y| ≤ M) :
    ∫ y, hermiteFun n y * deriv F y ∂γ =
      ∫ y, hermiteFun (n + 1) y * F y ∂γ := by
  -- Setup: basic regularity of the data.
  have hM_nn : 0 ≤ M := (abs_nonneg _).trans (hF_bd 0)
  have hF_diff : Differentiable ℝ F := hF.differentiable (by simp)
  have hF_meas : Measurable F := hF.continuous.measurable
  have hF'_meas : Measurable (deriv F) := (hF.continuous_deriv (by simp)).measurable
  have hH_meas : Measurable (hermiteFun n) := hermiteFun_measurable n
  have hH'_meas : Measurable (hermiteFun (n+1)) := hermiteFun_measurable (n+1)
  have hpdf_nn : ∀ y, 0 ≤ pdf y := pdf_nonneg
  -- Derivative of G(z) := hermiteFun n z * F z * pdf z.
  -- Product rule on (hermiteFun n · pdf) · F using
  --   (hermiteFun n · pdf)'(y) = -hermiteFun (n+1) y · pdf y  and  F'(y) = deriv F y.
  have hG_deriv : ∀ y, HasDerivAt (fun z => hermiteFun n z * F z * pdf z)
      (hermiteFun n y * deriv F y * pdf y -
        hermiteFun (n + 1) y * F y * pdf y) y := by
    intro y
    have hK : HasDerivAt (fun z => hermiteFun n z * pdf z)
        (-(hermiteFun (n + 1) y) * pdf y) y := hasDerivAt_hermiteFun_mul_pdf n y
    have hF_at : HasDerivAt F (deriv F y) y := hF_diff.differentiableAt.hasDerivAt
    have h_prod : HasDerivAt (fun z => hermiteFun n z * pdf z * F z)
        (-(hermiteFun (n + 1) y) * pdf y * F y +
          hermiteFun n y * pdf y * deriv F y) y := hK.mul hF_at
    have h_fun_eq :
        (fun z => hermiteFun n z * pdf z * F z) =
        (fun z => hermiteFun n z * F z * pdf z) := by
      funext z; ring
    rw [h_fun_eq] at h_prod
    convert h_prod using 1
    ring
  -- Auxiliary: `|hermiteFun k y * pdf y|` is Lebesgue-integrable.
  have h_int_abs_Hpdf : ∀ k : ℕ,
      Integrable (fun y => |hermiteFun k y * pdf y|) := fun k =>
    (integrable_hermiteFun_mul_pdf k).abs
  -- Tendsto: G → 0 at ±∞. Bound: ‖G y‖ ≤ M · |hermiteFun n y * pdf y|, RHS → 0.
  have h_M_Hpdf_atTop :
      Tendsto (fun y => M * |hermiteFun n y * pdf y|) atTop (𝓝 0) := by
    have h_abs : Tendsto (fun y => |hermiteFun n y * pdf y|) atTop (𝓝 0) := by
      have := (tendsto_hermiteFun_mul_pdf_atTop n).abs
      simpa [abs_zero] using this
    have := h_abs.const_mul M
    simpa using this
  have h_M_Hpdf_atBot :
      Tendsto (fun y => M * |hermiteFun n y * pdf y|) atBot (𝓝 0) := by
    have h_abs : Tendsto (fun y => |hermiteFun n y * pdf y|) atBot (𝓝 0) := by
      have := (tendsto_hermiteFun_mul_pdf_atBot n).abs
      simpa [abs_zero] using this
    have := h_abs.const_mul M
    simpa using this
  have hG_atTop : Tendsto (fun y => hermiteFun n y * F y * pdf y) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) h_M_Hpdf_atTop
    show ‖hermiteFun n y * F y * pdf y‖ ≤ M * |hermiteFun n y * pdf y|
    have h_abs_eq : |hermiteFun n y * F y * pdf y| =
        |F y| * |hermiteFun n y * pdf y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hpdf_nn y), abs_mul,
          abs_of_nonneg (hpdf_nn y)]
      ring
    rw [Real.norm_eq_abs, h_abs_eq]
    exact mul_le_mul_of_nonneg_right (hF_bd y) (abs_nonneg _)
  have hG_atBot : Tendsto (fun y => hermiteFun n y * F y * pdf y) atBot (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) h_M_Hpdf_atBot
    show ‖hermiteFun n y * F y * pdf y‖ ≤ M * |hermiteFun n y * pdf y|
    have h_abs_eq : |hermiteFun n y * F y * pdf y| =
        |F y| * |hermiteFun n y * pdf y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hpdf_nn y), abs_mul,
          abs_of_nonneg (hpdf_nn y)]
      ring
    rw [Real.norm_eq_abs, h_abs_eq]
    exact mul_le_mul_of_nonneg_right (hF_bd y) (abs_nonneg _)
  -- Integrability of the two pieces of G'.
  have h_int_HF'pdf :
      Integrable (fun y => hermiteFun n y * deriv F y * pdf y) := by
    refine Integrable.mono' ((h_int_abs_Hpdf n).const_mul M)
      ((hH_meas.mul hF'_meas).mul pdf_measurable |>.aestronglyMeasurable) ?_
    filter_upwards with y
    show ‖hermiteFun n y * deriv F y * pdf y‖ ≤ M * |hermiteFun n y * pdf y|
    have h_abs_eq : |hermiteFun n y * deriv F y * pdf y| =
        |deriv F y| * |hermiteFun n y * pdf y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hpdf_nn y), abs_mul,
          abs_of_nonneg (hpdf_nn y)]
      ring
    rw [Real.norm_eq_abs, h_abs_eq]
    exact mul_le_mul_of_nonneg_right (hF'_bd y) (abs_nonneg _)
  have h_int_HFpdf :
      Integrable (fun y => hermiteFun (n + 1) y * F y * pdf y) := by
    refine Integrable.mono' ((h_int_abs_Hpdf (n + 1)).const_mul M)
      ((hH'_meas.mul hF_meas).mul pdf_measurable |>.aestronglyMeasurable) ?_
    filter_upwards with y
    show ‖hermiteFun (n + 1) y * F y * pdf y‖ ≤ M * |hermiteFun (n + 1) y * pdf y|
    have h_abs_eq : |hermiteFun (n + 1) y * F y * pdf y| =
        |F y| * |hermiteFun (n + 1) y * pdf y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hpdf_nn y), abs_mul,
          abs_of_nonneg (hpdf_nn y)]
      ring
    rw [Real.norm_eq_abs, h_abs_eq]
    exact mul_le_mul_of_nonneg_right (hF_bd y) (abs_nonneg _)
  have h_int_G' :
      Integrable (fun y => hermiteFun n y * deriv F y * pdf y -
        hermiteFun (n + 1) y * F y * pdf y) := h_int_HF'pdf.sub h_int_HFpdf
  -- ∫_ℝ G' = 0 by FTC at both infinities.
  have h_int_zero :
      ∫ y, hermiteFun n y * deriv F y * pdf y -
        hermiteFun (n + 1) y * F y * pdf y = 0 := by
    have := integral_of_hasDerivAt_of_tendsto hG_deriv h_int_G' hG_atBot hG_atTop
    simpa using this
  have h_lebesgue :
      ∫ y, hermiteFun n y * deriv F y * pdf y =
        ∫ y, hermiteFun (n + 1) y * F y * pdf y := by
    have h := h_int_zero
    rw [integral_sub h_int_HF'pdf h_int_HFpdf] at h
    linarith
  -- Convert γ-integrals to Lebesgue via integral_gaussianReal_eq_integral_smul.
  have h_v_ne : (1 : NNReal) ≠ 0 := ne_of_gt zero_lt_one
  have h_lhs :
      ∫ y, hermiteFun n y * deriv F y ∂γ =
        ∫ y, hermiteFun n y * deriv F y * pdf y := by
    show ∫ y, hermiteFun n y * deriv F y ∂(gaussianReal (0 : ℝ) (1 : NNReal)) = _
    rw [integral_gaussianReal_eq_integral_smul h_v_ne]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show pdf y • (hermiteFun n y * deriv F y) = hermiteFun n y * deriv F y * pdf y
    rw [smul_eq_mul]; ring
  have h_rhs :
      ∫ y, hermiteFun (n + 1) y * F y ∂γ =
        ∫ y, hermiteFun (n + 1) y * F y * pdf y := by
    show ∫ y, hermiteFun (n + 1) y * F y ∂(gaussianReal (0 : ℝ) (1 : NNReal)) = _
    rw [integral_gaussianReal_eq_integral_smul h_v_ne]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show pdf y • (hermiteFun (n + 1) y * F y) = hermiteFun (n + 1) y * F y * pdf y
    rw [smul_eq_mul]; ring
  rw [h_lhs, h_rhs, h_lebesgue]

/-! ## Inductive nth-derivative formula for the OU semigroup

The Mehler integral `P_t f(x) = ∫ y, f(a·x + b·y) ∂γ` admits, for `t > 0`,
the closed-form iterated derivatives
  `iteratedDeriv n (P_t f) x = (a/b)^n · ∫ y, H_n(y) · f(a·x + b·y) ∂γ`. -/

/-- The nth-Hermite-weighted Mehler integral. -/
private def hermiteMehlerIntegral (t : ℝ) (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ y, hermiteFun n y * f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ

/-- **The iterated derivative of `P_t f` is a Hermite-weighted integral.** PROVED.

For `t > 0`, `f` with `ContDiff ⊤` and bounded `f, f'`,
  `(P_t f)^{(n)}(x) = (a/b)^n · ∫ y, H_n(y) · f(a·x + b·y) ∂γ`
where `a = exp(-t), b = sqrt(1 - exp(-2t))`.

Proof by induction on `n`:
* `n = 0`: both sides equal `P_t f`.
* Inductive step: differentiating
    `(a/b)^n · ∫ H_n(y) · f(a·x + b·y) dγ`
  in `x` via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` yields
    `(a/b)^n · ∫ H_n(y) · a · f'(a·x + b·y) dγ`.
  Apply `hermite_ibp_gaussian` to `F(y) = f(a·x + b·y)` (a · b · derivative
  in y), pushing the derivative onto Hermite to get
    `(a/b)^n · a · b⁻¹ · ∫ H_{n+1}(y) · f(a·x + b·y) dγ
        = (a/b)^{n+1} · ∫ H_{n+1}(y) · f(a·x + b·y) dγ`. -/
theorem iteratedDeriv_ouSemigroup_pos (t : ℝ) (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {M : ℝ}
    (hf_bd : ∀ x, |f x| ≤ M) (hf'_bd : ∀ x, |deriv f x| ≤ M)
    (n : ℕ) :
    iteratedDeriv n (ouSemigroup t f) =
      fun x => (Real.exp (-t) / Real.sqrt (1 - Real.exp (-2 * t))) ^ n *
        hermiteMehlerIntegral t n f x := by
  -- Setup: abbreviations a = exp(-t), b = sqrt(1 - exp(-2t)).
  set a : ℝ := Real.exp (-t) with ha_def
  set b : ℝ := Real.sqrt (1 - Real.exp (-2 * t)) with hb_def
  -- Bounds on a, b.
  have ha_pos : 0 < a := Real.exp_pos _
  have ha_nn : 0 ≤ a := ha_pos.le
  have h_exp_neg_two_t_lt : Real.exp (-2 * t) < 1 := by
    apply Real.exp_lt_one_iff.mpr; linarith
  have h_one_sub_pos : 0 < 1 - Real.exp (-2 * t) := by linarith
  have h_one_sub_le_one : 1 - Real.exp (-2 * t) ≤ 1 := by
    have : 0 < Real.exp (-2 * t) := Real.exp_pos _
    linarith
  have hb_pos : 0 < b := Real.sqrt_pos.mpr h_one_sub_pos
  have hb_nn : 0 ≤ b := hb_pos.le
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hb_le_one : b ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from by simp]
    exact Real.sqrt_le_sqrt h_one_sub_le_one
  have hb_abs : |b| = b := abs_of_pos hb_pos
  have ha_abs : |a| = a := abs_of_pos ha_pos
  -- M nonneg.
  have hM_nn : 0 ≤ M := (abs_nonneg _).trans (hf_bd 0)
  -- Basic regularity of f.
  have hf_C1 : ContDiff ℝ 1 f := hf.of_le (by simp : ((1 : WithTop ℕ∞)) ≤ ∞)
  have hf_diff : Differentiable ℝ f := hf.differentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hf_meas : Measurable f := hf.continuous.measurable
  have hf'_meas : Measurable (deriv f) :=
    (hf_C1.continuous_deriv (by simp)).measurable
  -- Differentiability of `fun y => f (a*x + b*y)` for each x.
  have hf_xy_diff : ∀ x y, HasDerivAt (fun y => f (a * x + b * y))
      (b * deriv f (a * x + b * y)) y := by
    intro x y
    have h_inner : HasDerivAt (fun y => a * x + b * y) b y := by
      simpa using (((hasDerivAt_id y).const_mul b)).const_add (a * x)
    have h_f : HasDerivAt f (deriv f (a * x + b * y)) (a * x + b * y) :=
      hf_diff.differentiableAt.hasDerivAt
    have := h_f.comp y h_inner
    simpa only [Function.comp_def, mul_comm b (deriv f _)] using this
  have hf_xy_contDiff : ∀ x, ContDiff ℝ 1 (fun y => f (a * x + b * y)) := by
    intro x
    have h_inner : ContDiff ℝ 1 (fun y : ℝ => a * x + b * y) :=
      contDiff_const.add (contDiff_const.mul contDiff_id)
    exact hf_C1.comp h_inner
  -- Helper: deriv in y of `fun y => f (a*x + b*y)` equals `b * deriv f (a*x + b*y)`.
  have hf_xy_deriv_eq : ∀ x y,
      deriv (fun y => f (a * x + b * y)) y = b * deriv f (a * x + b * y) :=
    fun x y => (hf_xy_diff x y).deriv
  -- The key derivative-under-the-integral helper.
  have hMehler_deriv : ∀ (n : ℕ) (x : ℝ),
      HasDerivAt (hermiteMehlerIntegral t n f)
        ((a / b) * hermiteMehlerIntegral t (n + 1) f x) x := by
    intro n x₀
    -- Set up the parametric integral.
    set F : ℝ → ℝ → ℝ := fun x y => hermiteFun n y * f (a * x + b * y) with hF_def
    set F' : ℝ → ℝ → ℝ :=
      fun x y => hermiteFun n y * (a * deriv f (a * x + b * y)) with hF'_def
    set bound : ℝ → ℝ := fun y => |hermiteFun n y| * (a * M) with hbound_def
    have hs : Set.Ioo (x₀ - 1) (x₀ + 1) ∈ nhds x₀ :=
      Ioo_mem_nhds (by linarith) (by linarith)
    -- Measurability.
    have hH_meas : Measurable (hermiteFun n) := hermiteFun_measurable n
    have hF_meas : ∀ x, AEStronglyMeasurable (F x) γ := by
      intro x
      have h1 : Measurable (fun y => f (a * x + b * y)) :=
        hf_meas.comp (measurable_const.add (measurable_const.mul measurable_id))
      exact (hH_meas.mul h1).aestronglyMeasurable
    -- Integrability of F x₀.
    have hF_int : Integrable (F x₀) γ := by
      refine Integrable.mono'
        ((integrable_hermiteFun_gamma n).abs.const_mul M) (hF_meas x₀) ?_
      filter_upwards with y
      show ‖hermiteFun n y * f (a * x₀ + b * y)‖ ≤ M * |hermiteFun n y|
      rw [Real.norm_eq_abs, abs_mul]
      rw [mul_comm M _]
      exact mul_le_mul_of_nonneg_left (hf_bd _) (abs_nonneg _)
    -- Measurability of F' x₀.
    have hF'_meas : AEStronglyMeasurable (F' x₀) γ := by
      have h1 : Measurable (fun y => deriv f (a * x₀ + b * y)) :=
        hf'_meas.comp (measurable_const.add (measurable_const.mul measurable_id))
      exact (hH_meas.mul (measurable_const.mul h1)).aestronglyMeasurable
    -- Bound on F'.
    have h_bound : ∀ᵐ y ∂γ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
        ‖F' x y‖ ≤ bound y := by
      filter_upwards with y x _
      show ‖hermiteFun n y * (a * deriv f (a * x + b * y))‖
        ≤ |hermiteFun n y| * (a * M)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, ha_abs]
      have h1 : |deriv f (a * x + b * y)| ≤ M := hf'_bd _
      have ha_M_nn : 0 ≤ a * M := mul_nonneg ha_nn hM_nn
      have h_inner : a * |deriv f (a * x + b * y)| ≤ a * M :=
        mul_le_mul_of_nonneg_left h1 ha_nn
      exact mul_le_mul_of_nonneg_left h_inner (abs_nonneg _)
    -- Integrability of the bound.
    have h_bound_int : Integrable bound γ := by
      show Integrable (fun y => |hermiteFun n y| * (a * M)) γ
      exact (integrable_hermiteFun_gamma n).abs.mul_const _
    -- Differentiability.
    have h_diff : ∀ᵐ y ∂γ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
        HasDerivAt (F · y) (F' x y) x := by
      filter_upwards with y x _
      show HasDerivAt (fun x => hermiteFun n y * f (a * x + b * y))
        (hermiteFun n y * (a * deriv f (a * x + b * y))) x
      -- Inner: HasDerivAt (fun x => a * x + b * y) a x
      have h_inner : HasDerivAt (fun x => a * x + b * y) a x := by
        simpa using ((hasDerivAt_id x).const_mul a).add_const (b * y)
      have h_f : HasDerivAt f (deriv f (a * x + b * y)) (a * x + b * y) :=
        hf_diff.differentiableAt.hasDerivAt
      have h_comp : HasDerivAt (fun x => f (a * x + b * y))
          (deriv f (a * x + b * y) * a) x := h_f.comp x h_inner
      have h_mul := h_comp.const_mul (hermiteFun n y)
      simpa [mul_comm a (deriv f _), mul_assoc] using h_mul
    -- Apply parametric differentiation.
    obtain ⟨_, h_deriv⟩ :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
        (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound h_bound_int h_diff
    -- h_deriv : HasDerivAt (fun x => ∫ y, F x y ∂γ) (∫ y, F' x₀ y ∂γ) x₀.
    -- LHS = hermiteMehlerIntegral t n f.
    have h_lhs_eq : (fun x => ∫ y, F x y ∂γ) = hermiteMehlerIntegral t n f := by
      funext x; rfl
    -- Now apply Hermite IBP to convert the RHS.
    -- For fixed x₀, let G(y) := f (a*x₀ + b*y); apply hermite_ibp_gaussian.
    set Gx : ℝ → ℝ := fun y => f (a * x₀ + b * y) with hGx_def
    have hGx_C1 : ContDiff ℝ 1 Gx := hf_xy_contDiff x₀
    have hGx_bd : ∀ y, |Gx y| ≤ M := fun y => hf_bd _
    have hGx_deriv_eq : ∀ y, deriv Gx y = b * deriv f (a * x₀ + b * y) :=
      fun y => hf_xy_deriv_eq x₀ y
    have hGx'_bd : ∀ y, |deriv Gx y| ≤ M := by
      intro y
      rw [hGx_deriv_eq, abs_mul, hb_abs]
      have h1 : |deriv f (a * x₀ + b * y)| ≤ M := hf'_bd _
      have : b * |deriv f (a * x₀ + b * y)| ≤ b * M :=
        mul_le_mul_of_nonneg_left h1 hb_nn
      have hbM_le : b * M ≤ 1 * M := mul_le_mul_of_nonneg_right hb_le_one hM_nn
      rw [one_mul] at hbM_le
      linarith
    -- Hermite IBP: ∫ H_n y * deriv Gx y dγ = ∫ H_{n+1} y * Gx y dγ.
    have h_ibp := hermite_ibp_gaussian n hGx_C1 hGx_bd hGx'_bd
    -- Substitute deriv Gx y = b * deriv f (a * x₀ + b * y).
    have h_lhs_ibp :
        ∫ y, hermiteFun n y * deriv Gx y ∂γ =
          b * ∫ y, hermiteFun n y * deriv f (a * x₀ + b * y) ∂γ := by
      have h_step1 : ∫ y, hermiteFun n y * deriv Gx y ∂γ =
          ∫ y, b * (hermiteFun n y * deriv f (a * x₀ + b * y)) ∂γ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show hermiteFun n y * deriv Gx y =
          b * (hermiteFun n y * deriv f (a * x₀ + b * y))
        rw [hGx_deriv_eq]; ring
      rw [h_step1, integral_const_mul]
    have h_rhs_ibp : ∫ y, hermiteFun (n + 1) y * Gx y ∂γ =
        hermiteMehlerIntegral t (n + 1) f x₀ := rfl
    -- So b * ∫ H_n * f' = hermiteMehlerIntegral t (n+1) f x₀.
    have h_key :
        b * ∫ y, hermiteFun n y * deriv f (a * x₀ + b * y) ∂γ =
          hermiteMehlerIntegral t (n + 1) f x₀ := by
      rw [← h_lhs_ibp, h_ibp, h_rhs_ibp]
    -- Now compute ∫ y, F' x₀ y ∂γ.
    have h_F'_int :
        ∫ y, F' x₀ y ∂γ = a * ∫ y, hermiteFun n y * deriv f (a * x₀ + b * y) ∂γ := by
      show ∫ y, hermiteFun n y * (a * deriv f (a * x₀ + b * y)) ∂γ = _
      have h_step1 :
          ∫ y, hermiteFun n y * (a * deriv f (a * x₀ + b * y)) ∂γ =
          ∫ y, a * (hermiteFun n y * deriv f (a * x₀ + b * y)) ∂γ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        ring
      rw [h_step1, integral_const_mul]
    -- Combine: ∫ F' = a * (1/b) * hermiteMehlerIntegral t (n+1) f x₀ = (a/b) * (...)
    have h_final_eq :
        ∫ y, F' x₀ y ∂γ = (a / b) * hermiteMehlerIntegral t (n + 1) f x₀ := by
      rw [h_F'_int]
      have h_subst : ∫ y, hermiteFun n y * deriv f (a * x₀ + b * y) ∂γ =
          b⁻¹ * hermiteMehlerIntegral t (n + 1) f x₀ := by
        have h := h_key
        have h' : b⁻¹ * (b * ∫ y, hermiteFun n y * deriv f (a * x₀ + b * y) ∂γ) =
            b⁻¹ * hermiteMehlerIntegral t (n + 1) f x₀ := by rw [h]
        rw [← mul_assoc, inv_mul_cancel₀ hb_ne, one_mul] at h'
        exact h'
      rw [h_subst, div_eq_mul_inv]
      ring
    rw [h_lhs_eq, h_final_eq] at h_deriv
    exact h_deriv
  -- Induction on n.
  induction n with
  | zero =>
    funext x
    rw [iteratedDeriv_zero]
    show ouSemigroup t f x =
      (a / b) ^ 0 * hermiteMehlerIntegral t 0 f x
    rw [pow_zero, one_mul]
    show ouSemigroup t f x = ∫ y, hermiteFun 0 y * f (a * x + b * y) ∂γ
    show (∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ)
      = ∫ y, hermiteFun 0 y * f (a * x + b * y) ∂γ
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [hermiteFun_zero]
    show f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) =
      1 * f (a * x + b * y)
    rw [one_mul]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    -- Goal: deriv (fun x => (a/b)^n * hermiteMehlerIntegral t n f x) x =
    --   (a/b)^(n+1) * hermiteMehlerIntegral t (n+1) f x
    have h_deriv_at : HasDerivAt
        (fun x => (a / b) ^ n * hermiteMehlerIntegral t n f x)
        ((a / b) ^ n * ((a / b) * hermiteMehlerIntegral t (n + 1) f x)) x :=
      (hMehler_deriv n x).const_mul ((a / b) ^ n)
    rw [h_deriv_at.deriv]
    ring

/-! ## `ContDiff ⊤` conclusion -/

/-- **Differentiability of the Hermite-Mehler integral.** PROVED.

For `t > 0` and `C¹` `f` with `f, f'` bounded, `hermiteMehlerIntegral t n f`
is differentiable in `x`. The proof uses
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` to differentiate under
the integral sign — the integrand `H_n(y) · f(a·x + b·y)` is differentiable
in `x` with derivative `H_n(y) · a · f'(a·x + b·y)`, uniformly bounded by
`|H_n(y)| · a · M`. -/
private lemma differentiable_hermiteMehlerIntegral (t : ℝ) (ht : 0 < t)
    {f : ℝ → ℝ} (hf_C1 : ContDiff ℝ 1 f) {M : ℝ}
    (hf_bd : ∀ x, |f x| ≤ M) (hf'_bd : ∀ x, |deriv f x| ≤ M)
    (n : ℕ) : Differentiable ℝ (hermiteMehlerIntegral t n f) := by
  set a : ℝ := Real.exp (-t) with ha_def
  set b : ℝ := Real.sqrt (1 - Real.exp (-2 * t)) with hb_def
  have ha_pos : 0 < a := Real.exp_pos _
  have ha_nn : 0 ≤ a := ha_pos.le
  have ha_abs : |a| = a := abs_of_pos ha_pos
  have h_exp_neg_two_t_lt : Real.exp (-2 * t) < 1 := by
    apply Real.exp_lt_one_iff.mpr; linarith
  have h_one_sub_pos : 0 < 1 - Real.exp (-2 * t) := by linarith
  have hb_pos : 0 < b := Real.sqrt_pos.mpr h_one_sub_pos
  have hb_nn : 0 ≤ b := hb_pos.le
  have hM_nn : 0 ≤ M := (abs_nonneg _).trans (hf_bd 0)
  have hf_diff : Differentiable ℝ f := hf_C1.differentiable (by simp)
  have hf_meas : Measurable f := hf_C1.continuous.measurable
  have hf'_meas : Measurable (deriv f) :=
    (hf_C1.continuous_deriv (by simp)).measurable
  intro x₀
  -- Set up the parametric integral on a neighbourhood of x₀.
  set F : ℝ → ℝ → ℝ := fun x y => hermiteFun n y * f (a * x + b * y) with hF_def
  set F' : ℝ → ℝ → ℝ :=
    fun x y => hermiteFun n y * (a * deriv f (a * x + b * y)) with hF'_def
  set bound : ℝ → ℝ := fun y => |hermiteFun n y| * (a * M) with hbound_def
  have hs : Set.Ioo (x₀ - 1) (x₀ + 1) ∈ nhds x₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hH_meas : Measurable (hermiteFun n) := hermiteFun_measurable n
  have hF_meas : ∀ x, AEStronglyMeasurable (F x) γ := by
    intro x
    have h1 : Measurable (fun y => f (a * x + b * y)) :=
      hf_meas.comp (measurable_const.add (measurable_const.mul measurable_id))
    exact (hH_meas.mul h1).aestronglyMeasurable
  have hF_int : Integrable (F x₀) γ := by
    refine Integrable.mono'
      ((integrable_hermiteFun_gamma n).abs.const_mul M) (hF_meas x₀) ?_
    filter_upwards with y
    show ‖hermiteFun n y * f (a * x₀ + b * y)‖ ≤ M * |hermiteFun n y|
    rw [Real.norm_eq_abs, abs_mul]
    rw [mul_comm M _]
    exact mul_le_mul_of_nonneg_left (hf_bd _) (abs_nonneg _)
  have hF'_meas : AEStronglyMeasurable (F' x₀) γ := by
    have h1 : Measurable (fun y => deriv f (a * x₀ + b * y)) :=
      hf'_meas.comp (measurable_const.add (measurable_const.mul measurable_id))
    exact (hH_meas.mul (measurable_const.mul h1)).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂γ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
      ‖F' x y‖ ≤ bound y := by
    filter_upwards with y x _
    show ‖hermiteFun n y * (a * deriv f (a * x + b * y))‖
      ≤ |hermiteFun n y| * (a * M)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, ha_abs]
    have h1 : |deriv f (a * x + b * y)| ≤ M := hf'_bd _
    have h_inner : a * |deriv f (a * x + b * y)| ≤ a * M :=
      mul_le_mul_of_nonneg_left h1 ha_nn
    exact mul_le_mul_of_nonneg_left h_inner (abs_nonneg _)
  have h_bound_int : Integrable bound γ := by
    show Integrable (fun y => |hermiteFun n y| * (a * M)) γ
    exact (integrable_hermiteFun_gamma n).abs.mul_const _
  have h_diff : ∀ᵐ y ∂γ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
      HasDerivAt (F · y) (F' x y) x := by
    filter_upwards with y x _
    show HasDerivAt (fun x => hermiteFun n y * f (a * x + b * y))
      (hermiteFun n y * (a * deriv f (a * x + b * y))) x
    have h_inner : HasDerivAt (fun x => a * x + b * y) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).add_const (b * y)
    have h_f : HasDerivAt f (deriv f (a * x + b * y)) (a * x + b * y) :=
      hf_diff.differentiableAt.hasDerivAt
    have h_comp : HasDerivAt (fun x => f (a * x + b * y))
        (deriv f (a * x + b * y) * a) x := h_f.comp x h_inner
    have h_mul := h_comp.const_mul (hermiteFun n y)
    simpa [mul_comm a (deriv f _), mul_assoc] using h_mul
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound h_bound_int h_diff
  -- `h_deriv : HasDerivAt (fun x => ∫ y, F x y ∂γ) (∫ y, F' x₀ y ∂γ) x₀`.
  -- And `(fun x => ∫ y, F x y ∂γ) = hermiteMehlerIntegral t n f`.
  exact h_deriv.differentiableAt

/-- **`ouSemigroup_contDiff` for `t > 0`.** PROVED.

The OU semigroup applied to a `C^∞` function with `f, f'` bounded gives a
`C^∞` function. Follows from `iteratedDeriv_ouSemigroup_pos`: each iterated
derivative equals `(a/b)^n · hermiteMehlerIntegral t n f`, which is
differentiable by `differentiable_hermiteMehlerIntegral`. The hypothesis
`ContDiff ℝ ⊤ f` is weakened (via `hf.of_le`) to `ContDiff ℝ 1 f` for the
parametric integral derivative; only `C^∞` regularity is required for the
conclusion, hence the result type `ContDiff ℝ ∞`. -/
theorem ouSemigroup_contDiff_pos (t : ℝ) (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {M : ℝ}
    (hf_bd : ∀ x, |f x| ≤ M) (hf'_bd : ∀ x, |deriv f x| ≤ M) :
    ContDiff ℝ ∞ (ouSemigroup t f) := by
  have hf_C1 : ContDiff ℝ 1 f := hf.of_le (by simp : ((1 : WithTop ℕ∞)) ≤ ∞)
  apply contDiff_of_differentiable_iteratedDeriv (n := (⊤ : ℕ∞))
  intro m _
  rw [iteratedDeriv_ouSemigroup_pos t ht hf hf_bd hf'_bd m]
  exact (differentiable_hermiteMehlerIntegral t ht hf_C1 hf_bd hf'_bd m).const_mul _

/-- **Boundary case `t = 0`:** `P_0 f = f`, so trivially `C^∞`. -/
theorem ouSemigroup_zero (f : ℝ → ℝ) : ouSemigroup 0 f = f := by
  ext x
  show ∫ y, f (Real.exp (-0) * x + Real.sqrt (1 - Real.exp (-2 * 0)) * y) ∂γ = f x
  have h_exp_neg_zero : Real.exp (-0 : ℝ) = 1 := by simp
  have h_exp_neg_two_zero : Real.exp (-2 * (0 : ℝ)) = 1 := by simp
  have h_sqrt_zero : Real.sqrt (1 - Real.exp (-2 * (0 : ℝ))) = 0 := by
    rw [h_exp_neg_two_zero]; simp
  simp_rw [h_exp_neg_zero, h_sqrt_zero, one_mul, zero_mul, add_zero]
  rw [integral_const]
  simp

/-- **Boundary case `t < 0`:** Lean's `Real.sqrt` returns 0 for negative
arguments, so `b = 0` and the integrand collapses to `f(exp(−t)·x)`. -/
theorem ouSemigroup_neg (t : ℝ) (ht : t < 0) (f : ℝ → ℝ) :
    ouSemigroup t f = fun x => f (Real.exp (-t) * x) := by
  ext x
  show ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ
      = f (Real.exp (-t) * x)
  have h_pos : 1 < Real.exp (-2 * t) := by
    have : 0 < -2 * t := by linarith
    have := Real.exp_pos (-2 * t)
    have h := Real.one_lt_exp_iff.mpr (by linarith : 0 < -2 * t)
    exact h
  have h_neg : 1 - Real.exp (-2 * t) < 0 := by linarith
  have h_sqrt : Real.sqrt (1 - Real.exp (-2 * t)) = 0 :=
    Real.sqrt_eq_zero'.mpr h_neg.le
  simp_rw [h_sqrt, zero_mul, add_zero]
  rw [integral_const]
  simp

/-- **Main result: `ouSemigroup_contDiff` discharged via Hermite IBP.**

For any `f : ℝ → ℝ` that is `C^∞` and has both `f` and `f'` bounded, the
OU semigroup `P_t f` is `C^∞` for every `t : ℝ`. The conclusion `C^∞`
is stated as `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`; the input hypothesis
`ContDiff ℝ ⊤ f` (where `⊤ : WithTop ℕ∞ = ω`, i.e. analyticity) is
weakened in the proof — only `C^∞` is needed. -/
theorem ouSemigroup_contDiff_bounded (t : ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {M : ℝ}
    (hf_bd : ∀ x, |f x| ≤ M) (hf'_bd : ∀ x, |deriv f x| ≤ M) :
    ContDiff ℝ ∞ (ouSemigroup t f) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [ouSemigroup_neg t ht]
    exact hf.comp (contDiff_const.mul contDiff_id)
  · rw [ouSemigroup_zero]; exact hf
  · exact ouSemigroup_contDiff_pos t ht hf hf_bd hf'_bd

/-! ## `ouSemigroup_preserves_IsCore` (relocated from `Euclidean.lean`)

This theorem was previously in `Euclidean.lean` and used the
`ouSemigroup_contDiff` axiom. With Path C complete, the axiom is
discharged: the C^∞ part comes from `ouSemigroup_contDiff_bounded`
above, and the bound part from `ouSemigroup_preserves_bounds` in
`Euclidean.lean`. -/

/-- **OU semigroup preserves `IsCore` (BGL §2.7).** PROVED (no axioms).

For `t ≥ 0` and `IsCore f`, `P_t f` is `IsCore`:
* `ContDiff ℝ ∞ (P_t f)`: by `ouSemigroup_contDiff_bounded` (Path C).
* Boundedness of `P_t f, (P_t f)', (P_t f)''` by the same `M`: by
  `ouSemigroup_preserves_bounds` via the Mehler derivative formulas. -/
theorem ouSemigroup_preserves_IsCore (t : ℝ) (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : IsCore f) : IsCore (ouSemigroup t f) := by
  obtain ⟨h_smooth, M, hM⟩ := hf
  refine ⟨ouSemigroup_contDiff_bounded t h_smooth
            (fun x => (hM x).1) (fun x => (hM x).2.1), M, ?_⟩
  exact ouSemigroup_preserves_bounds h_smooth hM t ht

end Gaussian1D

end
