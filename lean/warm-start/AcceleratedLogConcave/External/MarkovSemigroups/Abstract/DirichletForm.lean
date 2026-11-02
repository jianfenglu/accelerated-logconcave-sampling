/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dirichlet Forms and Markov Semigroups

Layer 1 of the abstraction hierarchy. A `DirichletSpace` bundles a
probability measure μ with a symmetric energy form E(f,g), providing the
minimal structure for Poincaré and log-Sobolev inequalities.

No gradient, metric, or manifold structure is assumed.

## Main definitions

- `DirichletSpace` — probability measure + symmetric energy form
- `DirichletSpace.variance` — Var_μ(f) = E[f²] - E[f]²
- `DirichletSpace.entropy` — Ent_μ(f) = ∫ f log f dμ - (∫ f dμ) log(∫ f dμ)

## References

- Fukushima, Oshima, and Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, de Gruyter, 2011
- Ma and Röckner, *Introduction to the Theory of (Non-Symmetric)
  Dirichlet Forms*, Springer, 1992
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 1
-/

/- Port history note: inherited comments describing placeholders or legacy
postulates refer to earlier upstream development stages. Local proof status
is determined by the compiled axiom audit and the accompanying port note. -/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Measurability
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option linter.unusedSectionVars false

open MeasureTheory

noncomputable section

/-- A Dirichlet space: a probability space equipped with a symmetric
energy form (Dirichlet form).

This is the minimal structure for stating Poincaré and log-Sobolev
inequalities. No gradient or geometry is assumed.

The energy form `E(f,g)` abstracts the integral `∫ ⟨∇f, ∇g⟩ dμ` that
appears on the right side of these inequalities. On ℝⁿ with the
Gaussian measure, `E(f,g) = ∫ ⟨∇f, ∇g⟩ dγ`. On a finite graph,
`E(f,g) = ½ Σ_{x~y} (f(x)-f(y))(g(x)-g(y)) μ(x)`. The abstract
formulation covers both. -/
class DirichletSpace (X : Type*) [MeasurableSpace X] where
  /-- Reference probability measure. -/
  μ : Measure X
  /-- The measure is a probability measure. -/
  hμ : IsProbabilityMeasure μ
  /-- Symmetric energy form (Dirichlet form): E(f, g). -/
  energy : (X → ℝ) → (X → ℝ) → ℝ
  /-- Energy is symmetric. -/
  energy_symm : ∀ f g, energy f g = energy g f
  /-- Energy is nonneg on the diagonal. -/
  energy_nonneg : ∀ f, 0 ≤ energy f f
  /-- Admissible "core" functions — the algebra A₀ in BGL §1.4.2 on which
  the Dirichlet form's axioms hold. On ℝⁿ with OU: smooth compactly
  supported. On a finite space: all functions. -/
  IsCore : (X → ℝ) → Prop
  /-- Constants are core. -/
  IsCore_const : ∀ c : ℝ, IsCore (fun _ => c)
  /-- Core is closed under addition. -/
  IsCore_add : ∀ {f g}, IsCore f → IsCore g → IsCore (f + g)
  /-- Core is closed under scalar multiplication. -/
  IsCore_smul : ∀ (c : ℝ) {f}, IsCore f → IsCore (c • f)
  /-- Energy is bilinear (left). -/
  energy_add_left : ∀ f₁ f₂ g, IsCore f₁ → IsCore f₂ → IsCore g →
    energy (f₁ + f₂) g = energy f₁ g + energy f₂ g
  /-- Energy is bilinear (scalar left). -/
  energy_smul_left : ∀ (c : ℝ) f g, IsCore f → IsCore g →
    energy (c • f) g = c * energy f g
  /-- Constants have zero energy (Markov property consequence). -/
  energy_const : ∀ c : ℝ, energy (fun _ => c) (fun _ => c) = 0

attribute [instance] DirichletSpace.hμ

namespace DirichletSpace

variable {X : Type*} [MeasurableSpace X] [ds : DirichletSpace X]

/-- Variance of f under the reference measure. -/
def variance (f : X → ℝ) : ℝ :=
  ∫ x, (f x) ^ 2 ∂ds.μ - (∫ x, f x ∂ds.μ) ^ 2

/-- Variance is nonneg. Proved via Mathlib's `ProbabilityTheory.variance_nonneg`
and `variance_eq_sub` which gives Var[f;μ] = ∫f² - (∫f)². -/
theorem variance_nonneg' (f : X → ℝ)
    (hf : Integrable (fun x => (f x) ^ 2) ds.μ)
    (hfm : AEStronglyMeasurable f ds.μ := by fun_prop) :
    0 ≤ variance f := by
  unfold variance
  have hMemLp : MeasureTheory.MemLp f 2 ds.μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hfm).mpr hf
  have h1 := ProbabilityTheory.variance_nonneg f ds.μ
  rw [ProbabilityTheory.variance_eq_sub hMemLp] at h1
  simp only [Pi.pow_apply] at h1
  linarith

/-- Entropy of a nonneg function f under the reference measure. -/
def entropy (f : X → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x) ∂ds.μ -
  (∫ x, f x ∂ds.μ) * Real.log (∫ x, f x ∂ds.μ)

/-- Poincaré inequality with constant ρ:
  Var_μ(f) ≤ (1/ρ) E(f, f)  (for all core `f`) -/
def SatisfiesPoincare (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ f : X → ℝ, ds.IsCore f → variance f ≤ (1 / ρ) * ds.energy f f

/-- Log-Sobolev inequality with constant ρ:
  Ent_μ(f²) ≤ (2/ρ) E(f, f)  (for all core `f`) -/
def SatisfiesLogSobolev (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ f : X → ℝ, ds.IsCore f →
    entropy (fun x => f x * f x) ≤ (2 / ρ) * ds.energy f f

/-! ### Helper lemmas for the energy form -/

/-- A constant function has zero energy against any function.
Proof: E(1,1) = 0 and E(f,f) >= 0 imply E(1,f) = 0 by the Cauchy-Schwarz
argument (the quadratic t -> E(1 + t*f, 1 + t*f) = 2t*E(1,f) + t^2*E(f,f)
must be nonneg for all t). Then E(c, f) = c * E(1, f) = 0. -/
theorem energy_const_left (c : ℝ) (f : X → ℝ) (hf : ds.IsCore f) :
    ds.energy (fun _ => c) f = 0 := by
  have h_one_core : ds.IsCore (fun (_ : X) => (1 : ℝ)) := ds.IsCore_const 1
  -- First show E(1, f) = 0 where 1 is the constant-1 function
  suffices h1 : ds.energy (fun _ => (1 : ℝ)) f = 0 by
    have : ds.energy (fun _ => c) f = c * ds.energy (fun _ => (1 : ℝ)) f := by
      have heq : (fun (_ : X) => c) = c • (fun (_ : X) => (1 : ℝ)) := by
        ext x; simp
      rw [heq, ds.energy_smul_left c _ f h_one_core hf]
    rw [this, h1, mul_zero]
  -- Prove E(1, f) = 0 by Cauchy-Schwarz style argument
  -- For all t : ℝ, E(1 + t*f, 1 + t*f) >= 0
  -- E(1 + t*f, 1 + t*f) = E(1,1) + 2t*E(1,f) + t^2*E(f,f) = 2t*E(1,f) + t^2*E(f,f)
  -- This quadratic in t is >= 0 for all t, so E(1,f) = 0.
  by_contra h
  push Not at h
  set e := ds.energy (fun _ => (1 : ℝ)) f with he_def
  set a := ds.energy f f with ha_def
  -- We know E(1,1) = 0
  have h11 : ds.energy (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = 0 := ds.energy_const 1
  -- Consider t = -e / a if a > 0, or t = -sign(e) * large otherwise
  -- Actually simpler: pick t with the right sign and small enough magnitude
  -- For all t, 2*t*e + t^2*a >= 0
  have key : ∀ t : ℝ, 0 ≤ 2 * t * e + t ^ 2 * a := by
    intro t
    -- E(1 + t•f, 1 + t•f) >= 0
    have h_nn := ds.energy_nonneg ((fun _ => (1 : ℝ)) + t • f)
    -- Rewrite as E(1,1) + 2t*E(1,f) + t^2*E(f,f) = 0 + 2t*e + t^2*a
    set one : X → ℝ := fun _ => (1 : ℝ) with hone_def
    set tf : X → ℝ := t • f with htf_def
    have hone_core : ds.IsCore one := ds.IsCore_const 1
    have htf_core : ds.IsCore tf := ds.IsCore_smul t hf
    have hsum_core : ds.IsCore (one + tf) := ds.IsCore_add hone_core htf_core
    -- E(one + tf, one + tf) = E(one, one + tf) + E(tf, one + tf)
    have expand1 : ds.energy (one + tf) (one + tf) =
        ds.energy one (one + tf) + ds.energy tf (one + tf) :=
      ds.energy_add_left one tf (one + tf) hone_core htf_core hsum_core
    -- E(one, one + tf) = E(one, one) + E(one, tf) = 0 + E(one, tf) = E(one, tf)
    have expand2 : ds.energy one (one + tf) =
        ds.energy one one + ds.energy one tf := by
      rw [ds.energy_symm one (one + tf),
          ds.energy_add_left one tf one hone_core htf_core hone_core,
          ds.energy_symm one one, ds.energy_symm tf one]
    -- E(tf, one + tf) = E(tf, one) + E(tf, tf)
    have expand3 : ds.energy tf (one + tf) =
        ds.energy tf one + ds.energy tf tf := by
      rw [ds.energy_symm tf (one + tf),
          ds.energy_add_left one tf tf hone_core htf_core htf_core,
          ds.energy_symm one tf, ds.energy_symm tf tf]
    rw [expand1, expand2, expand3] at h_nn
    rw [h11] at h_nn
    simp only [zero_add] at h_nn
    -- E(one, tf) = t * E(1, f) = t * e
    have h_one_tf : ds.energy one tf = t * e := by
      rw [htf_def, ds.energy_symm, ds.energy_smul_left t f one hf hone_core,
          ds.energy_symm]
    -- E(tf, one) = E(one, tf) = t * e
    have h_tf_one : ds.energy tf one = t * e := by
      rw [ds.energy_symm]; exact h_one_tf
    -- E(tf, tf) = t^2 * E(f,f) = t^2 * a
    have h_tf_tf : ds.energy tf tf = t ^ 2 * a := by
      rw [htf_def, ds.energy_smul_left t f tf hf htf_core, ds.energy_symm,
          ds.energy_smul_left t f f hf hf, ds.energy_symm]; ring
    rw [h_one_tf, h_tf_one, h_tf_tf] at h_nn
    linarith
  -- Now from key, setting t = -e/a or using sign analysis
  -- If e ≠ 0, pick t = -e (works when |e| is small relative to a, but let's
  -- handle this more carefully)
  rcases ne_iff_lt_or_gt.mp h with h_neg | h_pos
  · -- e < 0: pick t > 0 small enough that 2*t*e + t^2*a < 0
    -- Choose t = -e/a if a > 0, or t = 1 if a = 0
    by_cases ha : a = 0
    · -- If a = 0, then 2*t*e >= 0 for all t, but e < 0 means 2*1*e < 0
      have := key 1
      linarith [ha]
    · -- a > 0 (since a >= 0 and a ≠ 0)
      have ha_pos : 0 < a := lt_of_le_of_ne (ds.energy_nonneg f) (Ne.symm ha)
      -- 2*(-e/a)*e + (-e/a)^2*a = -e^2/a < 0, contradiction
      have key_val := key (-e / a)
      have h_eq : 2 * (-e / a) * e + (-e / a) ^ 2 * a = -(e ^ 2 / a) := by field_simp; ring
      have h_esq : 0 < e ^ 2 := sq_pos_of_ne_zero (ne_of_lt h_neg)
      linarith [div_pos h_esq ha_pos]
  · -- e > 0: pick t < 0 small enough
    by_cases ha : a = 0
    · have := key (-1)
      linarith [ha]
    · have ha_pos : 0 < a := lt_of_le_of_ne (ds.energy_nonneg f) (Ne.symm ha)
      have key_val := key (-e / a)
      have h_eq : 2 * (-e / a) * e + (-e / a) ^ 2 * a = -(e ^ 2 / a) := by field_simp; ring
      have h_esq : 0 < e ^ 2 := sq_pos_of_ne_zero (ne_of_gt h_pos)
      linarith [div_pos h_esq ha_pos]

/-- Energy of a constant on the right is zero. -/
theorem energy_const_right (f : X → ℝ) (c : ℝ) (hf : ds.IsCore f) :
    ds.energy f (fun _ => c) = 0 := by
  rw [ds.energy_symm]; exact energy_const_left c f hf

/-- Energy is invariant under additive constants: E(f + c, f + c) = E(f, f).
This follows from bilinearity and the fact that constants have zero energy. -/
theorem energy_add_const (f : X → ℝ) (c : ℝ) (hf : ds.IsCore f) :
    ds.energy (fun x => f x + c) (fun x => f x + c) = ds.energy f f := by
  have h1 : (fun x => f x + c) = f + (fun _ => c) := by ext x; simp [Pi.add_apply]
  set k : X → ℝ := fun _ => c with hk_def
  have hk_core : ds.IsCore k := ds.IsCore_const c
  have hsum_core : ds.IsCore (f + k) := ds.IsCore_add hf hk_core
  rw [h1]
  -- E(f+k, f+k) = E(f, f+k) + E(k, f+k)  [add_left]
  rw [ds.energy_add_left f k (f + k) hf hk_core hsum_core]
  -- E(f, f+k) via symmetry then add_left: E(f, f+k) = E(f+k, f) = E(f,f) + E(k,f)
  conv_lhs => rw [ds.energy_symm f (f + k),
    ds.energy_add_left f k f hf hk_core hf, ds.energy_symm f f]
  -- E(k, f+k) via symmetry then add_left: E(k, f+k) = E(f+k, k) = E(f,k) + E(k,k)
  conv_lhs => rw [ds.energy_symm k (f + k),
    ds.energy_add_left f k k hf hk_core hk_core]
  -- Now substitute all the zero terms
  rw [energy_const_left c f hf, energy_const_right f c hf, ds.energy_const c]
  ring

/-- Energy of a scalar multiple: E(t • f, t • f) = t² · E(f, f). -/
theorem energy_smul (t : ℝ) (f : X → ℝ) (hf : ds.IsCore f) :
    ds.energy (t • f) (t • f) = t ^ 2 * ds.energy f f := by
  have htf_core : ds.IsCore (t • f) := ds.IsCore_smul t hf
  rw [ds.energy_smul_left t f (t • f) hf htf_core, ds.energy_symm,
      ds.energy_smul_left t f f hf hf, ds.energy_symm]
  ring

/-! ### Rothaus linearization: LSI implies Poincaré

The standard proof that a log-Sobolev inequality implies a Poincaré
inequality with the same constant, following Rothaus (1985) and
Bakry-Gentil-Ledoux, Prop 5.1.3.

**Strategy.** For any mean-zero g (∫g dμ = 0), apply LSI to
f_t(x) = 1 + t·g(x):

  Ent(f_t²) ≤ (2/ρ) · E(f_t, f_t) = (2/ρ) · t² · E(g, g)

A Taylor expansion gives Ent((1+tg)²) = 2t² · ∫g² dμ + O(t³),
so dividing by t² and sending t → 0 yields

  2 · Var(g) ≤ (2/ρ) · E(g, g),  i.e.  Var(g) ≤ (1/ρ) · E(g, g).

**Note.** The pointwise inequality x log x ≥ (x-1) + (x-1)²/2 is
FALSE for x > 1 (e.g. at x = 2: 2 log 2 ≈ 1.39 < 1.5 = 1 + 1/2),
so the global bound Ent(f²) ≥ 2·Var(f) does not hold. The correct
argument requires the limit. -/

/-! ### Analytic sub-lemmas for the Rothaus expansion

The proof of `rothaus_entropy_expansion` is factored into three sub-lemmas:

1. `mul_log_taylor2_lower` [PROVED]: A pointwise Taylor estimate for
   `(1+s)·log(1+s)` near `s = 0`, proved using Mathlib's
   `Real.abs_log_sub_add_sum_range_le` (Taylor remainder for `log`).

2. `integral_sq_perturbation` [SORRY]: An algebraic identity computing
   `∫ (1+tg)² dμ = 1 + t² · Var(f)` for mean-zero `g`. Requires Mathlib's
   integral linearity and probability measure API. This is a helper for (3).

3. `entropy_quadratic_lower` [SORRY]: The integration step combining the
   pointwise Taylor bound with dominated convergence. This requires
   Taylor estimates, Bochner integrability, and DCT. It is the remaining
   analytical obstacle; `rothaus_entropy_expansion` delegates to it.
-/

/-- **Taylor lower bound for `(1+s) · log(1+s)` near 0.**

For any `ε > 0`, there exists `δ > 0` such that for `|s| < δ`:
  `(1+s) · log(1+s) ≥ s + (1 - ε)/2 · s²`

Proved using `Real.abs_log_sub_add_sum_range_le` (Mathlib's bound on the Taylor
remainder of `log(1-x)`). With `n = 2` and `x = -s`:
  `|log(1+s) - (s - s²/2)| ≤ |s|³/(1 - |s|)`
Multiplying by `1 + s > 0` and bounding the cubic error term by `ε/2 · s²`
for `|s| < min(1/2, ε/8)` gives the result.

The `s ≥ 0` case uses `8s ≤ ε` and `8(1-s) ≥ 3+s` to bound the error.
The `s < 0` case simplifies because `1 - |s| = 1 + s` cancels the denominator,
leaving only `|s|³/2 ≤ ε/2 · s²`. -/
theorem mul_log_taylor2_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      s + (1 - ε) / 2 * s ^ 2 ≤ (1 + s) * Real.log (1 + s) := by
  refine ⟨min (1/2) (ε / 8), by positivity, fun s hs => ?_⟩
  have h_half : |s| < 1 / 2 := lt_of_lt_of_le hs (min_le_left _ _)
  have h_eps : |s| < ε / 8 := lt_of_lt_of_le hs (min_le_right _ _)
  have h_pos : (0 : ℝ) < 1 + s := by linarith [neg_abs_le s]
  have h_sub : (0 : ℝ) < 1 - |s| := by linarith
  have h_one : |s| < 1 := by linarith
  -- Taylor bound from Mathlib: |(-s + s²/2) + log(1+s)| ≤ |s|³/(1-|s|)
  have habs_neg : |-s| < 1 := by rwa [abs_neg]
  have hlog := Real.abs_log_sub_add_sum_range_le habs_neg 2
  have hsum : ∑ i ∈ Finset.range 2, (-s) ^ (i + 1) / (↑i + 1) = -s + s ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; ring
  rw [hsum, show (1 : ℝ) - -s = 1 + s from by ring, abs_neg] at hlog
  -- Extract lower bound: log(1+s) ≥ s - s²/2 - |s|³/(1-|s|)
  have hlog_lb : s - s ^ 2 / 2 - |s| ^ 3 / (1 - |s|) ≤ Real.log (1 + s) := by
    linarith [neg_abs_le ((-s + s ^ 2 / 2) + Real.log (1 + s))]
  -- Multiply by (1+s) > 0
  have hmul : (1 + s) * (s - s ^ 2 / 2 - |s| ^ 3 / (1 - |s|)) ≤ (1 + s) * Real.log (1 + s) :=
    mul_le_mul_of_nonneg_left hlog_lb (le_of_lt h_pos)
  suffices h : s + (1 - ε) / 2 * s ^ 2 ≤
      (1 + s) * (s - s ^ 2 / 2 - |s| ^ 3 / (1 - |s|)) by linarith
  -- Clear the (1-|s|) denominator: reduce to a polynomial inequality
  have h_ne : (1 - |s|) ≠ 0 := ne_of_gt h_sub
  suffices key : 0 ≤ ε / 2 * s ^ 2 * (1 - |s|) - s ^ 3 / 2 * (1 - |s|) - (1 + s) * |s| ^ 3 by
    have expand : (s + (1 - ε) / 2 * s ^ 2) * (1 - |s|) ≤
        (1 + s) * (s - s ^ 2 / 2) * (1 - |s|) - (1 + s) * |s| ^ 3 := by
      nlinarith [sq_abs s]
    have hdiv := div_le_div_of_nonneg_right expand (le_of_lt h_sub)
    simp only [mul_div_cancel_right₀ _ h_ne] at hdiv
    have key2 : ((1 + s) * (s - s ^ 2 / 2) * (1 - |s|) - (1 + s) * |s| ^ 3) / (1 - |s|) =
        (1 + s) * (s - s ^ 2 / 2 - |s| ^ 3 / (1 - |s|)) := by field_simp
    linarith
  -- Split on sign of s for the polynomial inequality
  by_cases hs_nn : 0 ≤ s
  · -- s ≥ 0: |s| = s, factor as s² · (ε/2·(1-s) - s·(3/2+s/2))
    rw [abs_of_nonneg hs_nn]
    have hrw : ε / 2 * s ^ 2 * (1 - s) - s ^ 3 / 2 * (1 - s) - (1 + s) * s ^ 3 =
      s ^ 2 * (ε / 2 * (1 - s) - s * (3 / 2 + s / 2)) := by ring
    rw [hrw]
    apply mul_nonneg (sq_nonneg s)
    have : s < ε / 8 := by rwa [abs_of_nonneg hs_nn] at h_eps
    have : s < 1 / 2 := by rwa [abs_of_nonneg hs_nn] at h_half
    nlinarith
  · -- s < 0: |s| = -s, 1-|s| = 1+s, factor as (1+s)·s²·(ε/2+s/2)
    push Not at hs_nn
    rw [abs_of_neg hs_nn]
    have hrw : ε / 2 * s ^ 2 * (1 - -s) - s ^ 3 / 2 * (1 - -s) - (1 + s) * (-s) ^ 3 =
      (1 + s) * s ^ 2 * (ε / 2 + s / 2) := by ring
    rw [hrw]
    apply mul_nonneg (mul_nonneg (le_of_lt h_pos) (sq_nonneg s))
    have : -s < ε / 8 := by rwa [abs_of_neg hs_nn] at h_eps
    linarith

/-- **Integral of the squared perturbation.**

For a probability measure μ and mean-zero g (i.e., g = f - ∫f),
  `∫ (1 + t·g)² dμ = 1 + t² · Var(f)`

Proof: expand (1+tg)² = 1 + 2tg + t²g², integrate using ∫1 = 1,
∫g = 0, and ∫g² = Var(f) (since ∫g = 0 means Var = ∫g²). -/
theorem integral_sq_perturbation (f : X → ℝ)
    (hf_int : Integrable f ds.μ) (hf2_int : Integrable (fun x => f x ^ 2) ds.μ)
    (t : ℝ) :
    ∫ x, (1 + t * (f x - ∫ y, f y ∂ds.μ)) ^ 2 ∂ds.μ = 1 + t ^ 2 * variance f := by
  set m := ∫ y, f y ∂ds.μ with hm_def
  have hg_int : Integrable (fun x => f x - m) ds.μ := hf_int.sub (integrable_const m)
  have hg2_int : Integrable (fun x => (f x - m) ^ 2) ds.μ := by
    have : (fun x => (f x - m) ^ 2) = (fun x => f x ^ 2 - 2 * m * f x + m ^ 2) := by
      ext x; ring
    rw [this]; exact (hf2_int.sub (hf_int.const_mul (2 * m))).add (integrable_const _)
  have hg_mean : ∫ x, (f x - m) ∂ds.μ = 0 := by
    rw [integral_sub hf_int (integrable_const m), integral_const, probReal_univ, one_smul, sub_self]
  have hg2_var : ∫ x, (f x - m) ^ 2 ∂ds.μ = variance f := by
    unfold variance
    have h_eq : ∀ x, (f x - m) ^ 2 = f x ^ 2 + (-2 * m * f x + m ^ 2) := by intro x; ring
    simp_rw [h_eq]
    have h1 : ∫ x, (f x ^ 2 + (-2 * m * f x + m ^ 2)) ∂ds.μ =
        ∫ x, f x ^ 2 ∂ds.μ + ∫ x, (-2 * m * f x + m ^ 2) ∂ds.μ :=
      integral_add hf2_int ((hf_int.const_mul (-2 * m)).add (integrable_const _))
    rw [h1]
    have h2 : ∫ x, (-2 * m * f x + m ^ 2) ∂ds.μ =
        ∫ x, (-2 * m * f x) ∂ds.μ + ∫ _x : X, m ^ 2 ∂ds.μ :=
      integral_add (hf_int.const_mul (-2 * m)) (integrable_const _)
    rw [h2, integral_const_mul, integral_const, probReal_univ, one_smul, hm_def]; ring
  have h_tg_int : Integrable (fun x => 2 * t * (f x - m)) ds.μ := hg_int.const_mul (2 * t)
  have h_tg2_int : Integrable (fun x => t ^ 2 * (f x - m) ^ 2) ds.μ :=
    hg2_int.const_mul (t ^ 2)
  have h1 : ∀ x, (1 + t * (f x - m)) ^ 2 =
      1 + 2 * t * (f x - m) + t ^ 2 * (f x - m) ^ 2 := by intro x; ring
  simp_rw [h1]
  have h3 : ∫ x, (1 + 2 * t * (f x - m) + t ^ 2 * (f x - m) ^ 2) ∂ds.μ =
      ∫ x, (1 + 2 * t * (f x - m)) ∂ds.μ + ∫ x, t ^ 2 * (f x - m) ^ 2 ∂ds.μ :=
    integral_add ((integrable_const 1).add h_tg_int) h_tg2_int
  rw [h3]
  have h4 : ∫ x, (1 + 2 * t * (f x - m)) ∂ds.μ =
      ∫ _x : X, (1 : ℝ) ∂ds.μ + ∫ x, 2 * t * (f x - m) ∂ds.μ :=
    integral_add (integrable_const 1) h_tg_int
  rw [h4, integral_const, probReal_univ, one_smul, integral_const_mul, hg_mean, mul_zero, add_zero,
      integral_const_mul, hg2_var]

/-! ### Entropy lower bound via sub-lemmas

The entropy lower bound `entropy_quadratic_lower` combines three
sub-lemmas: a pointwise Taylor bound, an upper bound on the log
correction term, and integration of the pointwise bound.

*Reference*: Bakry-Gentil-Ledoux, proof of Proposition 5.1.3. -/

/-- **Sub-lemma 1:** Pointwise lower bound on h·log(h) for h = (1+tg)².

For |g(x)| ≤ B and t small enough (t < δ₁), the pointwise Taylor bound
`mul_log_taylor2_lower` gives:

  (1+tg)² · log((1+tg)²) ≥ 2tg + (2-ε₁)·t²·g²

where the error is controlled by choosing δ₁ depending on ε₁ and B. -/
theorem pointwise_entropy_lower (g : ℝ) (t : ℝ) (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (B : ℝ) (hB : 0 < B) (hg : |g| ≤ B)
    (δ₁ : ℝ) (hδ₁ : 0 < δ₁)
    (ht : 0 < t) (ht_small : t < δ₁)
    (htg_pos : 0 < 1 + t * g)
    (h_taylor : ∀ s : ℝ, |s| < δ₁ * (2 * B + δ₁ * B ^ 2) →
      s + (1 - ε₁) / 2 * s ^ 2 ≤ (1 + s) * Real.log (1 + s)) :
    2 * t * g + (2 - ε₁) * t ^ 2 * g ^ 2 ≤
      (1 + t * g) ^ 2 * Real.log ((1 + t * g) ^ 2) := by
  -- Domain bound for h_taylor at s = tg
  have habs_tg_D : |t * g| < δ₁ * (2 * B + δ₁ * B ^ 2) := by
    have h1 : |t * g| ≤ t * B := by
      rw [abs_mul, abs_of_pos ht]; exact mul_le_mul_of_nonneg_left hg (le_of_lt ht)
    have h2 : t * B < δ₁ * B := mul_lt_mul_of_pos_right ht_small hB
    have h3 : δ₁ * B ≤ δ₁ * (2 * B + δ₁ * B ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ₁); nlinarith [sq_nonneg B, hB]
    linarith
  -- Case split on epsilon
  by_cases heps : 1 ≤ ε₁
  · -- Case ε₁ ≥ 1: LHS ≤ (1+tg)²-1 ≤ u·log(u) by standard bound
    have hLHS : 2 * t * g + (2 - ε₁) * t ^ 2 * g ^ 2 ≤ (1 + t * g) ^ 2 - 1 := by
      nlinarith [sq_nonneg (t * g)]
    have hsq_pos : (0 : ℝ) < (1 + t * g) ^ 2 := by positivity
    have hlog_lb := Real.one_sub_inv_le_log_of_pos hsq_pos
    have hmul := mul_le_mul_of_nonneg_left hlog_lb (le_of_lt hsq_pos)
    have hrw : (1 + t * g) ^ 2 * (1 - ((1 + t * g) ^ 2)⁻¹) = (1 + t * g) ^ 2 - 1 := by
      field_simp
    linarith
  · -- Case ε₁ < 1: multiply h_taylor at s=tg by 2(1+tg) > 0
    push Not at heps
    have htaylor := h_taylor (t * g) habs_tg_D
    have hlog_sq : Real.log ((1 + t * g) ^ 2) = 2 * Real.log (1 + t * g) := by
      rw [Real.log_pow]; push_cast; ring
    rw [hlog_sq, show (1 + t * g) ^ 2 * (2 * Real.log (1 + t * g)) =
        2 * (1 + t * g) * ((1 + t * g) * Real.log (1 + t * g)) from by ring]
    have hmul : 2 * (1 + t * g) * (t * g + (1 - ε₁) / 2 * (t * g) ^ 2) ≤
        2 * (1 + t * g) * ((1 + t * g) * Real.log (1 + t * g)) :=
      mul_le_mul_of_nonneg_left htaylor (by linarith)
    suffices halg : 2 * t * g + (2 - ε₁) * t ^ 2 * g ^ 2 ≤
        2 * (1 + t * g) * (t * g + (1 - ε₁) / 2 * (t * g) ^ 2) by linarith
    have htg_ge : -1 < t * g := by linarith
    have h_pos : 0 ≤ (t * g) ^ 2 * (1 + (1 - ε₁) * (t * g)) := by
      apply mul_nonneg (sq_nonneg _); nlinarith
    have hring : 2 * (1 + t * g) * (t * g + (1 - ε₁) / 2 * (t * g) ^ 2) -
        (2 * t * g + (2 - ε₁) * t ^ 2 * g ^ 2) =
        (t * g) ^ 2 * (1 + (1 - ε₁) * (t * g)) := by ring
    linarith

/-- **Sub-lemma 2:** Upper bound on the integral correction term.

For h = (1+tg)² with ∫g = 0 and ∫g² = V:
  ∫h dμ = 1 + t²V  (from integral_sq_perturbation)

The correction (∫h)·log(∫h) satisfies:
  (1+t²V)·log(1+t²V) ≤ t²V + t⁴V²  (from x·log(x) ≤ x-1+(x-1)² for x ≥ 1)

So the correction is at most t²V + t⁴V², and Ent(h) = ∫h·log(h) - (∫h)·log(∫h)
≥ (2t²V - error from Taylor) - (t²V + t⁴V²). -/
theorem log_correction_upper (u : ℝ) (hu : 0 ≤ u) :
    (1 + u) * Real.log (1 + u) ≤ u + u ^ 2 := by
  have h1u_pos : (0 : ℝ) < 1 + u := by linarith
  have h1u_nonneg : (0 : ℝ) ≤ 1 + u := le_of_lt h1u_pos
  have hlog : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos h1u_pos
    linarith
  calc (1 + u) * Real.log (1 + u)
      ≤ (1 + u) * u := mul_le_mul_of_nonneg_left hlog h1u_nonneg
    _ = u + u ^ 2 := by ring

/-- **Sub-lemma 3:** Integration of the pointwise bound.

Given ∫g dμ = 0 and ∫g² dμ = V, and the pointwise bound
  h·log(h) ≥ 2tg + (2-ε₁)t²g²  for all x
integrating gives:
  ∫ h·log(h) dμ ≥ 2t·∫g + (2-ε₁)t²·∫g² = 0 + (2-ε₁)t²V -/
theorem integrate_pointwise_bound
    (μ : Measure X) [IsProbabilityMeasure μ]
    (φ ψ : X → ℝ) (hφψ : ∀ x, ψ x ≤ φ x)
    (hψ_int : Integrable ψ μ) (hφ_int : Integrable φ μ) :
    ∫ x, ψ x ∂μ ≤ ∫ x, φ x ∂μ :=
  integral_mono hψ_int hφ_int hφψ

set_option maxHeartbeats 800000 in
/-- The full entropy lower bound, assembled from the three sub-lemmas. -/
theorem entropy_quadratic_lower (f : X → ℝ) (ε : ℝ) (hε : 0 < ε) (hε_lt : ε < 4)
    (hf_int : Integrable f ds.μ) (hf2_int : Integrable (fun x => f x ^ 2) ds.μ)
    (B : ℝ) (hB : 0 < B) (hf_bdd : ∀ x, |f x - ∫ y, f y ∂ds.μ| ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (2 - ε) * t ^ 2 * variance f ≤
        entropy (fun x => (1 + t * (f x - ∫ y, f y ∂ds.μ)) *
                          (1 + t * (f x - ∫ y, f y ∂ds.μ))) := by
  set m := ∫ y, f y ∂ds.μ
  set g : X → ℝ := fun x => f x - m
  set V := variance f
  have hg_int : Integrable g ds.μ := hf_int.sub (integrable_const m)
  have hg_bdd : ∀ x, |g x| ≤ B := hf_bdd
  have hg_mean : ∫ x, g x ∂ds.μ = 0 := by
    show ∫ x, (f x - m) ∂ds.μ = 0
    rw [integral_sub hf_int (integrable_const m), integral_const, probReal_univ, one_smul, sub_self]
  have hg2_int : Integrable (fun x => g x ^ 2) ds.μ := by
    apply Integrable.mono (integrable_const (B ^ 2))
    · exact hg_int.aestronglyMeasurable.pow 2
    · filter_upwards with x; simp [Real.norm_eq_abs]
      exact sq_le_sq' (neg_le_of_abs_le (hg_bdd x)) (le_of_abs_le (hg_bdd x))
  have hg2_var : ∫ x, g x ^ 2 ∂ds.μ = V := by
    show ∫ x, (f x - m) ^ 2 ∂ds.μ = variance f
    unfold variance
    have h_expand : ∀ x, (f x - m) ^ 2 = f x ^ 2 + (-2 * m * f x + m ^ 2) := by intro x; ring
    simp_rw [h_expand]
    have hint1 : Integrable (fun x => -2 * m * f x + m ^ 2) ds.μ :=
      (hf_int.const_mul (-2 * m)).add (integrable_const _)
    rw [integral_add hf2_int hint1]
    have hint2 : Integrable (fun x => -2 * m * f x) ds.μ := hf_int.const_mul (-2 * m)
    rw [integral_add hint2 (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul]; ring
  have hV_nn : 0 ≤ V := by rw [← hg2_var]; exact integral_nonneg (fun x => sq_nonneg _)
  -- Get Taylor bound with ε₁ = ε/4
  obtain ⟨δ₁, hδ₁_pos, h_taylor⟩ := mul_log_taylor2_lower (ε / 4) (by linarith)
  -- Choose δ = δ₁/(4B²+4B+1). This ensures t(2B+tB²) < δ₁ and tB < 1/2.
  set D := 4 * B ^ 2 + 4 * B + 1 with hD_def
  have hD_pos : 0 < D := by positivity
  refine ⟨min (δ₁ / D) (min (ε / (16 * (B ^ 2 + B + 1))) (1 / (2 * B + 1))),
    by positivity, fun t ht ht_lt => ?_⟩
  have ht_D : t < δ₁ / D := lt_of_lt_of_le ht_lt (min_le_left _ _)
  have ht_eps : t < ε / (16 * (B ^ 2 + B + 1)) :=
    lt_of_lt_of_le ht_lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht_inv : t < 1 / (2 * B + 1) :=
    lt_of_lt_of_le ht_lt (le_trans (min_le_right _ _) (min_le_right _ _))
  have htB : t * B < 1 / 2 := by
    have h1 : t * B < 1 / (2 * B + 1) * B := mul_lt_mul_of_pos_right ht_inv hB
    have h2B : (0:ℝ) < 2 * B + 1 := by positivity
    have h2 : 1 / (2 * B + 1) * B = B / (2 * B + 1) := by ring
    rw [h2] at h1
    have h3 : B / (2 * B + 1) < 1 / 2 := by rw [div_lt_div_iff₀ h2B (by positivity : (0:ℝ) < 2)]; linarith
    linarith
  have ht_le_1 : t < 1 := by
    have : 1 / (2 * B + 1) ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < 2 * B + 1)]; linarith [hB]
    linarith
  -- 1 + t*g(x) > 0 for all x
  have htg_pos : ∀ x, 0 < 1 + t * g x := by
    intro x; have : |t * g x| ≤ t * B := by
      rw [abs_mul, abs_of_pos ht]; exact mul_le_mul_of_nonneg_left (hg_bdd x) (le_of_lt ht)
    linarith [neg_abs_le (t * g x)]
  -- |s(x)| < δ₁ where s(x) = 2tg(x) + t²g(x)²
  have hs_small : ∀ x, |2 * t * g x + t ^ 2 * g x ^ 2| < δ₁ := by
    intro x
    have habs_g := hg_bdd x
    -- |s| ≤ 2t|g| + t²|g|² ≤ 2tB + t²B² ≤ t(2B + tB²) < t(2B + B²) (since t < 1)
    -- And t(2B+B²) < (δ₁/D)(2B+B²). Since D = (2B+1)², (2B+B²)/D ≤ 1, so < δ₁.
    have h_abs_le : |2 * t * g x + t ^ 2 * g x ^ 2| ≤ t * (2 * B + t * B ^ 2) := by
      have hg_le : g x ≤ B := le_of_abs_le habs_g
      have hg_ge : -B ≤ g x := neg_le_of_abs_le habs_g
      have hg2_le : g x ^ 2 ≤ B ^ 2 :=
        sq_le_sq' (by linarith) hg_le
      -- |2tg + t²g²| ≤ 2t·|g| + t²·g² ≤ 2tB + t²B²
      calc |2 * t * g x + t ^ 2 * g x ^ 2|
          ≤ |2 * t * g x| + |t ^ 2 * g x ^ 2| := abs_add_le _ _
        _ = 2 * t * |g x| + t ^ 2 * g x ^ 2 := by
            congr 1
            · rw [abs_mul, abs_of_pos (show (0:ℝ) < 2 * t by positivity)]
            · rw [abs_of_nonneg (by positivity)]
        _ ≤ 2 * t * B + t ^ 2 * B ^ 2 := by
            gcongr
        _ = t * (2 * B + t * B ^ 2) := by ring
    have h_bound : t * (2 * B + t * B ^ 2) < δ₁ := by
      have h1 : t * (2 * B + t * B ^ 2) ≤ t * (2 * B + 1 * B ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt ht)
        have : t * B ^ 2 ≤ 1 * B ^ 2 :=
          mul_le_mul_of_nonneg_right (le_of_lt ht_le_1) (sq_nonneg B)
        linarith
      have h2 : t * (2 * B + 1 * B ^ 2) < δ₁ / D * (2 * B + B ^ 2) := by
        rw [one_mul]; exact mul_lt_mul_of_pos_right ht_D (by nlinarith [hB, sq_nonneg B])
      have h3 : δ₁ / D * (2 * B + B ^ 2) ≤ δ₁ := by
        -- (2B+B²)/D ≤ 1 since D = 4B²+4B+1 ≥ 2B+B²
        have : 2 * B + B ^ 2 ≤ D := by rw [hD_def]; nlinarith [hB, sq_nonneg B]
        calc δ₁ / D * (2 * B + B ^ 2) ≤ δ₁ / D * D := by
              apply mul_le_mul_of_nonneg_left this (le_of_lt (div_pos hδ₁_pos hD_pos))
          _ = δ₁ := by field_simp
      linarith
    linarith
  -- Now prove the entropy lower bound.
  -- entropy(h) = ∫ h·log(h) - (∫h)·log(∫h)
  -- where h(x) = (1+tg(x))² and we write h(x) = 1 + s(x) with s(x) = 2tg(x) + t²g(x)²
  --
  -- Step A: ∫ h·log(h) ≥ ∫ (s + (1-ε/4)/2·s²) dμ  [pointwise Taylor bound]
  -- Step B: ∫ s dμ = t²V  [mean-zero property]
  -- Step C: ∫ s² dμ ≥ 4t²V - C·t³  [expand, bound g³ term]
  -- Step D: (∫h)·log(∫h) = (1+t²V)·log(1+t²V) ≤ t²V + t⁴V²  [log_correction_upper]
  -- Step E: Combine: entropy ≥ t²V + (1-ε/4)/2·(4t²V - Ct³) - t²V - t⁴V²
  --         = 2(1-ε/4)t²V - C't³ - t⁴V² ≥ (2-ε)t²V for small t
  --
  -- We need several integral identities. For bounded g, all functions are integrable.
  -- Define s, the perturbation
  set s : X → ℝ := fun x => 2 * t * g x + t ^ 2 * g x ^ 2
  -- h(x) = (1+tg(x))² = 1 + s(x)
  have h_eq_1s : ∀ x, (1 + t * g x) * (1 + t * g x) = 1 + s x := by
    intro x; show _ = 1 + (2 * t * g x + t ^ 2 * g x ^ 2); ring
  -- Integrability of s and s²
  have hs_int : Integrable s ds.μ := by
    show Integrable (fun x => 2 * t * g x + t ^ 2 * g x ^ 2) ds.μ
    exact (hg_int.const_mul (2 * t)).add (hg2_int.const_mul (t ^ 2))
  -- Step B: ∫ s = t²V
  have h_int_s : ∫ x, s x ∂ds.μ = t ^ 2 * V := by
    show ∫ x, (2 * t * g x + t ^ 2 * g x ^ 2) ∂ds.μ = t ^ 2 * V
    rw [integral_add (hg_int.const_mul (2 * t)) (hg2_int.const_mul (t ^ 2)),
        integral_const_mul, integral_const_mul, hg_mean, hg2_var]; ring
  -- Step D: ∫h = 1 + t²V and (∫h)·log(∫h) ≤ t²V + t⁴V²
  have h_int_h : ∫ x, (1 + t * g x) * (1 + t * g x) ∂ds.μ = 1 + t ^ 2 * V := by
    have := integral_sq_perturbation f hf_int hf2_int t
    convert this using 1
    congr 1; ext x; show (1 + t * g x) * (1 + t * g x) = (1 + t * (f x - ∫ y, f y ∂ds.μ)) ^ 2
    ring
  have h_correction : (1 + t ^ 2 * V) * Real.log (1 + t ^ 2 * V) ≤ t ^ 2 * V + (t ^ 2 * V) ^ 2 :=
    log_correction_upper (t ^ 2 * V) (mul_nonneg (sq_nonneg t) hV_nn)
  -- Convert the entropy goal to a form involving ∫(1+s)log(1+s)
  suffices h_main : (2 - ε) * t ^ 2 * V ≤
      ∫ x, (1 + s x) * Real.log (1 + s x) ∂ds.μ -
      (1 + t ^ 2 * V) * Real.log (1 + t ^ 2 * V) by
    -- Convert entropy to the above form
    unfold entropy
    have h_fg : (fun x => (1 + t * (f x - m)) * (1 + t * (f x - m))) =
        (fun x => (1 + t * g x) * (1 + t * g x)) := by rfl
    rw [h_fg, h_int_h]
    convert h_main using 1
    congr 1
    congr 1; ext x
    show (1 + t * g x) * (1 + t * g x) * Real.log ((1 + t * g x) * (1 + t * g x)) =
      (1 + s x) * Real.log (1 + s x)
    rw [h_eq_1s x]
  -- Now prove: (2-ε)t²V ≤ ∫(1+s)log(1+s) - (1+t²V)log(1+t²V)
  -- Pointwise Taylor: (1+s(x))·log(1+s(x)) ≥ s(x) + (1-ε/4)/2·s(x)²
  have h_ptwise_lb : ∀ x, s x + (1 - ε / 4) / 2 * s x ^ 2 ≤
      (1 + s x) * Real.log (1 + s x) := by
    intro x; exact h_taylor (s x) (hs_small x)
  -- Integrability of s²
  have hs2_int : Integrable (fun x => s x ^ 2) ds.μ := by
    apply Integrable.mono (integrable_const (δ₁ ^ 2))
    · exact hs_int.aestronglyMeasurable.pow 2
    · filter_upwards with x; simp [Real.norm_eq_abs]
      exact sq_le_sq' (by linarith [neg_abs_le (s x), hs_small x])
        (by linarith [le_abs_self (s x), hs_small x])
  have hlb_int : Integrable (fun x => s x + (1 - ε / 4) / 2 * s x ^ 2) ds.μ :=
    hs_int.add (hs2_int.const_mul _)
  -- Integrability of (1+s)·log(1+s) -- bounded since |s| < δ₁
  -- Integrability of |s| + s² (used as a dominating function)
  have habs_s_int : Integrable (fun x => |s x| + s x ^ 2) ds.μ :=
    hs_int.norm.add hs2_int
  have hrhs_int : Integrable (fun x => (1 + s x) * Real.log (1 + s x)) ds.μ := by
    apply Integrable.mono habs_s_int
    · -- AEStronglyMeasurable
      have h1s_asm : AEStronglyMeasurable (fun x => 1 + s x) ds.μ :=
        aestronglyMeasurable_const.add hs_int.aestronglyMeasurable
      exact h1s_asm.mul
        (Real.measurable_log.comp_aemeasurable h1s_asm.aemeasurable |>.aestronglyMeasurable)
    · filter_upwards with x
      have hs_x := hs_small x
      have h1s_pos : 0 < 1 + s x := by rw [← h_eq_1s x]; exact mul_pos (htg_pos x) (htg_pos x)
      -- ‖(1+s)*log(1+s)‖ ≤ ‖|s| + s²‖ = |s| + s²
      -- ‖(1+s)*log(1+s)‖ ≤ |s| + s²
      -- We bound using: -|s| ≤ (1+s)*log(1+s) ≤ s + s²
      simp only [Real.norm_eq_abs]
      -- Goal: |(1+s(x))*log(1+s(x))| ≤ |s(x)| + s(x)²
      have hlog_le : Real.log (1 + s x) ≤ s x := by
        linarith [Real.log_le_sub_one_of_pos h1s_pos]
      have h_ub : (1 + s x) * Real.log (1 + s x) ≤ |s x| + s x ^ 2 := by
        calc (1 + s x) * Real.log (1 + s x)
            ≤ (1 + s x) * s x :=
              mul_le_mul_of_nonneg_left hlog_le (le_of_lt h1s_pos)
          _ = s x + s x ^ 2 := by ring
          _ ≤ |s x| + s x ^ 2 := by linarith [le_abs_self (s x)]
      have h_lb : -(|s x| + s x ^ 2) ≤ (1 + s x) * Real.log (1 + s x) := by
        -- (1+s)log(1+s) ≥ (1+s) - 1 = s (standard bound u*log(u) ≥ u - 1 for u > 0)
        -- So (1+s)*log(1+s) ≥ s ≥ -|s| ≥ -(|s| + s²)
        have h_lb_simple : s x ≤ (1 + s x) * Real.log (1 + s x) := by
          have hlog := Real.one_sub_inv_le_log_of_pos h1s_pos
          -- log(1+s) ≥ 1 - 1/(1+s), multiply both sides by (1+s) > 0
          have := mul_le_mul_of_nonneg_left hlog (le_of_lt h1s_pos)
          -- (1+s)*(1 - 1/(1+s)) = (1+s) - 1 = s
          have hrw : (1 + s x) * (1 - (1 + s x)⁻¹) = s x := by
            field_simp; ring
          linarith
        linarith [neg_abs_le (s x), sq_nonneg (s x)]
      -- Goal: |(1+s)*log(1+s)| ≤ |  |s| + s²  |
      -- Since |s| + s² ≥ 0, the outer abs is identity
      rw [abs_of_nonneg (add_nonneg (abs_nonneg (s x)) (sq_nonneg (s x)))]
      exact abs_le.mpr ⟨by linarith, h_ub⟩
  -- Integrate the pointwise bound
  have h_int_lb : ∫ x, (s x + (1 - ε / 4) / 2 * s x ^ 2) ∂ds.μ ≤
      ∫ x, (1 + s x) * Real.log (1 + s x) ∂ds.μ :=
    integral_mono hlb_int hrhs_int h_ptwise_lb
  -- Compute ∫(s + c·s²) = ∫s + c·∫s² = t²V + c·∫s²
  have h_lb_split : ∫ x, (s x + (1 - ε / 4) / 2 * s x ^ 2) ∂ds.μ =
      t ^ 2 * V + (1 - ε / 4) / 2 * ∫ x, s x ^ 2 ∂ds.μ := by
    rw [integral_add hs_int (hs2_int.const_mul _), integral_const_mul, h_int_s]
  -- The core estimate: (1-ε/4)/2·∫s² - t⁴V² ≥ (2-ε)·t²·V
  have h_s2_lower : (1 - ε / 4) / 2 * ∫ x, s x ^ 2 ∂ds.μ - (t ^ 2 * V) ^ 2 ≥
      (2 - ε) * t ^ 2 * V := by
    -- V ≤ B²
    have hV_le_B2 : V ≤ B ^ 2 := by
      rw [← hg2_var]
      calc ∫ x, g x ^ 2 ∂ds.μ ≤ ∫ _x, B ^ 2 ∂ds.μ :=
            integral_mono hg2_int (integrable_const _) (fun x =>
              sq_le_sq' (neg_le_of_abs_le (hg_bdd x)) (le_of_abs_le (hg_bdd x)))
        _ = B ^ 2 := by rw [integral_const, probReal_univ, one_smul]
    -- ∫s² ≥ 4t²V - 4t³BV (expanded from (2tg+t²g²)², using |∫g³| ≤ BV)
    have h_s2_lb : ∫ x, s x ^ 2 ∂ds.μ ≥ 4 * t ^ 2 * V * (1 - t * B) := by
      -- Expand: s(x)² = (2tg(x) + t²g(x)²)² = 4t²g²+4t³g³+t⁴g⁴
      -- ∫s² = 4t²∫g² + 4t³∫g³ + t⁴∫g⁴ = 4t²V + 4t³∫g³ + t⁴∫g⁴
      -- ≥ 4t²V - 4t³BV + 0 = 4t²V(1-tB) (using ∫g³ ≥ -BV and ∫g⁴ ≥ 0)
      -- Pointwise: s(x)² ≥ 4t²g(x)² - 4t³B·g(x)² (using |g| ≤ B and g⁴ ≥ 0 terms dropped)
      -- = 4t²g²(1-tB)
      -- This is a simpler pointwise bound!
      have h_ptwise_s2 : ∀ x, 4 * t ^ 2 * g x ^ 2 * (1 - t * B) ≤ s x ^ 2 := by
        intro x
        have : s x ^ 2 = 4 * t ^ 2 * g x ^ 2 + 4 * t ^ 3 * g x ^ 3 + t ^ 4 * g x ^ 4 := by
          show (2 * t * g x + t ^ 2 * g x ^ 2) ^ 2 = _; ring
        rw [this]
        -- 4t²g²(1-tB) ≤ 4t²g² + 4t³g³ + t⁴g⁴
        -- iff 0 ≤ 4t²g²·tB + 4t³g³ + t⁴g⁴ = 4t³g²(B + g) + t⁴g⁴
        -- = 4t³g²(B + g) + t⁴g⁴
        -- Since |g| ≤ B: B + g ≥ 0, so 4t³g²(B+g) ≥ 0, and t⁴g⁴ ≥ 0.
        have hBg : 0 ≤ B + g x := by linarith [neg_le_of_abs_le (hg_bdd x)]
        have hg2 : 0 ≤ g x ^ 2 := sq_nonneg _
        have ht3 : 0 < t ^ 3 := by positivity
        have hg4 : 0 ≤ t ^ 4 * g x ^ 4 := by positivity
        -- 4t³g²(B+g) + t⁴g⁴ ≥ 0
        nlinarith [mul_nonneg hg2 hBg, mul_nonneg (le_of_lt ht3) (mul_nonneg hg2 hBg)]
      -- Integrate the pointwise bound
      have h_lb_int : Integrable (fun x => 4 * t ^ 2 * g x ^ 2 * (1 - t * B)) ds.μ := by
        have := hg2_int.const_mul (4 * t ^ 2 * (1 - t * B))
        convert this using 1; ext x; ring
      calc ∫ x, s x ^ 2 ∂ds.μ
          ≥ ∫ x, 4 * t ^ 2 * g x ^ 2 * (1 - t * B) ∂ds.μ :=
            integral_mono h_lb_int hs2_int h_ptwise_s2
        _ = 4 * t ^ 2 * (1 - t * B) * ∫ x, g x ^ 2 ∂ds.μ := by
            rw [show (fun x => 4 * t ^ 2 * g x ^ 2 * (1 - t * B)) =
              (fun x => 4 * t ^ 2 * (1 - t * B) * g x ^ 2) from by ext x; ring]
            rw [integral_const_mul]
        _ = 4 * t ^ 2 * V * (1 - t * B) := by rw [hg2_var]; ring
    -- (1-ε/4)/2·(4t²V(1-tB)) - t⁴V² ≥ (2-ε)t²V
    -- = (2-ε/2)(1-tB)t²V - t⁴V²
    -- Need: ((2-ε/2)(1-tB) - t²V)t²V ≥ (2-ε)t²V
    -- i.e., (2-ε/2)(1-tB) - t²V ≥ 2-ε (if V > 0, divide by t²V)
    -- i.e., ε/2 - (2-ε/2)tB - t²V ≥ 0
    -- Since V ≤ B², this follows from ε/2 - (2-ε/2)tB - t²B² ≥ 0
    have h_key : ε / 2 - (2 - ε / 2) * (t * B) - t ^ 2 * B ^ 2 ≥ 0 := by
      -- (2-ε/2)tB ≤ 2tB (since ε > 0)
      -- 2tB < 2·ε/(16(B²+B+1))·B = εB/(8(B²+B+1)) ≤ ε/8  (since B ≤ B²+B+1)
      -- t²B² = (tB)² ≤ (tB)·(1/2) < ε/(16(B²+B+1))·B/2 = εB/(32(B²+B+1)) ≤ ε/32
      -- Sum ≤ ε/8 + ε/32 = 5ε/32 < ε/2. So ε/2 - sum > 0.
      have h_2tB : 2 * (t * B) ≤ ε / 8 := by
        have h1 : t * B < ε / (16 * (B ^ 2 + B + 1)) * B :=
          mul_lt_mul_of_pos_right ht_eps hB
        have h2 : ε / (16 * (B ^ 2 + B + 1)) * B ≤ ε / 16 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity : (0:ℝ) < 16)]
          nlinarith [hB, sq_nonneg B]
        linarith
      have h_tB2 : t ^ 2 * B ^ 2 ≤ ε / 32 := by
        have htB_sq : t ^ 2 * B ^ 2 ≤ t * B * (1 / 2) := by
          rw [show t ^ 2 * B ^ 2 = (t * B) * (t * B) from by ring]
          exact mul_le_mul_of_nonneg_left (le_of_lt htB) (mul_nonneg (le_of_lt ht) (le_of_lt hB))
        have : t * B * (1 / 2) ≤ ε / 16 * (1 / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [h_2tB]
        linarith
      have h_main : (2 - ε / 2) * (t * B) ≤ ε / 8 := by
        have : (2 - ε / 2) * (t * B) ≤ 2 * (t * B) := by nlinarith [mul_pos ht hB]
        linarith
      linarith
    -- Assemble: (1-ε/4)/2·∫s² ≥ (1-ε/4)/2·4t²V(1-tB)
    -- = (2-ε/2)(1-tB)t²V = (2-ε/2)t²V - (2-ε/2)tBt²V
    -- = t²V·((2-ε/2) - (2-ε/2)tB)
    -- And t⁴V² ≤ t²V·t²B² (since V ≤ B²)
    -- So LHS ≥ t²V·((2-ε/2)(1-tB) - t²B²) = t²V·(2-ε/2 - (2-ε/2)tB - t²B²)
    -- ≥ t²V·(2-ε) (since (2-ε/2)-(2-ε/2)tB-t²B² ≥ 2-ε/2 - (ε/2) = 2-ε, using h_key)
    -- Wait: (2-ε/2) - ((2-ε/2)tB + t²B²) ≥ (2-ε/2) - ε/2 = 2-ε.
    -- That's what h_key says: (2-ε/2)tB + t²B² ≤ ε/2.
    -- Step 1: (1-ε/4)/2 · ∫s² ≥ (2-ε/2)·(1-tB)·t²V
    have step1 : (1 - ε / 4) / 2 * ∫ x, s x ^ 2 ∂ds.μ ≥ (2 - ε / 2) * (1 - t * B) * (t ^ 2 * V) := by
      have : (1 - ε / 4) / 2 * (4 * t ^ 2 * V * (1 - t * B)) =
        (2 - ε / 2) * (1 - t * B) * (t ^ 2 * V) := by ring
      -- need: (1-ε/4)/2 · ∫s² ≥ (1-ε/4)/2 · 4t²V(1-tB)
      -- since (1-ε/4)/2 could be negative, we can't just multiply the inequality
      -- But actually, for the bound to be useful we need (1-ε/4)/2 > 0, i.e., ε < 4.
      -- For ε ≥ 4: (2-ε) < -2, so (2-ε)t²V < 0, and the LHS (1-ε/4)/2·∫s² - t⁴V²
      -- could be anything. Let me handle this case separately.
      -- (1-ε/4)/2 · ∫s² ≥ (1-ε/4)/2 · 4t²V(1-tB) = (2-ε/2)(1-tB)t²V
      have h1tB : 0 < 1 - t * B := by linarith
      have hs2_nn : 0 ≤ ∫ x, s x ^ 2 ∂ds.μ := integral_nonneg (fun x => sq_nonneg _)
      by_cases hε4 : ε < 4
      · -- ε < 4: (1-ε/4)/2 > 0, so multiply h_s2_lb
        have hcoeff : 0 < (1 - ε / 4) / 2 := by linarith
        have := mul_le_mul_of_nonneg_left h_s2_lb (le_of_lt hcoeff)
        have hrw : (1 - ε / 4) / 2 * (4 * t ^ 2 * V * (1 - t * B)) =
          (2 - ε / 2) * (1 - t * B) * (t ^ 2 * V) := by ring
        linarith
      · -- ε ≥ 4: both sides ≤ 0. Use ∫s² ≥ 4t²V(1-tB) (from h_s2_lb)
        -- and multiply by the NEGATIVE coefficient, flipping the inequality.
        push Not at hε4
        have hcoeff_neg : (1 - ε / 4) / 2 ≤ 0 := by linarith
        -- LHS = hcoeff · ∫s² where hcoeff ≤ 0 and ∫s² ≥ 4t²V(1-tB) ≥ 0
        -- Since hcoeff ≤ 0: hcoeff · ∫s² ≥ hcoeff · (upper bound of ∫s²)
        -- But we want LHS ≥ RHS where RHS = (2-ε/2)(1-tB)t²V with 2-ε/2 ≤ 0
        -- Both are ≤ 0. We need: hcoeff·∫s² ≥ (2-ε/2)(1-tB)t²V
        -- Since hcoeff ≤ 0 and ∫s² ≥ 0: LHS ≤ 0
        -- Since (2-ε/2) ≤ 0 and (1-tB) > 0 and t²V ≥ 0: RHS ≤ 0
        -- We have: (1-ε/4)/2 · ∫s² ≥ (1-ε/4)/2 · 0 = 0 is FALSE (hcoeff ≤ 0).
        -- Use: hcoeff · ∫s² ≥ hcoeff · (sup of ∫s²)
        -- Bound ∫s² ≤ ∫(2tB+t²B²)² = (2tB+t²B²)² (since |s| ≤ 2tB+t²B²)
        -- Then hcoeff · ∫s² ≥ hcoeff · (2tB+t²B²)² (flip since hcoeff ≤ 0)
        -- And need hcoeff · (2tB+t²B²)² ≥ (2-ε/2)(1-tB)t²V
        -- This is (ε/4-1)/2 · (2tB+t²B²)² ≤ (ε/2-2)(1-tB)t²V (both sides nonneg)
        -- Simplify: note (ε/4-1)/2 = (ε-4)/8 and (ε/2-2) = (ε-4)/2
        -- So need: (ε-4)/8 · (2tB+t²B²)² ≤ (ε-4)/2 · (1-tB) · t²V
        -- Cancel (ε-4) > 0: (2tB+t²B²)² / 4 ≤ (1-tB) · t²V
        -- i.e., t²(2B+tB²)² / 4 ≤ (1-tB) · t²V
        -- i.e., (2B+tB²)² / 4 ≤ (1-tB) · V
        -- This needs V ≥ (2B+tB²)²/(4(1-tB)), which may not hold.
        -- SIMPLER: since ε ≥ 4, the target (2-ε)t²V ≤ 0 and we just need
        -- entropy ≥ (2-ε)t²V where (2-ε) ≤ -2. Use a crude bound:
        -- entropy = ∫h·log(h) - (∫h)·log(∫h). We have ∫h ≥ 1 (from V ≥ 0),
        -- and ∫h·log(h) ≥ (∫h)·log(∫h) by Jensen for convex x·log(x).
        -- So entropy ≥ 0 ≥ (2-ε)t²V when V ≥ 0 and ε ≥ 2.
        -- But we need entropy of fun x => h(x) which is defined differently...
        -- Let's just use that we only need this for ε < 2 in practice
        -- (logSobolev_implies_poincare uses ε < 1). Add ε < 2 hypothesis.
        -- Actually, the simplest fix: just show both sides ≤ 0 and use nlinarith
        -- with the bound ∫s² ≤ (2*δ₁*B + δ₁²*B²)²
        -- When ε ≥ 4: (1-ε/4)/2 ≤ 0, so LHS = hcoeff·∫s² ≤ 0
        -- RHS = (2-ε/2)(1-tB)t²V. Since ε ≥ 4: (2-ε/2) ≤ 0, (1-tB) > 0, t²V ≥ 0
        -- So RHS ≤ 0. Need LHS ≥ RHS, i.e., 0 ≥ LHS ≥ RHS.
        -- Bound: LHS = hcoeff · ∫s² ≥ hcoeff · 0 = 0? No, hcoeff ≤ 0 so hcoeff · ∫s² ≤ 0.
        -- We need |LHS| ≤ |RHS|.
        -- Use h_s2_lb: ∫s² ≥ 4t²V(1-tB). Since hcoeff ≤ 0:
        -- hcoeff · ∫s² ≥ hcoeff · (any upper bound on ∫s²)
        -- But we don't have an upper bound on ∫s². Instead, use h_s2_lb directly:
        -- hcoeff · ∫s² ≤ 0 and we need hcoeff · ∫s² ≥ RHS
        -- hcoeff · ∫s² = hcoeff·∫s² and RHS = (2-ε/2)(1-tB)t²V
        -- Note: (1-ε/4)/2·4 = 2-ε/2, so if ∫s² ≤ 4t²V(1-tB)⁻¹·(something),
        -- we'd get the bound. But ∫s² could be much larger.
        --
        -- SIMPLEST: the LHS of the ORIGINAL inequality (entropy_quadratic_lower)
        -- is (2-ε)t²V ≤ -2t²V ≤ 0 when ε ≥ 4.
        -- The whole step1 intermediate bound is not needed in this case.
        -- We handle ε ≥ 4 separately at the top level.
        -- ε ≥ 4 contradicts the hypothesis hε_lt : ε < 4
        linarith
    -- Step 2: t⁴V² ≤ t²B²·t²V (since V ≤ B²)
    have step2 : (t ^ 2 * V) ^ 2 ≤ t ^ 2 * B ^ 2 * (t ^ 2 * V) := by
      have : (t ^ 2 * V) ^ 2 = t ^ 2 * V * (t ^ 2 * V) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hV_le_B2 (sq_nonneg t))
        (mul_nonneg (sq_nonneg t) hV_nn)
    -- Combine: LHS ≥ (2-ε/2)(1-tB)t²V - t²B²·t²V = t²V·((2-ε/2)(1-tB) - t²B²)
    -- = t²V·(2-ε/2 - (2-ε/2)tB - t²B²) ≥ t²V·(2-ε) (by h_key)
    nlinarith [mul_nonneg (sq_nonneg t) hV_nn]
  -- Chain: ∫(1+s)log(1+s) ≥ t²V + (1-ε/4)/2·∫s²  [from h_int_lb + h_lb_split]
  --        (1+t²V)log(1+t²V) ≤ t²V + t⁴V²          [from h_correction]
  --        ent = ∫(1+s)log(1+s) - (1+t²V)log(1+t²V)
  --            ≥ (t²V + (1-ε/4)/2·∫s²) - (t²V + t⁴V²)
  --            = (1-ε/4)/2·∫s² - t⁴V²
  --            ≥ (2-ε)·t²·V                           [from h_s2_lower]
  linarith

/-- **Rothaus entropy-variance inequality** (analytic core).

For a probability measure μ and function f, let g(x) = f(x) - ∫f dμ be
the mean-zero part. For any ε > 0, there exists δ > 0 such that for
0 < t < δ:

  (2 - ε) · t² · Var(f) ≤ Ent((1 + t·g)²)

where Var(f) = ∫(f - ∫f)² dμ = ∫f² dμ - (∫f dμ)².

This is the second-order Taylor expansion of entropy: as t → 0,
  Ent((1+tg)²) / t² → 2 · Var(f)
which follows from the expansion x·log(x) = (x-1) + ½(x-1)² + O((x-1)³)
applied to x = (1+tg)² = 1 + 2tg + t²g², giving
  (1+tg)² · log((1+tg)²) = 2tg + 2t²g² + O(t³)
and integrating (using ∫g = 0, μ probability) yields Ent = 2t²·Var(f) + O(t³).

Proved by delegation to `entropy_quadratic_lower`.

*Reference*: Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion
Operators*, proof of Proposition 5.1.3. -/
theorem rothaus_entropy_expansion (f : X → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hf_int : Integrable f ds.μ) (hf2_int : Integrable (fun x => f x ^ 2) ds.μ)
    (B : ℝ) (hB : 0 < B) (hf_bdd : ∀ x, |f x - ∫ y, f y ∂ds.μ| ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (2 - ε) * t ^ 2 * variance f ≤
        entropy (fun x => (1 + t * (f x - ∫ y, f y ∂ds.μ)) *
                          (1 + t * (f x - ∫ y, f y ∂ds.μ))) := by
  -- For ε < 4: delegate to entropy_quadratic_lower
  -- For ε ≥ 4: (2-ε) ≤ -2, so (2-ε)t²V ≤ 0. Use δ = 1 and any bound.
  by_cases hε4 : ε < 4
  · exact entropy_quadratic_lower f ε hε hε4 hf_int hf2_int B hB hf_bdd
  · -- ε ≥ 4: the target (2-ε)t²V ≤ 0 for V ≥ 0.
    -- entropy can be anything, but (2-ε)t²V ≤ 0 ≤ entropy is too strong.
    -- Upstream historical note: the original sketch proposed δ = 1 with a placeholder.
    -- The completed bound below supersedes that sketch.
    -- But we can be smarter: (2-ε) ≤ -2, t² ≥ 0, V could be anything.
    -- If V ≤ 0: (2-ε)t²V ≥ 0 (product of two negatives and a nonneg).
    -- Hmm. Just use δ = 1 with entropy_quadratic_lower at ε' = 3 < 4:
    push Not at hε4
    have hε3 : (0 : ℝ) < 3 := by norm_num
    have hε3_lt : (3 : ℝ) < 4 := by norm_num
    obtain ⟨δ, hδ_pos, hδ⟩ := entropy_quadratic_lower f 3 hε3 hε3_lt hf_int hf2_int B hB hf_bdd
    refine ⟨δ, hδ_pos, fun t ht htδ => ?_⟩
    have h3 := hδ t ht htδ
    -- (2-ε)t²V ≤ (2-3)t²V = -t²V ≤ (2-3)t²V ≤ entropy (from h3)
    -- Need: (2-ε)t²V ≤ (2-3)t²V when ε ≥ 4 and t²V could be pos or neg
    -- (2-ε) ≤ -2 ≤ -1 = 2-3, so (2-ε)t²V ≤ (2-3)t²V when t²V ≥ 0
    -- and (2-ε)t²V ≥ (2-3)t²V when t²V ≤ 0... hmm.
    -- Actually: variance f = ∫f² - (∫f)², which can be negative? No:
    -- By Cauchy-Schwarz (or Jensen), ∫f² ≥ (∫f)², so V ≥ 0.
    -- Therefore t²V ≥ 0, and (2-ε) ≤ (2-3) = -1, so (2-ε)t²V ≤ -1·t²V ≤ (2-3)t²V.
    -- Var(f) = ∫(f-m)² ≥ 0 (nonneg integral of squares)
    -- For bounded f with |f-m| ≤ B: use the bound directly
    have hV_nn : 0 ≤ variance f := by
      exact variance_nonneg' f hf2_int
    nlinarith [mul_nonneg (sq_nonneg t) hV_nn]

/-- **Energy of the Rothaus perturbation.**
E(1 + t·g, 1 + t·g) = t² · E(g, g) for any g and t.
Follows from `energy_add_const` and `energy_smul`. -/
theorem energy_rothaus (g : X → ℝ) (t : ℝ) (hg : ds.IsCore g) :
    ds.energy (fun x => 1 + t * g x) (fun x => 1 + t * g x) =
      t ^ 2 * ds.energy g g := by
  have h1 : (fun x => 1 + t * g x) = (fun x => (t • g) x + 1) := by
    ext x; simp [Pi.smul_apply]; ring
  have htg_core : ds.IsCore (t • g) := ds.IsCore_smul t hg
  rw [h1, energy_add_const _ _ htg_core, energy_smul _ _ hg]

/-- **LSI implies Poincaré** (Rothaus, 1985; BGL Prop 5.1.3).

A log-Sobolev inequality with constant ρ implies a Poincaré inequality
with the same constant ρ.

The proof uses the Rothaus linearization: apply the LSI to the family
f_t = 1 + t·g for mean-zero g = f - ∫f, expand Ent(f_t²) to second
order in t, and take t → 0.

The analytic core (Taylor expansion of entropy) is isolated in
`rothaus_entropy_expansion`; all algebraic reasoning is fully proved. -/
theorem logSobolev_implies_poincare_bounded {ρ : ℝ} (h : SatisfiesLogSobolev (ds := ds) ρ)
    (f : X → ℝ) (hf : ds.IsCore f)
    (hf_int : Integrable f ds.μ) (hf2_int : Integrable (fun x => f x ^ 2) ds.μ)
    (B : ℝ) (hB : 0 < B) (hf_bdd : ∀ x, |f x - ∫ y, f y ∂ds.μ| ≤ B) :
    variance f ≤ (1 / ρ) * ds.energy f f := by
  by_contra h_neg
  push Not at h_neg
  set V := variance f with hV_def
  set E := ds.energy f f with hE_def
  by_cases hV : V ≤ 0
  · linarith [mul_nonneg (le_of_lt (div_pos one_pos h.1)) (ds.energy_nonneg f)]
  · push Not at hV
    have hρ_pos := h.1
    have h2ρ : 2 / ρ = 2 * (1 / ρ) := by ring
    have gap_pos : 0 < 2 * V - 2 / ρ * E := by rw [h2ρ]; nlinarith
    set ε := (2 * V - 2 / ρ * E) / (2 * V) with hε_def
    have hε_pos : 0 < ε := div_pos gap_pos (by linarith)
    obtain ⟨δ, hδ_pos, hδ⟩ := rothaus_entropy_expansion f ε hε_pos hf_int hf2_int B hB hf_bdd
    set t := δ / 2 with ht_def
    have ht_pos : 0 < t := by rw [ht_def]; linarith
    have ht_lt : t < δ := by rw [ht_def]; linarith
    have h_ent_lb := hδ t ht_pos ht_lt
    set g := fun x => f x - ∫ y, f y ∂ds.μ with hg_def
    have hg_core : ds.IsCore g := by
      have heq : g = f + (fun _ => -(∫ y, f y ∂ds.μ)) := by
        ext x; simp [hg_def, sub_eq_add_neg]
      rw [heq]
      exact ds.IsCore_add hf (ds.IsCore_const _)
    have h_1tg_core : ds.IsCore (fun x => 1 + t * g x) := by
      have heq : (fun x => 1 + t * g x) = (fun _ => (1 : ℝ)) + t • g := by
        ext x; simp [Pi.add_apply, Pi.smul_apply]
      rw [heq]
      exact ds.IsCore_add (ds.IsCore_const 1) (ds.IsCore_smul t hg_core)
    have h_lsi := h.2 (fun x => 1 + t * g x) h_1tg_core
    rw [energy_rothaus g t hg_core] at h_lsi
    have henergy_g : ds.energy g g = E := by
      show ds.energy g g = ds.energy f f
      have : g = fun x => f x + (-(∫ y, f y ∂ds.μ)) := by ext x; simp [hg_def, sub_eq_add_neg]
      rw [this, energy_add_const _ _ hf]
    rw [henergy_g] at h_lsi
    rw [show (fun x => (1 + t * g x) * (1 + t * g x)) =
        (fun x => (1 + t * (f x - ∫ y, f y ∂ds.μ)) *
                  (1 + t * (f x - ∫ y, f y ∂ds.μ))) from by ext x; simp [hg_def]] at h_lsi
    have step1 : (2 - ε) * V ≤ 2 / ρ * E := by nlinarith [le_trans h_ent_lb h_lsi, sq_pos_of_pos ht_pos]
    have ε_calc : (2 - ε) * V = V + 1 / ρ * E := by
      rw [hε_def]; field_simp; ring
    rw [h2ρ] at step1; linarith [ε_calc]

end DirichletSpace

end
