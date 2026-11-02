/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# OU entropy decay: historical decomposition into atomic bridges

The following introduction records an earlier upstream postulate-based
plan. The two bridges now have proof bodies; the local compiled audit
supersedes this historical inventory.

This file packages **two atomic textbook bridges** for the Gaussian
Ornstein-Uhlenbeck semigroup on `ℝ`:

* `ouSemigroup_fisher_info_decay` — Bakry-Émery gradient decay for the
  Fisher information (BGL Prop 5.5.2, Jensen-on-`x²/y` argument).
* `hasDerivAt_entropy_ouSemigroup` — de Bruijn identity: the entropy
  `∫ g · log g dγ` differentiated under the OU heat flow equals minus
  the Fisher information (BGL §5.5).

Together these two facts (plus FTC and a one-line algebraic identity)
discharge the previous broad axiom `ouSemigroup_entropy_sq_decay_bound`
(BGL Theorem 5.5.2). The discharge lives in
`Instances/WorkInProgress/EuclideanEntropyDecay.lean`.

Both axioms require a positive lower bound `g ≥ ε > 0` on the function;
this is the standard regularization handling `log 0` in the textbook
proof. The application to `f²` proceeds via `g := f² + ε` plus a limit
`ε → 0`.

## Why split into two axioms?

The original axiom bundled "rate identity" + "gradient decay" + "FTC"
into a single statement. Splitting yields:
1. Each piece is a standalone textbook fact, vettable independently.
2. The Fisher info decay (A1) closely parallels `ouSemigroup_gradient_decay`
   which we proved — same Jensen + γ-invariance structure, just with
   `(g')²/g` instead of `(g')²`.
3. The de Bruijn identity (A2) is parametric-integral differentiation
   structurally identical to `hasDerivAt_l2sq_ouSemigroup_pos` which
   we proved — but applied to the `s · log s` integrand instead of
   `s²`.
4. Both axioms are reusable for future `BakryEmerySpace` instances.

## References

* Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, §5.5 (de Bruijn identity, Fisher information decay,
  entropy decay under Bakry-Émery curvature).
* Bakry-Émery (1985) "Diffusions hypercontractives", §I.
-/

/- Port history note: inherited comments describing placeholders or legacy
postulates refer to earlier upstream development stages. Local proof status
is determined by the compiled axiom audit and the accompanying port note. -/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.Euclidean
import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanStein

open MeasureTheory Filter Set Real ProbabilityTheory Topology

open scoped ContDiff

noncomputable section

namespace Gaussian1D

/-- The Fisher information of `g : ℝ → ℝ` against the standard Gaussian:
`I(g) = ∫ (g'(y))² / g(y) dγ(y)`.

For our purposes `g` is bounded below by some `ε > 0`, so the division
is well-defined everywhere. -/
def fisherInfo (g : ℝ → ℝ) : ℝ :=
  ∫ y, (deriv g y) ^ 2 / g y ∂γ

/-- The Boltzmann-style entropy `H(g) = ∫ g · log g dγ` (no `(∫g) log(∫g)`
subtraction at this granularity — the centered version is in
`DirichletSpace.entropy`). For `g ≥ ε > 0`, this is a smooth functional. -/
def boltzmannEntropy (g : ℝ → ℝ) : ℝ :=
  ∫ y, g y * Real.log (g y) ∂γ

/-! ## Cauchy-Schwarz helper -/

/-- **Cauchy-Schwarz inequality for the standard Gaussian measure.**
For functions `A, B : ℝ → ℝ` with `A·B`, `A²`, `B²` all γ-integrable,
`(∫ A·B dγ)² ≤ (∫ A² dγ)·(∫ B² dγ)`.

Proved via the polynomial discriminant: for every `λ ∈ ℝ`,
`0 ≤ ∫ (A - λ·B)² dγ`, then expanded and optimized in `λ`. -/
private lemma cauchy_schwarz_gamma (A B : ℝ → ℝ)
    (hAB : Integrable (fun y => A y * B y) γ)
    (hA2 : Integrable (fun y => A y ^ 2) γ)
    (hB2 : Integrable (fun y => B y ^ 2) γ) :
    (∫ y, A y * B y ∂γ) ^ 2 ≤ (∫ y, A y ^ 2 ∂γ) * (∫ y, B y ^ 2 ∂γ) := by
  set IA := ∫ y, A y ^ 2 ∂γ with hIA
  set IB := ∫ y, B y ^ 2 ∂γ with hIB
  set IAB := ∫ y, A y * B y ∂γ with hIAB
  have hIA_nn : 0 ≤ IA :=
    integral_nonneg (fun y => sq_nonneg _)
  have hIB_nn : 0 ≤ IB :=
    integral_nonneg (fun y => sq_nonneg _)
  by_cases hIB0 : IB = 0
  · -- If ∫B² = 0, then B = 0 a.e., so ∫A·B = 0.
    have hB_ae : (fun y => B y ^ 2) =ᵐ[γ] 0 := by
      have h_nn_ae : ∀ᵐ y ∂γ, 0 ≤ B y ^ 2 :=
        Filter.Eventually.of_forall (fun y => sq_nonneg _)
      exact (integral_eq_zero_iff_of_nonneg_ae h_nn_ae hB2).mp hIB0
    have hAB_ae : (fun y => A y * B y) =ᵐ[γ] 0 := by
      filter_upwards [hB_ae] with y hy
      have : B y = 0 := sq_eq_zero_iff.mp hy
      simp [this]
    have hIAB0 : IAB = 0 := by
      rw [hIAB]; exact integral_eq_zero_of_ae hAB_ae
    rw [hIAB0, hIB0]; simp
  · have hIB_pos : 0 < IB := lt_of_le_of_ne hIB_nn (Ne.symm hIB0)
    -- Optimal λ := IAB / IB makes ∫(A - λB)² = IA - IAB²/IB ≥ 0.
    set lam : ℝ := IAB / IB with h_lam_def
    have h_expand : ∫ y, (A y - lam * B y) ^ 2 ∂γ
        = IA - 2 * lam * IAB + lam ^ 2 * IB := by
      have h_eq : ∀ y, (A y - lam * B y) ^ 2
          = A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2 := fun y => by ring
      have h_sum_int :
          Integrable (fun y => A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2) γ :=
        (hA2.sub (hAB.const_mul (2 * lam))).add (hB2.const_mul (lam ^ 2))
      calc ∫ y, (A y - lam * B y) ^ 2 ∂γ
          = ∫ y, A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2 ∂γ :=
            integral_congr_ae (Filter.Eventually.of_forall h_eq)
        _ = (∫ y, A y ^ 2 - 2 * lam * (A y * B y) ∂γ) + ∫ y, lam ^ 2 * B y ^ 2 ∂γ :=
            integral_add (hA2.sub (hAB.const_mul (2 * lam))) (hB2.const_mul (lam ^ 2))
        _ = ((∫ y, A y ^ 2 ∂γ) - ∫ y, 2 * lam * (A y * B y) ∂γ)
            + ∫ y, lam ^ 2 * B y ^ 2 ∂γ := by
            rw [integral_sub hA2 (hAB.const_mul (2 * lam))]
        _ = IA - 2 * lam * IAB + lam ^ 2 * IB := by
            rw [integral_const_mul, integral_const_mul]
    have h_nn : 0 ≤ ∫ y, (A y - lam * B y) ^ 2 ∂γ :=
      integral_nonneg (fun y => sq_nonneg _)
    rw [h_expand] at h_nn
    -- Rewrite h_nn entirely in terms of IAB²/IB.
    have h_nn' : 0 ≤ IA - IAB ^ 2 / IB := by
      have h_alg : IA - 2 * lam * IAB + lam ^ 2 * IB = IA - IAB ^ 2 / IB := by
        rw [h_lam_def]; field_simp; ring
      linarith [h_alg ▸ h_nn]
    have h_step : IAB ^ 2 / IB ≤ IA := by linarith
    have := mul_le_mul_of_nonneg_right h_step hIB_nn
    rwa [div_mul_cancel₀ _ hIB0] at this

/-! ## A1: Fisher information gradient decay (BGL Prop 5.5.2) -/

/-- **Bakry-Émery gradient decay for the Fisher information.** AXIOM
(vetting-required textbook bridge).

For any `C¹` `g : ℝ → ℝ` with `g, g'` bounded and `g ≥ ε > 0` pointwise,
the Fisher information `I(P_t g)` decays exponentially:

  `I(P_t g) = ∫ ((P_t g)'(y))² / (P_t g)(y) dγ(y)
              ≤ exp(-2t) · ∫ (g'(y))² / g(y) dγ(y) = exp(-2t) · I(g)`.

## Proof in textbooks

Two steps:
1. The Mehler derivative formula gives `(P_t g)'(x) = e^{-t} P_t(g')(x)`
   (already proved as `hasDerivAt_ouSemigroup_C1`).
2. Apply Jensen's inequality to the convex function `φ(x, y) = x² / y`
   on `{y > 0}`:
   `((P_t g)'(x))² / (P_t g)(x) = (e^{-t} P_t(g'))² / P_t(g)
       = e^{-2t} · (P_t(g'))² / (P_t g)
       ≤ e^{-2t} · P_t((g')²/g)`
   by Jensen on the Mehler probability kernel.
3. Integrate against γ and use γ-invariance of P_t (Fubini +
   `ou_kernel_map`):
   `∫ ((P_t g)')² / P_t g dγ ≤ e^{-2t} · ∫ P_t((g')²/g) dγ
       = e^{-2t} · ∫ (g')²/g dγ`.

The Jensen step is the Bakry-Émery curvature condition `Γ₂ ≥ Γ` in
disguise (for OU on ℝ with `ρ = 1`, this curvature bound is exact).

## Discharge plan

Per Gemini 3.1-pro vetting (verdict: **Standard**, 2026-05-12): the
cleanest discharge avoids the 2D-Jensen-on-`x²/y` argument. Instead,
apply Cauchy-Schwarz on the Mehler probability kernel
`μ_x(dy) := P_t(x, dy)`:
  `(P_t g'(x))² = (∫ (g'/√g) · √g dμ_x)²
       ≤ (∫ (g')²/g dμ_x) · (∫ g dμ_x)`
giving `(P_t g'(x))² / P_t g(x) ≤ P_t((g')²/g)(x)`. Then `P_t g'(x) =
e^t · (P_t g)'(x)`... wait — by `hasDerivAt_ouSemigroup_C1`,
`(P_t g)'(x) = e^{-t} · P_t g'(x)`. So
`((P_t g)'(x))² / (P_t g)(x) = e^{-2t} (P_t g')² / P_t g ≤ e^{-2t}
P_t((g')²/g)`. Finally integrate against γ + γ-invariance.

Expected effort: ~150-250 lines (substantially less than the 2D-Jensen
route — most of the work is the Cauchy-Schwarz application + γ-invariance
manipulation).

## References

* Bakry-Gentil-Ledoux, Proposition 5.5.2 and §5.5.
* Bakry-Émery (1985), "Diffusions hypercontractives," Prop. 1.

## Vetting

**Standard** (gemini-3.1-pro-preview, 2026-05-12). Hypotheses tight;
`ε ≤ g ⇒ P_t g ≥ ε` for free since `P_t` averages against a probability
kernel; exponent `exp(-2t)` correct for OU(1) Bakry-Émery curvature
`ρ = 1`. No counterexamples. -/
theorem ouSemigroup_fisher_info_decay
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    fisherInfo (ouSemigroup t g) ≤ Real.exp (-2 * t) * fisherInfo g := by
  -- Notation
  set a := Real.exp (-t) with ha_def
  set b := Real.sqrt (1 - Real.exp (-2 * t)) with hb_def
  -- Basic facts
  have hε_nn : 0 ≤ ε := hε.le
  have hM_nn : 0 ≤ M := hε_nn.trans ((hg_lo 0).trans (hg_hi 0))
  have ha_pos : 0 < a := Real.exp_pos _
  have ha_nn : 0 ≤ a := ha_pos.le
  have ha_sq : a ^ 2 = Real.exp (-2 * t) := by
    show Real.exp (-t) ^ 2 = Real.exp (-2 * t)
    rw [show (-2 * t : ℝ) = -t + -t from by ring, Real.exp_add]; ring
  have h_gpos : ∀ x, 0 < g x := fun x => lt_of_lt_of_le hε (hg_lo x)
  have h_gabs : ∀ x, |g x| ≤ M := fun x => by
    rw [abs_of_pos (h_gpos x)]; exact hg_hi x
  have hg_norm : ∀ x, ‖g x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs]; exact h_gabs x
  have hg'_norm : ∀ x, ‖deriv g x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs]; exact hg'_bd x
  -- Measurability
  have hg_meas : Measurable g := hg.continuous.measurable
  have hg'_meas : Measurable (deriv g) :=
    (hg.continuous_deriv le_rfl).measurable
  -- Linear inner map (a*x + b*y), measurable in y for fixed x.
  -- Set the integrand functions for each fixed x.
  -- P_t g x ≥ ε.
  have h_Ptg_lo : ∀ x, ε ≤ ouSemigroup t g x := by
    intro x
    show ε ≤ ∫ y, g (a * x + b * y) ∂γ
    have h_int : Integrable (fun y => g (a * x + b * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg_norm _
    have h_le : ∀ y, (ε : ℝ) ≤ g (a * x + b * y) := fun y => hg_lo _
    calc (ε : ℝ) = ∫ _, ε ∂γ := by simp
      _ ≤ ∫ y, g (a * x + b * y) ∂γ :=
            integral_mono (integrable_const _) h_int h_le
  have h_Ptg_pos : ∀ x, 0 < ouSemigroup t g x := fun x =>
    lt_of_lt_of_le hε (h_Ptg_lo x)
  -- P_t g x ≤ M.
  have h_Ptg_hi : ∀ x, ouSemigroup t g x ≤ M := by
    intro x
    show ∫ y, g (a * x + b * y) ∂γ ≤ M
    have h_int : Integrable (fun y => g (a * x + b * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg_norm _
    calc ∫ y, g (a * x + b * y) ∂γ
        ≤ ∫ _, M ∂γ :=
            integral_mono h_int (integrable_const _) (fun y => hg_hi _)
      _ = M := by simp
  -- Mehler derivative formula.
  have h_deriv : ∀ x,
      HasDerivAt (ouSemigroup t g) (a * ouSemigroup t (deriv g) x) x := fun x =>
    hasDerivAt_ouSemigroup_C1 t hg hg_norm hg'_norm x
  have h_deriv_eq : ∀ x,
      deriv (ouSemigroup t g) x = a * ouSemigroup t (deriv g) x := fun x =>
    (h_deriv x).deriv
  -- Pointwise Cauchy-Schwarz.
  -- For each x: with Q(y) := g'(a*x + b*y), R(y) := g(a*x + b*y),
  -- (∫ Q dγ)² ≤ (∫ Q²/R dγ)·(∫ R dγ), since Q = (Q/√R)·√R and R ≥ ε > 0.
  have h_inv_lin_meas : Measurable (fun p : ℝ × ℝ => a * p.1 + b * p.2) :=
    (measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)
  -- Integrability of (g')²/g composed with kernel, over γ.prod γ.
  -- Bound: |g'|² / g ≤ M² / ε since |g'| ≤ M, g ≥ ε.
  have h_M2eps_nn : 0 ≤ M ^ 2 / ε := div_nonneg (sq_nonneg _) hε_nn
  have h_qsq_over_r_bd : ∀ x, (deriv g x) ^ 2 / g x ≤ M ^ 2 / ε := by
    intro x
    have h1 : (deriv g x) ^ 2 ≤ M ^ 2 := by
      have hxabs : |deriv g x| ≤ M := hg'_bd x
      have : (deriv g x) ^ 2 = |deriv g x| ^ 2 := by rw [sq_abs]
      rw [this]
      exact pow_le_pow_left₀ (abs_nonneg _) hxabs 2
    have h2 : (deriv g x) ^ 2 / g x ≤ (deriv g x) ^ 2 / ε :=
      div_le_div_of_nonneg_left (sq_nonneg _) hε (hg_lo x)
    have h3 : (deriv g x) ^ 2 / ε ≤ M ^ 2 / ε :=
      div_le_div_of_nonneg_right h1 hε_nn
    linarith
  have h_qsq_over_r_nn : ∀ x, 0 ≤ (deriv g x) ^ 2 / g x := fun x =>
    div_nonneg (sq_nonneg _) (h_gpos x).le
  -- Measurability of (deriv g y)² / g y.
  have h_qsq_over_r_meas : Measurable (fun y => (deriv g y) ^ 2 / g y) :=
    (hg'_meas.pow_const 2).div hg_meas
  -- The pointwise Cauchy-Schwarz bound:
  -- (∫ Q dγ)² ≤ (∫ Q²/R dγ) · (∫ R dγ)
  -- where Q(y) := g'(a*x + b*y), R(y) := g(a*x + b*y).
  -- Apply with A := Q/√R, B := √R; then A·B = Q, A² = Q²/R, B² = R.
  -- We need integrability of these functions.
  have h_cauchy : ∀ x,
      (ouSemigroup t (deriv g) x) ^ 2 ≤
        ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x * ouSemigroup t g x := by
    intro x
    -- Define A(y) := g'(a*x+b*y) / √(g(a*x+b*y)), B(y) := √(g(a*x+b*y))
    -- and apply cauchy_schwarz_gamma.
    set A : ℝ → ℝ := fun y => deriv g (a * x + b * y) / Real.sqrt (g (a * x + b * y))
    set B : ℝ → ℝ := fun y => Real.sqrt (g (a * x + b * y))
    have h_compose_pos : ∀ y, 0 < g (a * x + b * y) := fun y => h_gpos _
    have h_compose_lo : ∀ y, ε ≤ g (a * x + b * y) := fun y => hg_lo _
    have h_sqrt_pos : ∀ y, 0 < Real.sqrt (g (a * x + b * y)) := fun y =>
      Real.sqrt_pos.mpr (h_compose_pos y)
    have h_sqrt_sq : ∀ y, (Real.sqrt (g (a * x + b * y))) ^ 2 = g (a * x + b * y) := fun y =>
      Real.sq_sqrt (h_compose_pos y).le
    have h_AB : ∀ y, A y * B y = deriv g (a * x + b * y) := by
      intro y
      show (deriv g (a * x + b * y) / Real.sqrt (g (a * x + b * y))) *
          Real.sqrt (g (a * x + b * y)) = deriv g (a * x + b * y)
      have hsqrt_ne : Real.sqrt (g (a * x + b * y)) ≠ 0 := (h_sqrt_pos y).ne'
      field_simp
    have h_A2 : ∀ y, A y ^ 2 = (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) := by
      intro y
      show (deriv g (a * x + b * y) / Real.sqrt (g (a * x + b * y))) ^ 2
          = (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y)
      rw [div_pow, h_sqrt_sq]
    have h_B2 : ∀ y, B y ^ 2 = g (a * x + b * y) := h_sqrt_sq
    -- Measurability of A, B.
    have h_kernel_meas : Measurable (fun y => a * x + b * y) :=
      measurable_const.add (measurable_const.mul measurable_id)
    have h_sqrt_meas : Measurable Real.sqrt := Real.continuous_sqrt.measurable
    have hA_meas : Measurable A :=
      (hg'_meas.comp h_kernel_meas).div (h_sqrt_meas.comp (hg_meas.comp h_kernel_meas))
    have hB_meas : Measurable B :=
      h_sqrt_meas.comp (hg_meas.comp h_kernel_meas)
    -- Integrability.
    have h_AB_int : Integrable (fun y => A y * B y) γ := by
      refine Integrable.mono' (integrable_const M)
        (hA_meas.mul hB_meas).aestronglyMeasurable ?_
      filter_upwards with y
      rw [h_AB]
      exact hg'_norm _
    have h_A2_int : Integrable (fun y => A y ^ 2) γ := by
      refine Integrable.mono' (integrable_const (M ^ 2 / ε)) ?_ ?_
      · exact (hA_meas.pow_const 2).aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (by rw [h_A2]; exact h_qsq_over_r_nn _)]
        rw [h_A2]
        exact h_qsq_over_r_bd _
    have h_B2_int : Integrable (fun y => B y ^ 2) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hB_meas.pow_const 2).aestronglyMeasurable
      · filter_upwards with y
        rw [h_B2, Real.norm_eq_abs]
        exact h_gabs _
    have hCS := cauchy_schwarz_gamma A B h_AB_int h_A2_int h_B2_int
    -- Rewrite using h_AB, h_A2, h_B2.
    have h_lhs : (∫ y, A y * B y ∂γ) ^ 2 = (ouSemigroup t (deriv g) x) ^ 2 := by
      congr 1
      show ∫ y, A y * B y ∂γ = ∫ y, deriv g (a * x + b * y) ∂γ
      exact integral_congr_ae (Filter.Eventually.of_forall h_AB)
    have h_rhs_A2 : ∫ y, A y ^ 2 ∂γ
        = ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x := by
      show ∫ y, A y ^ 2 ∂γ = ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ
      exact integral_congr_ae (Filter.Eventually.of_forall h_A2)
    have h_rhs_B2 : ∫ y, B y ^ 2 ∂γ = ouSemigroup t g x := by
      show ∫ y, B y ^ 2 ∂γ = ∫ y, g (a * x + b * y) ∂γ
      exact integral_congr_ae (Filter.Eventually.of_forall h_B2)
    rw [h_lhs, h_rhs_A2, h_rhs_B2] at hCS
    exact hCS
  -- Combine with Mehler derivative:
  -- ((P_t g)'(x))² = a² · (P_t g'(x))² ≤ a² · P_t((g')²/g)(x) · P_t g(x).
  -- Divide by P_t g(x) ≥ ε > 0:
  -- ((P_t g)'(x))² / P_t g(x) ≤ a² · P_t((g')²/g)(x).
  have h_ptwise : ∀ x,
      (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x ≤
        a ^ 2 * ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x := by
    intro x
    have hPtg_pos := h_Ptg_pos x
    have h_step1 : (deriv (ouSemigroup t g) x) ^ 2 =
        a ^ 2 * (ouSemigroup t (deriv g) x) ^ 2 := by
      rw [h_deriv_eq x]; ring
    have h_step2 : a ^ 2 * (ouSemigroup t (deriv g) x) ^ 2 ≤
        a ^ 2 * (ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x * ouSemigroup t g x) :=
      mul_le_mul_of_nonneg_left (h_cauchy x) (sq_nonneg _)
    have h_combined : (deriv (ouSemigroup t g) x) ^ 2 ≤
        a ^ 2 * (ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x) * ouSemigroup t g x := by
      rw [h_step1, mul_assoc]
      exact h_step2
    -- Divide by P_t g(x) > 0.
    have h_div : (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x ≤
        a ^ 2 * ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x := by
      have := div_le_div_of_nonneg_right h_combined hPtg_pos.le
      -- (a² · P · Q) / Q = a² · P when Q > 0.
      have hQ_ne : ouSemigroup t g x ≠ 0 := hPtg_pos.ne'
      rw [mul_div_assoc, div_self hQ_ne, mul_one] at this
      exact this
    exact h_div
  -- Now integrate the pointwise bound against γ, and use γ-invariance of P_t.
  -- LHS: ∫ ((P_t g)')² / P_t g dγ = fisherInfo (P_t g).
  -- RHS: a² · ∫ P_t((g')²/g) dγ = a² · ∫ (g')²/g dγ = a² · fisherInfo g.
  -- γ-invariance of P_t for (g')²/g.
  have h_inv : ∫ x, ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x ∂γ =
      ∫ y, (deriv g y) ^ 2 / g y ∂γ := by
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ_meas : Measurable φ := h_inv_lin_meas
    have hmap := ou_kernel_map t ht
    have hg'_over_g_φ_int : Integrable
        (fun p => (deriv g (φ p)) ^ 2 / g (φ p)) (γ.prod γ) := by
      refine Integrable.mono' (integrable_const (M ^ 2 / ε)) ?_ ?_
      · exact ((h_qsq_over_r_meas.comp hφ_meas)).aestronglyMeasurable
      · filter_upwards with p
        rw [Real.norm_eq_abs, abs_of_nonneg (h_qsq_over_r_nn _)]
        exact h_qsq_over_r_bd _
    have h_fubini :
        ∫ x, (∫ y, (deriv g (a*x + b*y)) ^ 2 / g (a*x + b*y) ∂γ) ∂γ =
          ∫ p, (deriv g (φ p)) ^ 2 / g (φ p) ∂(γ.prod γ) :=
      (integral_prod _ hg'_over_g_φ_int).symm
    have h_law : HasLaw φ γ (γ.prod γ) := ⟨hφ_meas.aemeasurable, hmap⟩
    have h_push : ∫ p, (deriv g (φ p)) ^ 2 / g (φ p) ∂(γ.prod γ) =
        ∫ z, (deriv g z) ^ 2 / g z ∂γ :=
      h_law.integral_comp h_qsq_over_r_meas.aestronglyMeasurable
    show ∫ x, (∫ y, (deriv g (a*x + b*y)) ^ 2 / g (a*x + b*y) ∂γ) ∂γ
        = ∫ y, (deriv g y) ^ 2 / g y ∂γ
    rw [h_fubini, h_push]
  -- Integrability of the LHS integrand: ((P_t g)')² / P_t g.
  -- Bounds: |(P_t g)'(x)| ≤ M (since |a · P_t(g') x| ≤ 1 · M ≤ M, and
  -- in any case ((P_t g)')² / P_t g ≤ M² / ε.)
  have h_Ptg_meas : Measurable (ouSemigroup t g) := by
    -- (x ↦ ∫ y, g(a*x + b*y) dγ y) is measurable as integral_prod_right'.
    show Measurable fun x => ∫ y, g (a * x + b * y) ∂γ
    have h_sm : StronglyMeasurable
        (fun p : ℝ × ℝ => g (a * p.1 + b * p.2)) :=
      (hg_meas.comp ((measurable_const.mul measurable_fst).add
        (measurable_const.mul measurable_snd))).stronglyMeasurable
    exact (h_sm.integral_prod_right' (ν := γ)).measurable
  have h_Ptdg_meas : Measurable (ouSemigroup t (deriv g)) := by
    show Measurable fun x => ∫ y, deriv g (a * x + b * y) ∂γ
    have h_sm : StronglyMeasurable
        (fun p : ℝ × ℝ => deriv g (a * p.1 + b * p.2)) :=
      (hg'_meas.comp ((measurable_const.mul measurable_fst).add
        (measurable_const.mul measurable_snd))).stronglyMeasurable
    exact (h_sm.integral_prod_right' (ν := γ)).measurable
  -- Pointwise: (deriv (P_t g) x)² / (P_t g) x ≤ a² · M² / ε.
  have h_lhs_bd : ∀ x,
      (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x ≤ a ^ 2 * (M ^ 2 / ε) := by
    intro x
    have hPtg_pos := h_Ptg_pos x
    have h1 : (deriv (ouSemigroup t g) x) ^ 2 = a ^ 2 * (ouSemigroup t (deriv g) x) ^ 2 := by
      rw [h_deriv_eq x]; ring
    have h_Ptdg_bd : |ouSemigroup t (deriv g) x| ≤ M := by
      show |∫ y, deriv g (a * x + b * y) ∂γ| ≤ M
      have h_int : Integrable (fun y => deriv g (a * x + b * y)) γ := by
        refine Integrable.mono' (integrable_const M) ?_ ?_
        · exact (hg'_meas.comp
            (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
        · filter_upwards with y; exact hg'_norm _
      calc |∫ y, deriv g (a * x + b * y) ∂γ|
          ≤ ∫ y, |deriv g (a * x + b * y)| ∂γ := abs_integral_le_integral_abs
        _ ≤ ∫ _, M ∂γ :=
              integral_mono h_int.abs (integrable_const _) (fun y => hg'_bd _)
        _ = M := by simp
    have h_Ptdg_sq_bd : (ouSemigroup t (deriv g) x) ^ 2 ≤ M ^ 2 := by
      have : (ouSemigroup t (deriv g) x) ^ 2 = |ouSemigroup t (deriv g) x| ^ 2 := by rw [sq_abs]
      rw [this]
      exact pow_le_pow_left₀ (abs_nonneg _) h_Ptdg_bd 2
    have h2 : a ^ 2 * (ouSemigroup t (deriv g) x) ^ 2 ≤ a ^ 2 * M ^ 2 :=
      mul_le_mul_of_nonneg_left h_Ptdg_sq_bd (sq_nonneg _)
    have h3 : a ^ 2 * M ^ 2 / ouSemigroup t g x ≤ a ^ 2 * M ^ 2 / ε := by
      apply div_le_div_of_nonneg_left _ hε (h_Ptg_lo x)
      positivity
    have h4 : (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x ≤ a ^ 2 * M ^ 2 / ε := by
      rw [h1]
      calc a ^ 2 * (ouSemigroup t (deriv g) x) ^ 2 / ouSemigroup t g x
          ≤ a ^ 2 * M ^ 2 / ouSemigroup t g x :=
            div_le_div_of_nonneg_right h2 (h_Ptg_pos x).le
        _ ≤ a ^ 2 * M ^ 2 / ε := h3
    calc (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x
        ≤ a ^ 2 * M ^ 2 / ε := h4
      _ = a ^ 2 * (M ^ 2 / ε) := by ring
  have h_lhs_nn : ∀ x, 0 ≤ (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x := fun x =>
    div_nonneg (sq_nonneg _) (h_Ptg_pos x).le
  have h_lhs_int : Integrable (fun x => (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x) γ := by
    refine Integrable.mono' (integrable_const (a ^ 2 * (M ^ 2 / ε))) ?_ ?_
    · -- Measurability: deriv (ouSemigroup t g) x = a · ouSemigroup t (deriv g) x.
      have h_eq : (fun x => (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x) =
          (fun x => (a * ouSemigroup t (deriv g) x) ^ 2 / ouSemigroup t g x) := by
        funext x; rw [h_deriv_eq x]
      rw [h_eq]
      refine Measurable.aestronglyMeasurable ?_
      exact ((measurable_const.mul h_Ptdg_meas).pow_const 2).div h_Ptg_meas
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (h_lhs_nn _)]
      exact h_lhs_bd _
  -- Integrability of RHS integrand: a² · P_t((g')²/g) x.
  have h_Pt_qsq_over_r_meas : Measurable
      (fun x => ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x) := by
    show Measurable fun x => ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ
    have h_sm : StronglyMeasurable
        (fun p : ℝ × ℝ => (deriv g (a * p.1 + b * p.2)) ^ 2 / g (a * p.1 + b * p.2)) :=
      (h_qsq_over_r_meas.comp ((measurable_const.mul measurable_fst).add
        (measurable_const.mul measurable_snd))).stronglyMeasurable
    exact (h_sm.integral_prod_right' (ν := γ)).measurable
  have h_rhs_int : Integrable (fun x => a ^ 2 *
      ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x) γ := by
    refine Integrable.mono' (integrable_const (a ^ 2 * (M ^ 2 / ε))) ?_ ?_
    · exact (measurable_const.mul h_Pt_qsq_over_r_meas).aestronglyMeasurable
    · filter_upwards with x
      have h_inner_bd : ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x ≤ M ^ 2 / ε := by
        show ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ ≤ M ^ 2 / ε
        have h_int : Integrable
            (fun y => (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y)) γ := by
          refine Integrable.mono' (integrable_const (M ^ 2 / ε)) ?_ ?_
          · exact (h_qsq_over_r_meas.comp
              (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
          · filter_upwards with y
            rw [Real.norm_eq_abs, abs_of_nonneg (h_qsq_over_r_nn _)]
            exact h_qsq_over_r_bd _
        calc ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ
            ≤ ∫ _, (M ^ 2 / ε) ∂γ :=
                integral_mono h_int (integrable_const _) (fun y => h_qsq_over_r_bd _)
          _ = M ^ 2 / ε := by simp
      have h_inner_nn : 0 ≤ ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x := by
        show 0 ≤ ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ
        exact integral_nonneg (fun y => h_qsq_over_r_nn _)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h_inner_nn)]
      exact mul_le_mul_of_nonneg_left h_inner_bd (sq_nonneg _)
  -- Assemble: integrate the pointwise bound.
  show fisherInfo (ouSemigroup t g) ≤ Real.exp (-2 * t) * fisherInfo g
  unfold fisherInfo
  calc ∫ y, (deriv (ouSemigroup t g) y) ^ 2 / ouSemigroup t g y ∂γ
      ≤ ∫ x, a ^ 2 * ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x ∂γ := by
        exact integral_mono h_lhs_int h_rhs_int h_ptwise
    _ = a ^ 2 * ∫ x, ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x ∂γ := by
        rw [integral_const_mul]
    _ = a ^ 2 * ∫ y, (deriv g y) ^ 2 / g y ∂γ := by rw [h_inv]
    _ = Real.exp (-2 * t) * ∫ y, (deriv g y) ^ 2 / g y ∂γ := by rw [ha_sq]

/-! ## A2: De Bruijn identity (entropy derivative = -Fisher info) -/

/-- **De Bruijn identity for the OU semigroup.** AXIOM
(vetting-required textbook bridge).

For any `C¹` `g : ℝ → ℝ` with `g, g'` bounded and `g ≥ ε > 0` pointwise,
the Boltzmann entropy `H(P_s g) = ∫ P_s g · log(P_s g) dγ` is
differentiable in `s` at any `t > 0` with derivative

  `(d/dt) H(P_t g) = -I(P_t g)`.

## Proof in textbooks

Differentiate under the integral sign:
  `(d/dt) ∫ P_t g · log(P_t g) dγ
     = ∫ ((d/dt) P_t g) · (1 + log P_t g) dγ`
     `= ∫ L(P_t g) · (1 + log P_t g) dγ`  (heat equation
                                            `hasDerivAt_t_ouSemigroup`)
     `= ∫ L(P_t g) · log(P_t g) dγ`  (since `∫ L(h) dγ = 0` for any
                                       `h` integrable, by γ-invariance)
     `= -∫ Γ(P_t g, log(P_t g)) dγ`  (integration by parts,
                                       `gaussian_dirichlet_form_identity`-style)
     `= -∫ ((P_t g)')² / P_t g dγ`  (since `Γ(f, log g) = f' · g'/g` and
                                       here `f = g = P_t g`).

The parametric differentiation requires the integrand
`(s, y) ↦ P_s g(y) · log(P_s g(y))` to satisfy a uniform dominator —
since `g ≥ ε > 0` and `|g| ≤ M`, `P_s g` also stays in `[ε, M]`, and
`s · log s` is continuous and bounded on `[ε, M]`.

## Discharge plan

Per Gemini 3.1-pro vetting (verdict: **Standard**, 2026-05-12). Two
sub-steps:

1. **Bilinear Dirichlet form identity** (auxiliary, ~50-100 lines):
   `∫ f · L h dγ = -∫ f' · h' dγ` for suitable test functions. Provable
   via 1D IBP using the identity `(h'(y) · e^{-y²/2})' = (Lh)(y) ·
   e^{-y²/2}`. This generalizes our existing
   `gaussian_dirichlet_form_identity` (which is the diagonal case
   `f = h = g`).
2. **Parametric differentiation** (~150-250 lines): differentiate
   `s ↦ ∫ P_s g · log(P_s g) dγ` under the integral via the heat
   equation `(d/ds) P_s g = L(P_s g)` and the chain rule. Use the
   bilinear Dirichlet form identity to get
   `∫ L(P_t g) · (1 + log P_t g) dγ = -∫ ((P_t g)')² / P_t g dγ`
   (taking `f := P_t g`, `h := 1 + log P_t g`, so `h' = (P_t g)'/P_t g`).
   The `(d/ds) = (d/dt)`-style step uses Mathlib's
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; dominator is
   `|L(P_t g)|·(M·log M + 1)` which is γ-integrable (linear growth
   times Gaussian).

The C¹ restriction on `g` (not `C^∞`) is intentional: for `t > 0`,
`P_t g` is automatically `C^∞` (by `ouSemigroup_contDiff_bounded`,
discharged in `EuclideanHermite.lean`), so the differentiation works
cleanly. At `t = 0` the right-derivative is established by FTC + DCT
limit (the auxiliary `hasDerivWithinAt_entropy_ouSemigroup_zero`).

## References

* Bakry-Gentil-Ledoux, §5.5 (de Bruijn identity).
* Stam (1959), "Some inequalities satisfied by the quantities of
  information of Fisher and Shannon."

## Vetting

**Standard** (gemini-3.1-pro-preview, 2026-05-12). For `t > 0`, the
parametric differentiation goes through cleanly because `P_t g` is
`C^∞` and the integrand `(LP_tg)(1 + log P_tg)` has at-most-linear
growth × Gaussian decay → γ-integrable. The boundary version at
`t = 0` (which has only `C¹` regularity) is correct via the FTC+DCT
route: `lim_{t↘0} I(P_t g) = I(g)` by DCT, so the right-derivative
matches. Hypotheses tight; both `g ≤ M` and `|g'| ≤ M` are needed
for clean dominator bounds. -/
theorem hasDerivAt_entropy_ouSemigroup
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => boltzmannEntropy (ouSemigroup s g))
      (-fisherInfo (ouSemigroup t g)) t := by
  -- ===========================================================================
  -- UPSTREAM HISTORICAL PARTIAL-PROOF NOTE (2026-05-12)
  -- Superseded by the completed proof below and the local compiled axiom audit.
  --
  -- This proof builds the proof infrastructure (Phase 1, ~250 lines below)
  -- but the final assembly via the parametric-DCT + bilinear Dirichlet form
  -- requires four substantial sub-lemmas marked with `sorry` (see the
  -- comprehensive comment below). The mathematical strategy is fully laid
  -- out in the docstring above and in inline comments. Math vetting:
  -- **Standard** (Gemini 3.1-pro, 2026-05-12).
  -- ===========================================================================
  -- Notation.
  set a : ℝ → ℝ := fun s => Real.exp (-s) with ha_def
  set b : ℝ → ℝ := fun s => Real.sqrt (1 - Real.exp (-2 * s)) with hb_def
  -- Basic bounds on ε, M.
  have hε_nn : 0 ≤ ε := hε.le
  have hε_le_M : ε ≤ M := (hg_lo 0).trans (hg_hi 0)
  have hM_nn : 0 ≤ M := hε_nn.trans hε_le_M
  -- Basic properties of g.
  have h_gpos : ∀ x, 0 < g x := fun x => lt_of_lt_of_le hε (hg_lo x)
  have h_gabs : ∀ x, |g x| ≤ M := fun x => by
    rw [abs_of_pos (h_gpos x)]; exact hg_hi x
  have hg_norm : ∀ x, ‖g x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs]; exact h_gabs x
  have hg'_norm : ∀ x, ‖deriv g x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs]; exact hg'_bd x
  have hg_cont : Continuous g := hg.continuous
  have hg_meas : Measurable g := hg_cont.measurable
  have hg'_cont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hg'_meas : Measurable (deriv g) := hg'_cont.measurable
  -- Neighborhood of t in (0, ∞): Ioo (t/2) (3t/2).
  set tlo : ℝ := t / 2 with htlo_def
  set thi : ℝ := 3 * t / 2 with hthi_def
  have htlo_pos : 0 < tlo := half_pos ht
  have htlo_lt_t : tlo < t := half_lt_self ht
  have ht_lt_thi : t < thi := by show t < 3 * t / 2; linarith
  have h_nbhd : Set.Ioo tlo thi ∈ nhds t := Ioo_mem_nhds htlo_lt_t ht_lt_thi
  -- Lower bound on b(s) for s ∈ Ioo tlo thi.
  have h_atlo_lt_one : Real.exp (-2 * tlo) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hb_lo_pos : 0 < b tlo := by apply Real.sqrt_pos.mpr; linarith
  have hb_pos_on_nbhd : ∀ s ∈ Set.Ioo tlo thi, 0 < b s := by
    intro s hs
    apply Real.sqrt_pos.mpr
    have : Real.exp (-2 * s) < 1 := Real.exp_lt_one_iff.mpr (by linarith [hs.1])
    linarith
  have hb_t_pos : 0 < b t := hb_pos_on_nbhd t ⟨htlo_lt_t, ht_lt_thi⟩
  -- a(s) properties.
  have h_a_pos : ∀ s, 0 < a s := fun s => Real.exp_pos _
  have h_a_nn : ∀ s, 0 ≤ a s := fun s => (h_a_pos s).le
  have h_a_le_one : ∀ s, 0 ≤ s → a s ≤ 1 := fun s hs =>
    Real.exp_le_one_iff.mpr (by linarith)
  -- P_s g bounds (averaging against probability measure preserves [ε, M]).
  have h_Ptg_lo : ∀ s, 0 ≤ s → ∀ x, ε ≤ ouSemigroup s g x := by
    intro s hs x
    show ε ≤ ∫ y, g (a s * x + b s * y) ∂γ
    have h_int : Integrable (fun y => g (a s * x + b s * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg_norm _
    calc (ε : ℝ) = ∫ _, ε ∂γ := by simp
      _ ≤ ∫ y, g (a s * x + b s * y) ∂γ :=
            integral_mono (integrable_const _) h_int (fun _ => hg_lo _)
  have h_Ptg_hi : ∀ s, 0 ≤ s → ∀ x, ouSemigroup s g x ≤ M := by
    intro s hs x
    show ∫ y, g (a s * x + b s * y) ∂γ ≤ M
    have h_int : Integrable (fun y => g (a s * x + b s * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg_norm _
    calc ∫ y, g (a s * x + b s * y) ∂γ
        ≤ ∫ _, M ∂γ :=
            integral_mono h_int (integrable_const _) (fun _ => hg_hi _)
      _ = M := by simp
  have h_Ptg_pos : ∀ s, 0 ≤ s → ∀ x, 0 < ouSemigroup s g x := fun s hs x =>
    lt_of_lt_of_le hε (h_Ptg_lo s hs x)
  have h_Ptg_abs : ∀ s, 0 ≤ s → ∀ x, |ouSemigroup s g x| ≤ M := fun s hs x => by
    rw [abs_of_pos (h_Ptg_pos s hs x)]; exact h_Ptg_hi s hs x
  -- Mehler derivative: (P_s g)'(x) = a(s) · P_s(g')(x).
  have h_deriv_Ptg : ∀ s, ∀ x,
      HasDerivAt (ouSemigroup s g)
        (a s * ouSemigroup s (deriv g) x) x := fun s x =>
    hasDerivAt_ouSemigroup_C1 s hg hg_norm hg'_norm x
  have h_deriv_Ptg_eq : ∀ s, ∀ x,
      deriv (ouSemigroup s g) x = a s * ouSemigroup s (deriv g) x :=
    fun s x => (h_deriv_Ptg s x).deriv
  -- |P_s(g')(x)| ≤ M.
  have h_Ptdg_abs : ∀ s, 0 ≤ s → ∀ x, |ouSemigroup s (deriv g) x| ≤ M := by
    intro s hs x
    show |∫ y, deriv g (a s * x + b s * y) ∂γ| ≤ M
    have h_int : Integrable (fun y => deriv g (a s * x + b s * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg'_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg'_norm _
    calc |∫ y, deriv g (a s * x + b s * y) ∂γ|
        ≤ ∫ y, |deriv g (a s * x + b s * y)| ∂γ := abs_integral_le_integral_abs
      _ ≤ ∫ _, M ∂γ :=
            integral_mono h_int.abs (integrable_const _) (fun _ => hg'_bd _)
      _ = M := by simp
  -- |(P_s g)'(x)| ≤ M.
  have h_dPtg_abs : ∀ s, 0 ≤ s → ∀ x, |deriv (ouSemigroup s g) x| ≤ M := by
    intro s hs x
    rw [h_deriv_Ptg_eq s x, abs_mul, abs_of_nonneg (h_a_nn s)]
    calc a s * |ouSemigroup s (deriv g) x|
        ≤ 1 * M := mul_le_mul (h_a_le_one s hs) (h_Ptdg_abs s hs x) (abs_nonneg _) (by norm_num)
      _ = M := one_mul _
  -- Measurability of P_s g.
  have h_Ptg_meas : ∀ s, Measurable (ouSemigroup s g) := fun s => by
    show Measurable fun x => ∫ y, g (a s * x + b s * y) ∂γ
    have h_sm : StronglyMeasurable
        (fun p : ℝ × ℝ => g (a s * p.1 + b s * p.2)) :=
      (hg_cont.comp ((continuous_const.mul continuous_fst).add
        (continuous_const.mul continuous_snd))).stronglyMeasurable
    exact (h_sm.integral_prod_right' (ν := γ)).measurable
  -- Bound on |log(P_t g x) + 1|.
  set Mlog : ℝ := |Real.log ε| + |Real.log M| + 1 with hMlog_def
  have hMlog_nn : 0 ≤ Mlog := by positivity
  have h_log_bd : ∀ x, |Real.log (ouSemigroup t g x) + 1| ≤ Mlog := by
    intro x
    have h1 : ε ≤ ouSemigroup t g x := h_Ptg_lo t ht.le x
    have h2 : ouSemigroup t g x ≤ M := h_Ptg_hi t ht.le x
    have hPtg_pos := h_Ptg_pos t ht.le x
    have hlog_bd : |Real.log (ouSemigroup t g x)| ≤ |Real.log ε| + |Real.log M| := by
      by_cases hcase : ouSemigroup t g x ≤ 1
      · have h_log_le_0 : Real.log (ouSemigroup t g x) ≤ 0 :=
          Real.log_nonpos hPtg_pos.le hcase
        have h_log_eps_le : Real.log ε ≤ Real.log (ouSemigroup t g x) :=
          Real.log_le_log hε h1
        rw [abs_of_nonpos h_log_le_0]
        have h_eps_log_nonpos : Real.log ε ≤ 0 :=
          Real.log_nonpos hε.le (le_trans h1 hcase)
        rw [abs_of_nonpos h_eps_log_nonpos]
        linarith [abs_nonneg (Real.log M)]
      · have h1' : (1 : ℝ) < ouSemigroup t g x := not_le.mp hcase
        have h_log_nn : 0 ≤ Real.log (ouSemigroup t g x) := Real.log_nonneg h1'.le
        have h_log_le_M : Real.log (ouSemigroup t g x) ≤ Real.log M :=
          Real.log_le_log hPtg_pos h2
        have h_log_M_nn : 0 ≤ Real.log M := h_log_nn.trans h_log_le_M
        rw [abs_of_nonneg h_log_nn, abs_of_nonneg h_log_M_nn]
        linarith [abs_nonneg (Real.log ε)]
    calc |Real.log (ouSemigroup t g x) + 1|
        ≤ |Real.log (ouSemigroup t g x)| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ (|Real.log ε| + |Real.log M|) + 1 := by
          gcongr; rw [abs_one]
      _ = Mlog := by simp [Mlog]
  -- log(P_t g) + 1 has derivative (P_t g)'/(P_t g).
  have h_logPtg_deriv : ∀ x,
      HasDerivAt (fun y => Real.log (ouSemigroup t g y) + 1)
        (deriv (ouSemigroup t g) x / ouSemigroup t g x) x := by
    intro x
    have hPtg_pos := h_Ptg_pos t ht.le x
    have h_log_deriv : HasDerivAt Real.log (ouSemigroup t g x)⁻¹ (ouSemigroup t g x) :=
      Real.hasDerivAt_log hPtg_pos.ne'
    have h_Ptg_deriv : HasDerivAt (ouSemigroup t g) (deriv (ouSemigroup t g) x) x :=
      (h_deriv_Ptg t x).congr_deriv (h_deriv_Ptg_eq t x).symm
    have h_comp := h_log_deriv.comp x h_Ptg_deriv
    have h_comp' : HasDerivAt (fun y => Real.log (ouSemigroup t g y))
        (deriv (ouSemigroup t g) x / ouSemigroup t g x) x := by
      simpa only [Function.comp_def, div_eq_mul_inv, mul_comm] using h_comp
    exact h_comp'.add_const 1
  -- Bound on |(log P_t g + 1)'| ≤ M/ε.
  have h_logPtg'_bd : ∀ x,
      |deriv (fun y => Real.log (ouSemigroup t g y) + 1) x| ≤ M / ε := by
    intro x
    rw [(h_logPtg_deriv x).deriv]
    have hPtg_pos := h_Ptg_pos t ht.le x
    have hPtg_lo := h_Ptg_lo t ht.le x
    rw [abs_div, abs_of_pos hPtg_pos]
    have h_num_bd : |deriv (ouSemigroup t g) x| ≤ M := h_dPtg_abs t ht.le x
    calc |deriv (ouSemigroup t g) x| / ouSemigroup t g x
        ≤ M / ouSemigroup t g x :=
          div_le_div_of_nonneg_right h_num_bd hPtg_pos.le
      _ ≤ M / ε := div_le_div_of_nonneg_left hM_nn hε hPtg_lo
  -- ===========================================================================
  -- (A) + (B): Stein-based smoothing.  We build:
  --   h_aux x := ∫ y, y * g (a t * x + b t * y) ∂γ
  -- and show, using Stein at fixed x:
  --   deriv (ouSemigroup t g) x = (a t / b t) * h_aux x
  -- Differentiating h_aux via parametric DCT (the integrand y * g(...) is C¹
  -- in x with derivative y * a t * deriv g(...), dominated by |y| * a t * M)
  -- gives both `(P_t g)''` as a continuous function with explicit bound.
  -- ===========================================================================
  -- Abbreviations for the values at the fixed point `t`.
  set at_ : ℝ := a t with hat_def
  set bt_ : ℝ := b t with hbt_def
  have hat_pos : 0 < at_ := h_a_pos t
  have hat_nn : 0 ≤ at_ := hat_pos.le
  have hat_le_one : at_ ≤ 1 := h_a_le_one t ht.le
  have hbt_pos : 0 < bt_ := hb_t_pos
  have hbt_nn : 0 ≤ bt_ := hbt_pos.le
  have hbt_ne : bt_ ≠ 0 := hbt_pos.ne'
  have hbt_le_one : bt_ ≤ 1 := by
    show Real.sqrt (1 - Real.exp (-2 * t)) ≤ 1
    have h_exp_pos : 0 < Real.exp (-2 * t) := Real.exp_pos _
    have h_one_sub_le : 1 - Real.exp (-2 * t) ≤ 1 := by linarith
    calc Real.sqrt (1 - Real.exp (-2 * t)) ≤ Real.sqrt 1 :=
            Real.sqrt_le_sqrt h_one_sub_le
      _ = 1 := Real.sqrt_one
  -- Absolute first moment of γ.
  set C_abs_y : ℝ := ∫ y, |y| ∂γ with hCabs_def
  have h_id_int : Integrable (fun y : ℝ => y) γ :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have h_abs_id_int : Integrable (fun y : ℝ => |y|) γ := h_id_int.abs
  have hCabs_nn : 0 ≤ C_abs_y := integral_nonneg (fun y => abs_nonneg _)
  -- Define h_aux x := ∫ y, y * g (at_*x + bt_*y) ∂γ.
  set h_aux : ℝ → ℝ := fun x => ∫ y, y * g (at_ * x + bt_ * y) ∂γ
    with h_aux_def
  -- Integrability of y ↦ y * g (at_*x + bt_*y) for any x.
  have h_aux_int : ∀ x, Integrable (fun y => y * g (at_ * x + bt_ * y)) γ := by
    intro x
    refine Integrable.mono' (h_abs_id_int.const_mul M) ?_ ?_
    · exact (measurable_id.mul (hg_meas.comp
        (measurable_const.add (measurable_const.mul measurable_id)))).aestronglyMeasurable
    · filter_upwards with y
      show ‖y * g (at_ * x + bt_ * y)‖ ≤ M * |y|
      rw [Real.norm_eq_abs, abs_mul]
      calc |y| * |g (at_ * x + bt_ * y)|
          ≤ |y| * M :=
            mul_le_mul_of_nonneg_left (h_gabs _) (abs_nonneg _)
        _ = M * |y| := mul_comm _ _
  -- Stein at fixed x: ∫ y * g(at_*x + bt_*y) dγ = bt_ * P_t (deriv g) x.
  have h_stein_x : ∀ x, h_aux x = bt_ * ouSemigroup t (deriv g) x := by
    intro x
    -- F(y) := g(at_*x + bt_*y). F is C¹ in y, with deriv = bt_ * (deriv g)(...).
    set F : ℝ → ℝ := fun y => g (at_ * x + bt_ * y) with hF_def
    have hF_C1 : ContDiff ℝ 1 F := by
      have h_inner : ContDiff ℝ 1 (fun y : ℝ => at_ * x + bt_ * y) :=
        contDiff_const.add (contDiff_const.mul contDiff_id)
      exact hg.comp h_inner
    have hF_bd : ∀ y, |F y| ≤ M := fun y => h_gabs _
    have hF'_eq : ∀ y, deriv F y = bt_ * deriv g (at_ * x + bt_ * y) := by
      intro y
      have h_inner : HasDerivAt (fun z : ℝ => at_ * x + bt_ * z) bt_ y := by
        simpa using ((hasDerivAt_id y).const_mul bt_).const_add (at_ * x)
      have h_g : HasDerivAt g (deriv g (at_ * x + bt_ * y)) (at_ * x + bt_ * y) :=
        (hg.differentiable (by simp)).differentiableAt.hasDerivAt
      have h_comp : HasDerivAt F (deriv g (at_ * x + bt_ * y) * bt_) y :=
        h_g.comp y h_inner
      simpa [mul_comm bt_ _] using h_comp.deriv
    have hF'_bd : ∀ y, |deriv F y| ≤ M := by
      intro y
      rw [hF'_eq y, abs_mul, abs_of_nonneg hbt_nn]
      have h_dg : |deriv g (at_ * x + bt_ * y)| ≤ M := hg'_bd _
      calc bt_ * |deriv g (at_ * x + bt_ * y)|
          ≤ 1 * M := mul_le_mul hbt_le_one h_dg (abs_nonneg _) (by norm_num)
        _ = M := one_mul _
    have h_stein := stein_identity_standard hF_C1 hF_bd hF'_bd
    -- ∫ y * F y dγ = ∫ deriv F y dγ.
    -- LHS = h_aux x. RHS = bt_ * P_t (deriv g) x.
    have h_lhs : ∫ y, y * F y ∂γ = h_aux x := rfl
    have h_rhs : ∫ y, deriv F y ∂γ = bt_ * ouSemigroup t (deriv g) x := by
      have h_rw : (fun y => deriv F y) =
          (fun y => bt_ * deriv g (at_ * x + bt_ * y)) := by
        funext y; exact hF'_eq y
      rw [h_rw, integral_const_mul]
      rfl
    rw [← h_lhs, h_stein, h_rhs]
  -- Pointwise formula: (P_t g)' x = (at_/bt_) * h_aux x.
  have h_dPtg_haux : ∀ x, deriv (ouSemigroup t g) x = (at_ / bt_) * h_aux x := by
    intro x
    have h1 : deriv (ouSemigroup t g) x = at_ * ouSemigroup t (deriv g) x :=
      h_deriv_Ptg_eq t x
    rw [h1, h_stein_x x]
    field_simp
  -- h_aux is differentiable, with deriv given by parametric DCT.
  -- deriv h_aux x = ∫ y, y * at_ * (deriv g)(at_*x + bt_*y) ∂γ
  --              = at_ * ∫ y, y * (deriv g)(at_*x + bt_*y) ∂γ.
  set h_aux' : ℝ → ℝ := fun x => at_ * ∫ y, y * deriv g (at_ * x + bt_ * y) ∂γ
    with h_aux'_def
  -- Integrability of y * (deriv g)(at_*x + bt_*y).
  have h_aux'_int : ∀ x, Integrable
      (fun y => y * deriv g (at_ * x + bt_ * y)) γ := by
    intro x
    refine Integrable.mono' (h_abs_id_int.const_mul M) ?_ ?_
    · exact (measurable_id.mul (hg'_meas.comp
        (measurable_const.add (measurable_const.mul measurable_id)))).aestronglyMeasurable
    · filter_upwards with y
      show ‖y * deriv g (at_ * x + bt_ * y)‖ ≤ M * |y|
      rw [Real.norm_eq_abs, abs_mul]
      calc |y| * |deriv g (at_ * x + bt_ * y)|
          ≤ |y| * M :=
            mul_le_mul_of_nonneg_left (hg'_bd _) (abs_nonneg _)
        _ = M * |y| := mul_comm _ _
  have h_haux_deriv : ∀ x₀, HasDerivAt h_aux (h_aux' x₀) x₀ := by
    intro x₀
    -- Parametric integral derivative.
    set F : ℝ → ℝ → ℝ := fun x y => y * g (at_ * x + bt_ * y) with hF_def
    set F' : ℝ → ℝ → ℝ := fun x y => y * (at_ * deriv g (at_ * x + bt_ * y))
      with hF'_def
    set bound : ℝ → ℝ := fun y => |y| * (at_ * M) with hbound_def
    have hs : Set.Ioo (x₀ - 1) (x₀ + 1) ∈ nhds x₀ :=
      Ioo_mem_nhds (by linarith) (by linarith)
    have hF_meas_local : ∀ x, AEStronglyMeasurable (F x) γ := by
      intro x
      exact (measurable_id.mul (hg_meas.comp
        (measurable_const.add (measurable_const.mul measurable_id)))).aestronglyMeasurable
    have hF_int_local : Integrable (F x₀) γ := h_aux_int x₀
    have hF'_meas_local : AEStronglyMeasurable (F' x₀) γ := by
      refine (measurable_id.mul (measurable_const.mul ?_)).aestronglyMeasurable
      exact hg'_meas.comp (measurable_const.add (measurable_const.mul measurable_id))
    have h_bound_loc : ∀ᵐ y ∂γ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
        ‖F' x y‖ ≤ bound y := by
      filter_upwards with y x _
      show ‖y * (at_ * deriv g (at_ * x + bt_ * y))‖ ≤ |y| * (at_ * M)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hat_nn]
      have h_dg : |deriv g (at_ * x + bt_ * y)| ≤ M := hg'_bd _
      have h1 : at_ * |deriv g (at_ * x + bt_ * y)| ≤ at_ * M :=
        mul_le_mul_of_nonneg_left h_dg hat_nn
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h_bound_int_local : Integrable bound γ := by
      show Integrable (fun y => |y| * (at_ * M)) γ
      exact h_abs_id_int.mul_const _
    have h_diff_loc : ∀ᵐ y ∂γ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
        HasDerivAt (F · y) (F' x y) x := by
      filter_upwards with y x _
      show HasDerivAt (fun x => y * g (at_ * x + bt_ * y))
        (y * (at_ * deriv g (at_ * x + bt_ * y))) x
      have h_inner : HasDerivAt (fun x : ℝ => at_ * x + bt_ * y) at_ x := by
        simpa using ((hasDerivAt_id x).const_mul at_).add_const (bt_ * y)
      have h_g : HasDerivAt g (deriv g (at_ * x + bt_ * y)) (at_ * x + bt_ * y) :=
        (hg.differentiable (by simp)).differentiableAt.hasDerivAt
      have h_comp : HasDerivAt (fun x => g (at_ * x + bt_ * y))
          (deriv g (at_ * x + bt_ * y) * at_) x := h_g.comp x h_inner
      have h_mul := h_comp.const_mul y
      simpa [mul_comm at_ _, mul_assoc] using h_mul
    obtain ⟨_, h_deriv⟩ :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
        (Filter.Eventually.of_forall hF_meas_local) hF_int_local
        hF'_meas_local h_bound_loc h_bound_int_local h_diff_loc
    -- h_deriv : HasDerivAt (fun x => ∫ y, F x y ∂γ) (∫ y, F' x₀ y ∂γ) x₀.
    -- LHS = h_aux. RHS = h_aux' x₀.
    have h_lhs_eq : (fun x => ∫ y, F x y ∂γ) = h_aux := rfl
    have h_rhs_eq : ∫ y, F' x₀ y ∂γ = h_aux' x₀ := by
      show ∫ y, y * (at_ * deriv g (at_ * x₀ + bt_ * y)) ∂γ =
        at_ * ∫ y, y * deriv g (at_ * x₀ + bt_ * y) ∂γ
      have h_rw : (fun y => y * (at_ * deriv g (at_ * x₀ + bt_ * y))) =
          (fun y => at_ * (y * deriv g (at_ * x₀ + bt_ * y))) := by
        funext y; ring
      rw [h_rw, integral_const_mul]
    rw [← h_lhs_eq, ← h_rhs_eq]; exact h_deriv
  -- Continuity of h_aux'.
  have h_haux'_cont : Continuous h_aux' := by
    show Continuous (fun x => at_ * ∫ y, y * deriv g (at_ * x + bt_ * y) ∂γ)
    refine continuous_const.mul ?_
    refine continuous_of_dominated (bound := fun y => M * |y|) ?_ ?_ ?_ ?_
    · intro x
      exact (measurable_id.mul (hg'_meas.comp
        (measurable_const.add (measurable_const.mul measurable_id)))).aestronglyMeasurable
    · intro x
      filter_upwards with y
      show ‖y * deriv g (at_ * x + bt_ * y)‖ ≤ M * |y|
      rw [Real.norm_eq_abs, abs_mul]
      calc |y| * |deriv g (at_ * x + bt_ * y)|
          ≤ |y| * M :=
            mul_le_mul_of_nonneg_left (hg'_bd _) (abs_nonneg _)
        _ = M * |y| := mul_comm _ _
    · exact h_abs_id_int.const_mul M
    · filter_upwards with y
      refine Continuous.mul continuous_const ?_
      exact hg'_cont.comp ((continuous_const.mul continuous_id).add_const _)
  -- Now: deriv (ouSemigroup t g) = (at_/bt_) * h_aux pointwise.
  have h_dPtg_eq_fun :
      deriv (ouSemigroup t g) = fun x => (at_ / bt_) * h_aux x := by
    funext x; exact h_dPtg_haux x
  -- (P_t g)''(x) = (at_/bt_) * h_aux' x.
  have h_dd_Ptg : ∀ x, HasDerivAt (deriv (ouSemigroup t g))
      ((at_ / bt_) * h_aux' x) x := by
    intro x
    have h := (h_haux_deriv x).const_mul (at_ / bt_)
    -- h : HasDerivAt (fun y => (at_/bt_) * h_aux y) ((at_/bt_) * h_aux' x) x.
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with y
    exact h_dPtg_haux y
  -- (A) ContDiff ℝ 2 (ouSemigroup t g): differentiable + C¹ of deriv.
  have h_Ptg_C2 : ContDiff ℝ 2 (ouSemigroup t g) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun x => (h_deriv_Ptg t x).differentiableAt, ?_, ?_⟩
    · intro h_eq; exact absurd h_eq (by decide)
    · rw [contDiff_one_iff_deriv]
      refine ⟨fun x => (h_dd_Ptg x).differentiableAt, ?_⟩
      -- deriv (deriv (ouSemigroup t g)) x = (at_/bt_) * h_aux' x by h_dd_Ptg.
      have h_dd_eq : deriv (deriv (ouSemigroup t g)) =
          fun x => (at_ / bt_) * h_aux' x := by
        funext x; exact (h_dd_Ptg x).deriv
      rw [h_dd_eq]; exact continuous_const.mul h_haux'_cont
  -- (B) Bound on |(P_t g)''|: M_dd := (at_/bt_) * at_ * M * C_abs_y.
  -- |(at_/bt_) * h_aux' x| = (at_/bt_) * at_ * |∫ y * (deriv g)(at_*x+bt_*y) dγ|
  --   ≤ (at_/bt_) * at_ * M * C_abs_y.
  set M_dd : ℝ := (at_ / bt_) * at_ * M * C_abs_y with hMdd_def
  have hMdd_nn : 0 ≤ M_dd := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hat_nn) hM_nn) hCabs_nn
    exact div_nonneg hat_nn hbt_nn
  have h_dd_Ptg_bd : ∀ x, |deriv (deriv (ouSemigroup t g)) x| ≤ M_dd := by
    intro x
    rw [(h_dd_Ptg x).deriv]
    show |(at_ / bt_) * h_aux' x| ≤ M_dd
    have h_haux'_bd : |h_aux' x| ≤ at_ * M * C_abs_y := by
      show |at_ * ∫ y, y * deriv g (at_ * x + bt_ * y) ∂γ| ≤ at_ * M * C_abs_y
      rw [abs_mul, abs_of_nonneg hat_nn]
      have h_int_bd :
          |∫ y, y * deriv g (at_ * x + bt_ * y) ∂γ| ≤ M * C_abs_y := by
        calc |∫ y, y * deriv g (at_ * x + bt_ * y) ∂γ|
            ≤ ∫ y, |y * deriv g (at_ * x + bt_ * y)| ∂γ :=
              abs_integral_le_integral_abs
          _ ≤ ∫ y, M * |y| ∂γ := by
              refine integral_mono (h_aux'_int x).abs ?_ ?_
              · exact (h_abs_id_int.const_mul M)
              · intro y
                show |y * deriv g (at_ * x + bt_ * y)| ≤ M * |y|
                rw [abs_mul]
                calc |y| * |deriv g (at_ * x + bt_ * y)|
                    ≤ |y| * M :=
                      mul_le_mul_of_nonneg_left (hg'_bd _) (abs_nonneg _)
                  _ = M * |y| := mul_comm _ _
          _ = M * ∫ y, |y| ∂γ := by rw [integral_const_mul]
          _ = M * C_abs_y := rfl
      calc at_ * |∫ y, y * deriv g (at_ * x + bt_ * y) ∂γ|
          ≤ at_ * (M * C_abs_y) :=
            mul_le_mul_of_nonneg_left h_int_bd hat_nn
        _ = at_ * M * C_abs_y := by ring
    rw [abs_mul, abs_of_nonneg (div_nonneg hat_nn hbt_nn)]
    calc at_ / bt_ * |h_aux' x|
        ≤ at_ / bt_ * (at_ * M * C_abs_y) :=
          mul_le_mul_of_nonneg_left h_haux'_bd (div_nonneg hat_nn hbt_nn)
      _ = M_dd := by show _ = at_ / bt_ * at_ * M * C_abs_y; ring
  -- (C) log(P_t g) + 1 is C¹.
  have h_Ptg_C1 : ContDiff ℝ 1 (ouSemigroup t g) := by
    -- ContDiff 1 is implied by ContDiff 2.
    exact h_Ptg_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have h_logPtg_C1 : ContDiff ℝ 1 (fun y => Real.log (ouSemigroup t g y) + 1) := by
    -- log is C^∞ on ℝ \ {0}; compose with P_t g (which is C¹ and ≥ ε > 0).
    have h_log_cd : ContDiffOn ℝ ω Real.log ({0}ᶜ) := Real.contDiffOn_log
    have h_log_at : ∀ x, ContDiffAt ℝ 1 Real.log (ouSemigroup t g x) := by
      intro x
      have hx_pos : 0 < ouSemigroup t g x := h_Ptg_pos t ht.le x
      have hx : ouSemigroup t g x ∈ ({0} : Set ℝ)ᶜ := fun h => by
        rw [Set.mem_singleton_iff] at h; linarith
      have h_open : IsOpen ({0} : Set ℝ)ᶜ := isOpen_compl_singleton
      have h1 := h_log_cd.contDiffAt (h_open.mem_nhds hx)
      exact h1.of_le (by exact OrderTop.le_top _)
    -- Compose. Pointwise contDiffAt assemble to ContDiff via contDiff_iff_contDiffAt.
    have h_comp_at : ∀ x, ContDiffAt ℝ 1 (fun y => Real.log (ouSemigroup t g y)) x := by
      intro x
      exact (h_log_at x).comp x h_Ptg_C1.contDiffAt
    have h_comp : ContDiff ℝ 1 (fun y => Real.log (ouSemigroup t g y)) :=
      contDiff_iff_contDiffAt.mpr h_comp_at
    exact h_comp.add contDiff_const
  -- (D) Parametric DCT for the entropy: derivative of H(P_s g) at s = t equals
  -- the L²-paired integrand ∫ (L P_t g) · (1 + log P_t g) dγ, where
  -- L P_t g(y) := (P_t g)''(y) - y · (P_t g)'(y).
  --
  -- Strategy: differentiate F(s, y) := P_s g(y) · log(P_s g(y)) in `s` under
  -- the integral.  The inner s-derivative of `P_s g(y)` at `s = τ`, for any
  -- τ ∈ Ioo tlo thi, comes from parametric DCT in `s` of the Mehler integral
  -- (the integrand `g(α(s)y + b(s)z)` differentiates in s to
  -- `(deriv g)(α(s)y+b(s)z) · (α'(s)y + b'(s)z)`).  Combined with Stein at
  -- s = t, the result is `(L P_t g)(y) = (P_t g)''(y) - y · (P_t g)'(y)`.
  have h_param_deriv : HasDerivAt (fun s => boltzmannEntropy (ouSemigroup s g))
      (∫ y, (deriv (deriv (ouSemigroup t g)) y - y * deriv (ouSemigroup t g) y) *
            (Real.log (ouSemigroup t g y) + 1) ∂γ) t := by
    -- Uniform lower bound on b(s) over Ioo tlo thi.
    have h_b_τ_ge : ∀ τ ∈ Set.Ioo tlo thi, b tlo ≤ b τ := by
      intro τ hτ
      show Real.sqrt (1 - Real.exp (-2 * tlo)) ≤ Real.sqrt (1 - Real.exp (-2 * τ))
      apply Real.sqrt_le_sqrt
      have : Real.exp (-2 * τ) ≤ Real.exp (-2 * tlo) :=
        Real.exp_le_exp.mpr (by linarith [hτ.1])
      linarith
    -- Inner integrand of P_s g(y).
    set G : ℝ → ℝ → ℝ → ℝ := fun s y z => g (a s * y + b s * z) with hG_def
    set G' : ℝ → ℝ → ℝ → ℝ := fun s y z =>
      deriv g (a s * y + b s * z) *
        (-a s * y + (Real.exp (-2 * s) / b s) * z) with hG'_def
    -- (P_s g)(y) = ∫ z, G s y z dγ for any s.
    have hPsg_eq : ∀ s y, ouSemigroup s g y = ∫ z, G s y z ∂γ := fun s y => rfl
    -- α(s)·y + b(s)·z is C¹ in s with derivative -α(s)·y + b'(s)·z (for s ∈ Ioo tlo thi).
    have hG_deriv_s : ∀ s y z, s ∈ Set.Ioo tlo thi →
        HasDerivAt (fun u => G u y z) (G' s y z) s := by
      intro s y z hs
      have h_α : HasDerivAt (fun u : ℝ => a u * y) (-a s * y) s := by
        have h1 : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) s := by
          convert (hasDerivAt_id s).neg using 1
          rfl
        have h2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-s) * (-1)) s := h1.exp
        have h3 : HasDerivAt (fun u : ℝ => Real.exp (-u) * y)
            (Real.exp (-s) * (-1) * y) s := h2.mul_const y
        have : (Real.exp (-s) * (-1) * y) = -a s * y := by show _ = _; ring
        rw [← this]; exact h3
      have h_b' : HasDerivAt (fun u : ℝ => b u * z)
          ((Real.exp (-2 * s) / b s) * z) s :=
        (hasDerivAt_b s (by linarith [hs.1])).mul_const z
      have h_arg : HasDerivAt (fun u => a u * y + b u * z)
          (-a s * y + (Real.exp (-2 * s) / b s) * z) s := h_α.add h_b'
      have h_g_diff : HasDerivAt g (deriv g (a s * y + b s * z))
          (a s * y + b s * z) :=
        (hg.differentiable (by simp)).differentiableAt.hasDerivAt
      exact h_g_diff.comp s h_arg
    -- Uniform bound on |G' s y z| for s ∈ Ioo tlo thi:
    -- |G' s y z| ≤ M · (|y| + (1/b tlo) · |z|).
    have hb_tlo_pos : 0 < b tlo := hb_lo_pos
    have hG'_bd : ∀ s y z, s ∈ Set.Ioo tlo thi →
        |G' s y z| ≤ M * (|y| + (1 / b tlo) * |z|) := by
      intro s y z hs
      have h_dg_abs : |deriv g (a s * y + b s * z)| ≤ M := hg'_bd _
      have h_b_pos : 0 < b s := hb_pos_on_nbhd s hs
      have h_b_lo_le : b tlo ≤ b s := h_b_τ_ge s hs
      have h_a_le : a s ≤ 1 := h_a_le_one s (by linarith [hs.1, htlo_pos])
      have h_a_nn' : 0 ≤ a s := h_a_nn s
      have h_e_2s_nn : 0 ≤ Real.exp (-2 * s) := (Real.exp_pos _).le
      have h_e_2s_le : Real.exp (-2 * s) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith [hs.1, htlo_pos])
      have h_div_le : Real.exp (-2 * s) / b s ≤ 1 / b tlo := by
        rw [div_le_div_iff₀ h_b_pos hb_tlo_pos]
        calc Real.exp (-2 * s) * b tlo
            ≤ 1 * b tlo :=
              mul_le_mul_of_nonneg_right h_e_2s_le hb_tlo_pos.le
          _ = b tlo := one_mul _
          _ ≤ b s := h_b_lo_le
          _ = 1 * b s := (one_mul _).symm
      have h_div_nn : 0 ≤ Real.exp (-2 * s) / b s := div_nonneg h_e_2s_nn h_b_pos.le
      have h_factor_abs :
          |-a s * y + (Real.exp (-2 * s) / b s) * z| ≤
            |y| + (1 / b tlo) * |z| := by
        have h_step1 : |-a s * y + (Real.exp (-2 * s) / b s) * z| ≤
            |-a s * y| + |(Real.exp (-2 * s) / b s) * z| := abs_add_le _ _
        have h_step2 : |-a s * y| = a s * |y| := by
          rw [abs_mul, abs_neg, abs_of_nonneg h_a_nn']
        have h_step3 : |(Real.exp (-2 * s) / b s) * z| =
            (Real.exp (-2 * s) / b s) * |z| := by
          rw [abs_mul, abs_of_nonneg h_div_nn]
        have h_step4 : a s * |y| ≤ 1 * |y| :=
          mul_le_mul_of_nonneg_right h_a_le (abs_nonneg _)
        have h_step5 : (Real.exp (-2 * s) / b s) * |z| ≤ (1 / b tlo) * |z| :=
          mul_le_mul_of_nonneg_right h_div_le (abs_nonneg _)
        linarith
      have h_main : |deriv g (a s * y + b s * z) *
              (-a s * y + (Real.exp (-2 * s) / b s) * z)| ≤
            M * (|y| + (1 / b tlo) * |z|) := by
        rw [abs_mul]
        exact mul_le_mul h_dg_abs h_factor_abs (abs_nonneg _) hM_nn
      exact h_main
    -- (d/ds)[P_s g(y)] from outer DCT in z.
    -- For each y, set Inner_s_y(z) := G s y z. Apply parametric DCT in s with z the dummy.
    -- Get HasDerivAt (fun u => ∫ z, G u y z dγ) (∫ z, G' s y z dγ) s.
    set hPsy : ℝ → ℝ → ℝ :=
        fun s y => ∫ z, G' s y z ∂γ with hPsy_def
    have h_inner_deriv : ∀ y, HasDerivAt
        (fun s => ouSemigroup s g y) (hPsy t y) t := by
      intro y
      -- Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le.
      have hG_meas : ∀ s, AEStronglyMeasurable (G s y) γ := fun s =>
        (hg_meas.comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      have hG_int : Integrable (G t y) γ := by
        refine Integrable.mono' (integrable_const M) (hG_meas t) ?_
        filter_upwards with z; rw [Real.norm_eq_abs]; exact h_gabs _
      set bound_inner : ℝ → ℝ := fun z => M * (|y| + (1 / b tlo) * |z|)
        with hbound_inner_def
      have h_bound_inner_int : Integrable bound_inner γ := by
        show Integrable (fun z => M * (|y| + (1 / b tlo) * |z|)) γ
        have heq : (fun z => M * (|y| + (1 / b tlo) * |z|)) =
            (fun z => M * |y| + (M * (1 / b tlo)) * |z|) := by
          funext z; ring
        rw [heq]
        refine Integrable.add (integrable_const _) ?_
        exact h_abs_id_int.const_mul _
      have hG'_meas : AEStronglyMeasurable (G' t y) γ := by
        refine ((hg'_meas.comp ?_).mul ?_).aestronglyMeasurable
        · exact measurable_const.add (measurable_const.mul measurable_id)
        · exact measurable_const.add (measurable_const.mul measurable_id)
      have h_bd_inner : ∀ᵐ z ∂γ, ∀ s ∈ Set.Ioo tlo thi,
          ‖G' s y z‖ ≤ bound_inner z := by
        filter_upwards with z s hs
        show ‖G' s y z‖ ≤ M * (|y| + (1 / b tlo) * |z|)
        rw [Real.norm_eq_abs]
        exact hG'_bd s y z hs
      have h_diff_inner : ∀ᵐ z ∂γ, ∀ s ∈ Set.Ioo tlo thi,
          HasDerivAt (fun u => G u y z) (G' s y z) s := by
        filter_upwards with z s hs
        exact hG_deriv_s s y z hs
      obtain ⟨_, h_deriv⟩ :=
        hasDerivAt_integral_of_dominated_loc_of_deriv_le h_nbhd
          (Filter.Eventually.of_forall hG_meas) hG_int hG'_meas h_bd_inner
          h_bound_inner_int h_diff_inner
      -- h_deriv : HasDerivAt (fun s => ∫ z, G s y z ∂γ) (∫ z, G' t y z ∂γ) t.
      -- And (fun s => ∫ z, G s y z ∂γ) = (fun s => ouSemigroup s g y).
      have h_eq : (fun s => ∫ z, G s y z ∂γ) = (fun s => ouSemigroup s g y) :=
        funext fun s => (hPsg_eq s y).symm
      rw [h_eq] at h_deriv
      exact h_deriv
    -- At s = t: hPsy t y = (P_t g)''(y) - y · (P_t g)'(y).
    have h_inner_at_t : ∀ y, hPsy t y =
        deriv (deriv (ouSemigroup t g)) y - y * deriv (ouSemigroup t g) y := by
      intro y
      show ∫ z, G' t y z ∂γ =
        deriv (deriv (ouSemigroup t g)) y - y * deriv (ouSemigroup t g) y
      -- Split G' t y z into two parts.
      -- G' t y z = (-at_) * y * (deriv g)(at_·y + bt_·z)
      --         + (exp(-2t)/bt_) * z * (deriv g)(at_·y + bt_·z).
      have h_split : ∀ z, G' t y z =
          -at_ * y * deriv g (at_ * y + bt_ * z) +
          (Real.exp (-2 * t) / bt_) * z * deriv g (at_ * y + bt_ * z) := by
        intro z
        show deriv g (a t * y + b t * z) *
              (-a t * y + (Real.exp (-2 * t) / b t) * z) = _
        change deriv g (at_ * y + bt_ * z) *
              (-at_ * y + (Real.exp (-2 * t) / bt_) * z) = _
        ring
      have h_int_pt1 : Integrable
          (fun z => -at_ * y * deriv g (at_ * y + bt_ * z)) γ := by
        refine Integrable.const_mul ?_ _
        refine Integrable.mono' (integrable_const M) ?_ ?_
        · exact (hg'_meas.comp
            (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
        · filter_upwards with z; rw [Real.norm_eq_abs]; exact hg'_bd _
      have h_int_pt2 : Integrable
          (fun z => (Real.exp (-2 * t) / bt_) * z *
            deriv g (at_ * y + bt_ * z)) γ := by
        refine Integrable.mono' ((h_abs_id_int.const_mul
          ((Real.exp (-2 * t) / bt_) * M)).abs) ?_ ?_
        · exact (((measurable_const.mul measurable_id).mul
            (hg'_meas.comp (measurable_const.add
              (measurable_const.mul measurable_id))))).aestronglyMeasurable
        · filter_upwards with z
          have h_e_2t_nn : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
          have h_coeff_nn : 0 ≤ Real.exp (-2 * t) / bt_ :=
            div_nonneg h_e_2t_nn hbt_nn
          show ‖(Real.exp (-2 * t) / bt_) * z * deriv g (at_ * y + bt_ * z)‖ ≤
            ‖Real.exp (-2 * t) / bt_ * M * |z|‖
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h_coeff_nn,
              Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h_coeff_nn,
              abs_abs, abs_of_nonneg hM_nn]
          have h_dg : |deriv g (at_ * y + bt_ * z)| ≤ M := hg'_bd _
          calc Real.exp (-2 * t) / bt_ * |z| * |deriv g (at_ * y + bt_ * z)|
              ≤ Real.exp (-2 * t) / bt_ * |z| * M :=
                mul_le_mul_of_nonneg_left h_dg
                  (mul_nonneg h_coeff_nn (abs_nonneg _))
            _ = Real.exp (-2 * t) / bt_ * M * |z| := by ring
      have h_pt1 : ∫ z, -at_ * y * deriv g (at_ * y + bt_ * z) ∂γ =
          -at_ * y * ouSemigroup t (deriv g) y := by
        rw [integral_const_mul]; rfl
      have h_pt2 : ∫ z, (Real.exp (-2 * t) / bt_) * z *
            deriv g (at_ * y + bt_ * z) ∂γ =
          (Real.exp (-2 * t) / bt_) *
            ∫ z, z * deriv g (at_ * y + bt_ * z) ∂γ := by
        have h_rw : (fun z => (Real.exp (-2 * t) / bt_) * z *
            deriv g (at_ * y + bt_ * z)) =
            (fun z => (Real.exp (-2 * t) / bt_) * (z * deriv g (at_ * y + bt_ * z))) := by
          funext z; ring
        rw [h_rw, integral_const_mul]
      -- ∫ z, z * deriv g (at_*y + bt_*z) dγ = h_aux' y / at_ = (1/at_) * h_aux' y.
      -- Actually h_aux' y = at_ * ∫ z, z * deriv g (at_·y + bt_·z) dγ.
      have h_aux'_split : ∫ z, z * deriv g (at_ * y + bt_ * z) ∂γ = h_aux' y / at_ := by
        show ∫ z, z * deriv g (at_ * y + bt_ * z) ∂γ =
              (at_ * ∫ z, z * deriv g (at_ * y + bt_ * z) ∂γ) / at_
        have hat_ne : at_ ≠ 0 := hat_pos.ne'
        rw [mul_div_cancel_left₀ _ hat_ne]
      -- Compute ∫ G' t y z dγ.
      have h_integral : ∫ z, G' t y z ∂γ =
          -at_ * y * ouSemigroup t (deriv g) y +
          (Real.exp (-2 * t) / bt_) * (h_aux' y / at_) := by
        have h_rw : (fun z => G' t y z) =
            (fun z => -at_ * y * deriv g (at_ * y + bt_ * z) +
              (Real.exp (-2 * t) / bt_) * z * deriv g (at_ * y + bt_ * z)) := by
          funext z; exact h_split z
        rw [h_rw, integral_add h_int_pt1 h_int_pt2, h_pt1, h_pt2, h_aux'_split]
      rw [h_integral]
      -- RHS: deriv (deriv (P_t g)) y - y · deriv (P_t g) y.
      -- deriv (P_t g) y = at_ * ouSemigroup t (deriv g) y.
      -- deriv (deriv (P_t g)) y = (at_/bt_) * h_aux' y.
      rw [(h_dd_Ptg y).deriv, h_deriv_Ptg_eq t y]
      -- Goal: -at_ * y * ouSemigroup t (deriv g) y +
      --       (Real.exp (-2 * t) / bt_) * (h_aux' y / at_)
      --     = (at_/bt_) * h_aux' y - y * (a t * ouSemigroup t (deriv g) y).
      -- Use: exp(-2t) = at_ * at_.
      have h_exp_2t : Real.exp (-2 * t) = at_ * at_ := by
        show Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t)
        rw [← Real.exp_add]; congr 1; ring
      change -at_ * y * ouSemigroup t (deriv g) y +
            (Real.exp (-2 * t) / bt_) * (h_aux' y / at_)
          = at_ / bt_ * h_aux' y - y * (at_ * ouSemigroup t (deriv g) y)
      rw [h_exp_2t]
      field_simp
      ring
    -- Now apply parametric DCT to the outer integrand F(s, y) := P_s g(y) · log(P_s g(y)).
    -- The s-derivative at s = τ is (d/ds P_s g(y)) · (1 + log P_s g(y)) = hPsy τ y · (1 + log P_τ g y).
    set F_outer : ℝ → ℝ → ℝ := fun s y => ouSemigroup s g y * Real.log (ouSemigroup s g y)
      with hF_outer_def
    set F_outer' : ℝ → ℝ → ℝ := fun s y =>
      hPsy s y * (Real.log (ouSemigroup s g y) + 1) with hF_outer'_def
    -- Uniform bound on hPsy s y for s ∈ Ioo tlo thi:
    --   |hPsy s y| ≤ ∫ z, |G' s y z| dγ ≤ ∫ z, M · (|y| + (1/b tlo) · |z|) dγ
    --              = M · |y| + M · (1/b tlo) · C_abs_y.
    have h_hPsy_bd : ∀ s y, s ∈ Set.Ioo tlo thi →
        |hPsy s y| ≤ M * |y| + (M * (1 / b tlo)) * C_abs_y := by
      intro s y hs
      show |∫ z, G' s y z ∂γ| ≤ M * |y| + (M * (1 / b tlo)) * C_abs_y
      have h_int : Integrable (fun z => G' s y z) γ := by
        refine Integrable.mono' (?_ : Integrable
          (fun z => M * (|y| + (1 / b tlo) * |z|)) γ) ?_ ?_
        · have heq : (fun z => M * (|y| + (1 / b tlo) * |z|)) =
              (fun z => M * |y| + (M * (1 / b tlo)) * |z|) := by
            funext z; ring
          rw [heq]
          refine Integrable.add (integrable_const _) ?_
          exact h_abs_id_int.const_mul _
        · refine ((hg'_meas.comp ?_).mul ?_).aestronglyMeasurable
          · exact measurable_const.add (measurable_const.mul measurable_id)
          · exact measurable_const.add (measurable_const.mul measurable_id)
        · filter_upwards with z; rw [Real.norm_eq_abs]; exact hG'_bd s y z hs
      calc |∫ z, G' s y z ∂γ|
          ≤ ∫ z, |G' s y z| ∂γ := abs_integral_le_integral_abs
        _ ≤ ∫ z, M * (|y| + (1 / b tlo) * |z|) ∂γ := by
            refine integral_mono h_int.abs ?_ ?_
            · have heq : (fun z => M * (|y| + (1 / b tlo) * |z|)) =
                  (fun z => M * |y| + (M * (1 / b tlo)) * |z|) := by
                funext z; ring
              rw [heq]
              refine Integrable.add (integrable_const _) ?_
              exact h_abs_id_int.const_mul _
            · intro z; exact hG'_bd s y z hs
        _ = ∫ z, (M * |y| + (M * (1 / b tlo)) * |z|) ∂γ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            ring
        _ = M * |y| + (M * (1 / b tlo)) * C_abs_y := by
            rw [integral_add (integrable_const _)
                  (h_abs_id_int.const_mul _),
                integral_const, integral_const_mul]
            simp [C_abs_y, measureReal_def, measure_univ]
    -- Uniform bound on log: |log (P_s g y) + 1| ≤ Mlog for s ∈ [tlo, thi] ⊂ (0, ∞).
    have h_log_bd_s : ∀ s y, s ∈ Set.Ioo tlo thi →
        |Real.log (ouSemigroup s g y) + 1| ≤ Mlog := by
      intro s y hs
      have hs_nn : 0 ≤ s := by linarith [hs.1, htlo_pos]
      have h_Psg_lo := h_Ptg_lo s hs_nn y
      have h_Psg_hi := h_Ptg_hi s hs_nn y
      have hPsg_pos := h_Ptg_pos s hs_nn y
      have hlog_bd : |Real.log (ouSemigroup s g y)| ≤ |Real.log ε| + |Real.log M| := by
        by_cases hcase : ouSemigroup s g y ≤ 1
        · have h_log_le_0 : Real.log (ouSemigroup s g y) ≤ 0 :=
            Real.log_nonpos hPsg_pos.le hcase
          have h_log_eps_le : Real.log ε ≤ Real.log (ouSemigroup s g y) :=
            Real.log_le_log hε h_Psg_lo
          rw [abs_of_nonpos h_log_le_0]
          have h_eps_log_nonpos : Real.log ε ≤ 0 :=
            Real.log_nonpos hε.le (le_trans h_Psg_lo hcase)
          rw [abs_of_nonpos h_eps_log_nonpos]
          linarith [abs_nonneg (Real.log M)]
        · have h1' : (1 : ℝ) < ouSemigroup s g y := not_le.mp hcase
          have h_log_nn : 0 ≤ Real.log (ouSemigroup s g y) := Real.log_nonneg h1'.le
          have h_log_le_M : Real.log (ouSemigroup s g y) ≤ Real.log M :=
            Real.log_le_log hPsg_pos h_Psg_hi
          have h_log_M_nn : 0 ≤ Real.log M := h_log_nn.trans h_log_le_M
          rw [abs_of_nonneg h_log_nn, abs_of_nonneg h_log_M_nn]
          linarith [abs_nonneg (Real.log ε)]
      calc |Real.log (ouSemigroup s g y) + 1|
          ≤ |Real.log (ouSemigroup s g y)| + |(1 : ℝ)| := abs_add_le _ _
        _ ≤ (|Real.log ε| + |Real.log M|) + 1 := by gcongr; rw [abs_one]
        _ = Mlog := by simp [Mlog]
    -- Bound on |F_outer'|:
    -- |F_outer' s y| ≤ (M·|y| + M·(1/b tlo)·C_abs_y) · Mlog.
    set bound_outer : ℝ → ℝ := fun y =>
      (M * |y| + (M * (1 / b tlo)) * C_abs_y) * Mlog with hbound_outer_def
    have h_bound_outer_int : Integrable bound_outer γ := by
      show Integrable (fun y => (M * |y| + (M * (1 / b tlo)) * C_abs_y) * Mlog) γ
      have heq : (fun y => (M * |y| + (M * (1 / b tlo)) * C_abs_y) * Mlog) =
          (fun y => (M * Mlog) * |y| + (M * (1 / b tlo) * C_abs_y * Mlog)) := by
        funext y; ring
      rw [heq]
      refine Integrable.add ?_ (integrable_const _)
      exact h_abs_id_int.const_mul _
    have h_F_outer'_bd : ∀ᵐ y ∂γ, ∀ s ∈ Set.Ioo tlo thi,
        ‖F_outer' s y‖ ≤ bound_outer y := by
      filter_upwards with y s hs
      show ‖hPsy s y * (Real.log (ouSemigroup s g y) + 1)‖ ≤
        (M * |y| + (M * (1 / b tlo)) * C_abs_y) * Mlog
      rw [Real.norm_eq_abs, abs_mul]
      have h_hPsy := h_hPsy_bd s y hs
      have h_log := h_log_bd_s s y hs
      have h_lhs_nn : 0 ≤ M * |y| + (M * (1 / b tlo)) * C_abs_y := by
        refine add_nonneg ?_ ?_
        · exact mul_nonneg hM_nn (abs_nonneg _)
        · refine mul_nonneg (mul_nonneg hM_nn ?_) hCabs_nn
          exact div_nonneg (by norm_num) hb_tlo_pos.le
      exact mul_le_mul h_hPsy h_log (abs_nonneg _) h_lhs_nn
    -- F_outer is measurable for each s.
    have hF_outer_meas : ∀ s, AEStronglyMeasurable (F_outer s) γ := fun s =>
      ((h_Ptg_meas s).mul (h_Ptg_meas s).log).aestronglyMeasurable
    -- F_outer t is γ-integrable.
    have hF_outer_int : Integrable (F_outer t) γ := by
      refine Integrable.mono' (integrable_const (M * (|Real.log ε| + |Real.log M|))) ?_ ?_
      · exact hF_outer_meas t
      · filter_upwards with y
        show ‖ouSemigroup t g y * Real.log (ouSemigroup t g y)‖ ≤
          M * (|Real.log ε| + |Real.log M|)
        rw [Real.norm_eq_abs, abs_mul]
        have hP_lo := h_Ptg_lo t ht.le y
        have hP_hi := h_Ptg_hi t ht.le y
        have hP_pos := h_Ptg_pos t ht.le y
        have hlog_abs_bd : |Real.log (ouSemigroup t g y)| ≤
            |Real.log ε| + |Real.log M| := by
          by_cases hcase : ouSemigroup t g y ≤ 1
          · have h_log_le_0 : Real.log (ouSemigroup t g y) ≤ 0 :=
              Real.log_nonpos hP_pos.le hcase
            have h_log_eps_le : Real.log ε ≤ Real.log (ouSemigroup t g y) :=
              Real.log_le_log hε hP_lo
            rw [abs_of_nonpos h_log_le_0]
            have h_eps_log_nonpos : Real.log ε ≤ 0 :=
              Real.log_nonpos hε.le (le_trans hP_lo hcase)
            rw [abs_of_nonpos h_eps_log_nonpos]
            linarith [abs_nonneg (Real.log M)]
          · have h1' : (1 : ℝ) < ouSemigroup t g y := not_le.mp hcase
            have h_log_nn : 0 ≤ Real.log (ouSemigroup t g y) := Real.log_nonneg h1'.le
            have h_log_le_M : Real.log (ouSemigroup t g y) ≤ Real.log M :=
              Real.log_le_log hP_pos hP_hi
            have h_log_M_nn : 0 ≤ Real.log M := h_log_nn.trans h_log_le_M
            rw [abs_of_nonneg h_log_nn, abs_of_nonneg h_log_M_nn]
            linarith [abs_nonneg (Real.log ε)]
        have h_g_abs : |ouSemigroup t g y| ≤ M := h_Ptg_abs t ht.le y
        exact mul_le_mul h_g_abs hlog_abs_bd (abs_nonneg _) hM_nn
    have hF_outer'_meas : AEStronglyMeasurable (F_outer' t) γ := by
      show AEStronglyMeasurable
        (fun y => hPsy t y * (Real.log (ouSemigroup t g y) + 1)) γ
      -- hPsy t y = (P_t g)''(y) - y * (P_t g)'(y) by h_inner_at_t.
      have h_eq : (fun y => hPsy t y * (Real.log (ouSemigroup t g y) + 1)) =
          (fun y => (deriv (deriv (ouSemigroup t g)) y - y * deriv (ouSemigroup t g) y) *
            (Real.log (ouSemigroup t g y) + 1)) := by
        funext y; rw [h_inner_at_t y]
      rw [h_eq]
      -- The RHS is measurable: P_t g is C², log P_t g + 1 is C¹.
      have h_dd_meas : Measurable (deriv (deriv (ouSemigroup t g))) := by
        have h_C1' : ContDiff ℝ 1 (deriv (ouSemigroup t g)) := by
          have h2 : ContDiff ℝ (1 + 1) (ouSemigroup t g) := by convert h_Ptg_C2 using 1; norm_num
          exact h2.deriv'
        exact (h_C1'.continuous_deriv (le_refl 1)).measurable
      have h_d_meas : Measurable (deriv (ouSemigroup t g)) :=
        (h_Ptg_C2.continuous_deriv (by norm_num)).measurable
      have h_log_meas : Measurable (fun y => Real.log (ouSemigroup t g y) + 1) :=
        (h_logPtg_C1.continuous.measurable)
      exact ((h_dd_meas.sub (measurable_id.mul h_d_meas)).mul h_log_meas).aestronglyMeasurable
    -- HasDerivAt of the inner integrand F_outer wrt s.
    -- d/ds [P_s g(y) · log(P_s g(y))] = (d/ds P_s g y) · (1 + log P_s g y)
    -- by chain rule: f(u) := u log u, f'(u) = log u + 1.
    have h_F_outer_diff : ∀ᵐ y ∂γ, ∀ s ∈ Set.Ioo tlo thi,
        HasDerivAt (fun u => F_outer u y) (F_outer' s y) s := by
      filter_upwards with y s hs
      have hs_nn : 0 ≤ s := by linarith [hs.1, htlo_pos]
      have hPsg_pos := h_Ptg_pos s hs_nn y
      -- Let u(s) := ouSemigroup s g y.  Then F_outer s y = u(s) * log(u(s)).
      -- Chain rule with mul_log.
      have h_inner_at_s : HasDerivAt (fun s => ouSemigroup s g y) (hPsy s y) s := by
        -- Reapply parametric DCT at s (similar to h_inner_deriv but at s instead of t).
        -- For an arbitrary s ∈ Ioo tlo thi, we redo the argument.  This is exactly
        -- the same computation as for h_inner_deriv, but parameterized at s.
        have hG_meas : ∀ u, AEStronglyMeasurable (G u y) γ := fun u =>
          (hg_meas.comp
            (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
        have hG_int : Integrable (G s y) γ := by
          refine Integrable.mono' (integrable_const M) (hG_meas s) ?_
          filter_upwards with z; rw [Real.norm_eq_abs]; exact h_gabs _
        set bound_inner : ℝ → ℝ := fun z => M * (|y| + (1 / b tlo) * |z|)
        have h_bound_inner_int : Integrable bound_inner γ := by
          show Integrable (fun z => M * (|y| + (1 / b tlo) * |z|)) γ
          have heq : (fun z => M * (|y| + (1 / b tlo) * |z|)) =
              (fun z => M * |y| + (M * (1 / b tlo)) * |z|) := by
            funext z; ring
          rw [heq]
          refine Integrable.add (integrable_const _) ?_
          exact h_abs_id_int.const_mul _
        have hG'_meas : AEStronglyMeasurable (G' s y) γ := by
          refine ((hg'_meas.comp ?_).mul ?_).aestronglyMeasurable
          · exact measurable_const.add (measurable_const.mul measurable_id)
          · exact measurable_const.add (measurable_const.mul measurable_id)
        have h_bd_inner : ∀ᵐ z ∂γ, ∀ u ∈ Set.Ioo tlo thi,
            ‖G' u y z‖ ≤ bound_inner z := by
          filter_upwards with z u hu
          show ‖G' u y z‖ ≤ M * (|y| + (1 / b tlo) * |z|)
          rw [Real.norm_eq_abs]; exact hG'_bd u y z hu
        have h_diff_inner : ∀ᵐ z ∂γ, ∀ u ∈ Set.Ioo tlo thi,
            HasDerivAt (fun v => G v y z) (G' u y z) u := by
          filter_upwards with z u hu
          exact hG_deriv_s u y z hu
        have h_nbhd_s : Set.Ioo tlo thi ∈ nhds s := IsOpen.mem_nhds isOpen_Ioo hs
        obtain ⟨_, h_deriv⟩ :=
          hasDerivAt_integral_of_dominated_loc_of_deriv_le h_nbhd_s
            (Filter.Eventually.of_forall hG_meas) hG_int hG'_meas h_bd_inner
            h_bound_inner_int h_diff_inner
        have h_eq : (fun u => ∫ z, G u y z ∂γ) = (fun u => ouSemigroup u g y) :=
          funext fun u => (hPsg_eq u y).symm
        rw [h_eq] at h_deriv
        exact h_deriv
      -- Apply chain rule: u(s) log(u(s)).
      have h_u_pos : 0 < ouSemigroup s g y := hPsg_pos
      have h_log_at : HasDerivAt Real.log (ouSemigroup s g y)⁻¹ (ouSemigroup s g y) :=
        Real.hasDerivAt_log h_u_pos.ne'
      have h_log_comp : HasDerivAt (fun u => Real.log (ouSemigroup u g y))
          (hPsy s y * (ouSemigroup s g y)⁻¹) s := by
        have := h_log_at.comp s h_inner_at_s
        simpa only [Function.comp_def, mul_comm] using this
      -- Now d/ds [P_s g y * log(P_s g y)] = hPsy s y * log(P_s g y) + P_s g y * (hPsy s y / P_s g y)
      --                                    = hPsy s y * (log(P_s g y) + 1).
      have h_prod : HasDerivAt (fun u => ouSemigroup u g y * Real.log (ouSemigroup u g y))
          (hPsy s y * Real.log (ouSemigroup s g y) +
            ouSemigroup s g y * (hPsy s y * (ouSemigroup s g y)⁻¹)) s :=
        h_inner_at_s.mul h_log_comp
      show HasDerivAt (fun u => F_outer u y) (F_outer' s y) s
      change HasDerivAt (fun u => ouSemigroup u g y * Real.log (ouSemigroup u g y))
        (hPsy s y * (Real.log (ouSemigroup s g y) + 1)) s
      have h_eq : hPsy s y * Real.log (ouSemigroup s g y) +
            ouSemigroup s g y * (hPsy s y * (ouSemigroup s g y)⁻¹) =
          hPsy s y * (Real.log (ouSemigroup s g y) + 1) := by
        have h_ne : ouSemigroup s g y ≠ 0 := h_u_pos.ne'
        field_simp
      rw [← h_eq]; exact h_prod
    -- Apply parametric DCT.
    obtain ⟨_, h_outer_deriv⟩ :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le h_nbhd
        (Filter.Eventually.of_forall hF_outer_meas) hF_outer_int hF_outer'_meas
        h_F_outer'_bd h_bound_outer_int h_F_outer_diff
    -- h_outer_deriv : HasDerivAt (fun s => ∫ y, F_outer s y ∂γ) (∫ y, F_outer' t y ∂γ) t.
    -- The LHS is `fun s => boltzmannEntropy (ouSemigroup s g)`.
    have h_lhs_eq : (fun s => ∫ y, F_outer s y ∂γ) =
        (fun s => boltzmannEntropy (ouSemigroup s g)) := by
      funext s; rfl
    -- The RHS: ∫ y, F_outer' t y ∂γ = ∫ y, hPsy t y · (1 + log P_t g y) dγ.
    -- And hPsy t y = (P_t g)''(y) - y · (P_t g)'(y).
    have h_rhs_eq : ∫ y, F_outer' t y ∂γ =
        ∫ y, (deriv (deriv (ouSemigroup t g)) y - y * deriv (ouSemigroup t g) y) *
          (Real.log (ouSemigroup t g y) + 1) ∂γ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show hPsy t y * (Real.log (ouSemigroup t g y) + 1) =
        (deriv (deriv (ouSemigroup t g)) y - y * deriv (ouSemigroup t g) y) *
          (Real.log (ouSemigroup t g y) + 1)
      rw [h_inner_at_t y]
    rw [← h_lhs_eq, ← h_rhs_eq]
    exact h_outer_deriv
  -- ===========================================================================
  -- Phase 4 (provable): bilinear Dirichlet form ⇒ -fisherInfo.
  -- ===========================================================================
  -- Apply gaussian_dirichlet_form_bilinear with
  --   f := fun y => Real.log (P_t g y) + 1
  --   h := ouSemigroup t g
  -- which gives:
  --   ∫ (log P_t g + 1) · ((P_t g)'' - y · (P_t g)') dγ = -∫ (deriv f) · (deriv h) dγ
  -- and (deriv f) · (deriv h) = ((P_t g)'/P_t g) · (P_t g)' = ((P_t g)')² / (P_t g).
  -- Bounds for gaussian_dirichlet_form_bilinear: |f|, |f'| ≤ max(Mlog, M/ε);
  -- |h|, |h'|, |h''| ≤ max(M, M, M_dd).
  have h_bilinear : ∫ y, (deriv (deriv (ouSemigroup t g)) y - y * deriv (ouSemigroup t g) y) *
      (Real.log (ouSemigroup t g y) + 1) ∂γ = -fisherInfo (ouSemigroup t g) := by
    -- Set up the maximum bound for f and the bound for h, h', h''.
    set Mf : ℝ := max Mlog (M / ε) with hMf_def
    have hMf_lo_log : ∀ x, |Real.log (ouSemigroup t g x) + 1| ≤ Mf := fun x =>
      (h_log_bd x).trans (le_max_left _ _)
    have hMf_lo_log' : ∀ x,
        |deriv (fun y => Real.log (ouSemigroup t g y) + 1) x| ≤ Mf := fun x =>
      (h_logPtg'_bd x).trans (le_max_right _ _)
    set Mh : ℝ := max (max M M) M_dd with hMh_def
    -- We need a single bound that works for h, h', h'' (not all the same).
    -- gaussian_dirichlet_form_bilinear takes Mh, Mh', Mh'' separately.
    have h_apply :=
      gaussian_dirichlet_form_bilinear (f := fun y => Real.log (ouSemigroup t g y) + 1)
        (h := ouSemigroup t g) h_logPtg_C1 (Mf := Mf) hMf_lo_log hMf_lo_log'
        h_Ptg_C2 (Mh := M) (Mh' := M) (Mh'' := M_dd)
        (h_Ptg_abs t ht.le) (h_dPtg_abs t ht.le) h_dd_Ptg_bd
    -- h_apply : ∫ (log P_t g + 1) · ((P_t g)'' - y · (P_t g)') dγ
    --           = -∫ deriv(log P_t g + 1) · deriv(P_t g) dγ
    -- We want: ∫ (...) · (log P_t g + 1) = -fisherInfo.
    -- Rewrite the LHS of h_apply to match our target order.
    rw [show (fun y => (deriv (deriv (ouSemigroup t g)) y - y * deriv (ouSemigroup t g) y) *
        (Real.log (ouSemigroup t g y) + 1)) =
        (fun y => (Real.log (ouSemigroup t g y) + 1) *
        (deriv (deriv (ouSemigroup t g)) y - y * deriv (ouSemigroup t g) y)) from by
      funext y; ring]
    rw [h_apply]
    -- Now goal: -∫ deriv(log P_t g + 1) · deriv(P_t g) dγ = -fisherInfo (P_t g).
    -- deriv(log P_t g + 1) y = (P_t g)' y / (P_t g) y (by h_logPtg_deriv).
    show -∫ y, deriv (fun y => Real.log (ouSemigroup t g y) + 1) y *
        deriv (ouSemigroup t g) y ∂γ = -fisherInfo (ouSemigroup t g)
    congr 1
    have h_integrand_eq : (fun y => deriv (fun y => Real.log (ouSemigroup t g y) + 1) y *
        deriv (ouSemigroup t g) y) =
        (fun y => (deriv (ouSemigroup t g) y) ^ 2 / ouSemigroup t g y) := by
      funext y
      rw [(h_logPtg_deriv y).deriv]
      have hPtg_pos := h_Ptg_pos t ht.le y
      have hPtg_ne : ouSemigroup t g y ≠ 0 := hPtg_pos.ne'
      rw [sq, mul_div_assoc, mul_comm, ← mul_div_assoc, mul_div_assoc]
    rw [h_integrand_eq]
    rfl
  -- Combine the parametric derivative with the bilinear identity.
  convert h_param_deriv using 1
  exact h_bilinear.symm

/-- **Pointwise continuity of `s ↦ P_s g x` at `s = 0`** for bounded continuous `g`,
via DCT on the inner Mehler integrand. Inlined here to avoid an extra import. -/
private theorem tendsto_ouSemigroup_pointwise_atZero_local
    {g_aux : ℝ → ℝ} (hg_cont : Continuous g_aux) {M_g : ℝ} (hg_bd : ∀ y, |g_aux y| ≤ M_g) (x : ℝ) :
    Tendsto (fun s => ouSemigroup s g_aux x) (𝓝[Ici 0] 0) (𝓝 (g_aux x)) := by
  have h_rewrite : (fun s : ℝ => ouSemigroup s g_aux x) =
      fun s => ∫ y, g_aux (Real.exp (-s) * x +
        Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂γ := rfl
  rw [h_rewrite]
  have h_target : g_aux x = ∫ _y : ℝ, g_aux x ∂γ := by simp
  rw [h_target]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M_g) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with s _
    exact (hg_cont.comp ((continuous_const.mul continuous_const).add
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s _
    filter_upwards with y
    show ‖g_aux (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y)‖ ≤ M_g
    rw [Real.norm_eq_abs]
    exact hg_bd _
  · filter_upwards with y
    have h_arg : Tendsto (fun s : ℝ =>
        Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y)
        (𝓝[Ici 0] 0) (𝓝 x) := by
      have h_cont : ContinuousAt (fun s : ℝ =>
          Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y) 0 := by
        fun_prop
      have h := h_cont.tendsto
      have h_val : Real.exp (-(0 : ℝ)) * x + Real.sqrt (1 - Real.exp (-2 * 0)) * y = x := by
        simp
      rw [h_val] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact hg_cont.continuousAt.tendsto.comp h_arg

/-- **Boundary case of de Bruijn at `t = 0+`.** PROVED.

The de Bruijn identity extends to a right-derivative at `t = 0`:
`HasDerivWithinAt (s ↦ H(P_s g)) (-I(g)) (Ici 0) 0`.

Proof: apply `hasDerivWithinAt_Ici_of_tendsto_deriv`:
* Differentiability on `Ioi 0` — from `hasDerivAt_entropy_ouSemigroup` (A2).
* Continuity at `0` of the entropy `s ↦ H(P_s g)` — DCT, using `s · log s`
  continuous on `[ε, M]`.
* Convergence of the derivative `-I(P_s g) → -I(g)` as `s → 0+` — DCT
  again, using `((P_s g)')² / P_s g ≤ M²/ε` uniformly. -/
theorem hasDerivWithinAt_entropy_ouSemigroup_zero
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M) :
    HasDerivWithinAt (fun s => boltzmannEntropy (ouSemigroup s g))
      (-fisherInfo g) (Set.Ici 0) 0 := by
  -- Notation and bounds.
  have hε_nn : 0 ≤ ε := hε.le
  have hM_nn : 0 ≤ M := hε_nn.trans ((hg_lo 0).trans (hg_hi 0))
  have h_gpos : ∀ x, 0 < g x := fun x => lt_of_lt_of_le hε (hg_lo x)
  have h_gabs : ∀ x, |g x| ≤ M := fun x => by
    rw [abs_of_pos (h_gpos x)]; exact hg_hi x
  have hg_norm : ∀ x, ‖g x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs]; exact h_gabs x
  have hg'_norm : ∀ x, ‖deriv g x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs]; exact hg'_bd x
  have hg_cont : Continuous g := hg.continuous
  have hg_meas : Measurable g := hg_cont.measurable
  have hg'_cont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hg'_meas : Measurable (deriv g) := hg'_cont.measurable
  -- For each s ≥ 0, P_s g stays in [ε, M] and P_s (g') is bounded by M.
  have h_Ptg_lo : ∀ s, 0 ≤ s → ∀ x, ε ≤ ouSemigroup s g x := by
    intro s hs x
    set a := Real.exp (-s)
    set b := Real.sqrt (1 - Real.exp (-2 * s))
    show ε ≤ ∫ y, g (a * x + b * y) ∂γ
    have h_int : Integrable (fun y => g (a * x + b * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg_norm _
    have h_le : ∀ y, (ε : ℝ) ≤ g (a * x + b * y) := fun y => hg_lo _
    calc (ε : ℝ) = ∫ _, ε ∂γ := by simp
      _ ≤ ∫ y, g (a * x + b * y) ∂γ :=
            integral_mono (integrable_const _) h_int h_le
  have h_Ptg_hi : ∀ s, 0 ≤ s → ∀ x, ouSemigroup s g x ≤ M := by
    intro s hs x
    set a := Real.exp (-s)
    set b := Real.sqrt (1 - Real.exp (-2 * s))
    show ∫ y, g (a * x + b * y) ∂γ ≤ M
    have h_int : Integrable (fun y => g (a * x + b * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg_norm _
    calc ∫ y, g (a * x + b * y) ∂γ
        ≤ ∫ _, M ∂γ :=
            integral_mono h_int (integrable_const _) (fun y => hg_hi _)
      _ = M := by simp
  have h_Ptg_pos : ∀ s, 0 ≤ s → ∀ x, 0 < ouSemigroup s g x := fun s hs x =>
    lt_of_lt_of_le hε (h_Ptg_lo s hs x)
  have h_Ptg_abs : ∀ s, 0 ≤ s → ∀ x, |ouSemigroup s g x| ≤ M := fun s hs x => by
    rw [abs_of_pos (h_Ptg_pos s hs x)]; exact h_Ptg_hi s hs x
  -- |P_s (g') x| ≤ M.
  have h_Ptg'_abs : ∀ s, 0 ≤ s → ∀ x, |ouSemigroup s (deriv g) x| ≤ M := by
    intro s hs x
    set a := Real.exp (-s)
    set b := Real.sqrt (1 - Real.exp (-2 * s))
    show |∫ y, deriv g (a * x + b * y) ∂γ| ≤ M
    have h_int : Integrable (fun y => deriv g (a * x + b * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg'_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg'_norm _
    calc |∫ y, deriv g (a * x + b * y) ∂γ|
        ≤ ∫ y, |deriv g (a * x + b * y)| ∂γ := abs_integral_le_integral_abs
      _ ≤ ∫ _, M ∂γ :=
            integral_mono h_int.abs (integrable_const _) (fun y => hg'_bd _)
      _ = M := by simp
  -- Measurability of P_s g and its log/product.
  have h_Ptg_meas : ∀ s, Measurable (ouSemigroup s g) := fun s => by
    show Measurable fun x => ∫ y, g (Real.exp (-s) * x +
      Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂γ
    have h_sm : StronglyMeasurable
        (fun p : ℝ × ℝ => g (Real.exp (-s) * p.1 +
          Real.sqrt (1 - Real.exp (-2 * s)) * p.2)) :=
      (hg_cont.comp ((continuous_const.mul continuous_fst).add
        (continuous_const.mul continuous_snd))).stronglyMeasurable
    exact (h_sm.integral_prod_right' (ν := γ)).measurable
  have h_Ptdg_meas : ∀ s, Measurable (ouSemigroup s (deriv g)) := fun s => by
    show Measurable fun x => ∫ y, deriv g (Real.exp (-s) * x +
      Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂γ
    have h_sm : StronglyMeasurable
        (fun p : ℝ × ℝ => deriv g (Real.exp (-s) * p.1 +
          Real.sqrt (1 - Real.exp (-2 * s)) * p.2)) :=
      (hg'_cont.comp ((continuous_const.mul continuous_fst).add
        (continuous_const.mul continuous_snd))).stronglyMeasurable
    exact (h_sm.integral_prod_right' (ν := γ)).measurable
  -- For convenience: bound |s · log s| for s ∈ [ε, M] by K := M * (|log ε| + |log M|).
  set K : ℝ := M * (|Real.log ε| + |Real.log M|) with hK_def
  have h_log_bd : ∀ s, ε ≤ s → s ≤ M → |Real.log s| ≤ |Real.log ε| + |Real.log M| := by
    intro s hs1 hs2
    by_cases h1 : s ≤ 1
    · -- log s ≤ 0; -log s ≤ -log ε.
      have hs_pos : 0 < s := lt_of_lt_of_le hε hs1
      have h_log_s_le_0 : Real.log s ≤ 0 := Real.log_nonpos hs_pos.le h1
      have h_log_eps_le : Real.log ε ≤ Real.log s :=
        Real.log_le_log hε hs1
      rw [abs_of_nonpos h_log_s_le_0]
      have h_eps_log_nonpos : Real.log ε ≤ 0 := Real.log_nonpos hε.le (le_trans hs1 h1)
      rw [abs_of_nonpos h_eps_log_nonpos]
      linarith [abs_nonneg (Real.log M)]
    · have h1 : (1 : ℝ) < s := not_le.mp h1
      -- s > 1, so log s ≥ 0; log s ≤ log M.
      have hs_pos : (0 : ℝ) < s := lt_trans one_pos h1
      have h_log_s_nn : 0 ≤ Real.log s := Real.log_nonneg h1.le
      have h_log_s_le : Real.log s ≤ Real.log M :=
        Real.log_le_log hs_pos hs2
      have h_log_M_nn : 0 ≤ Real.log M := h_log_s_nn.trans h_log_s_le
      rw [abs_of_nonneg h_log_s_nn, abs_of_nonneg h_log_M_nn]
      linarith [abs_nonneg (Real.log ε)]
  have hK_nn : 0 ≤ K := by
    refine mul_nonneg hM_nn ?_
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have h_slog_bd : ∀ s, ε ≤ s → s ≤ M → |s * Real.log s| ≤ K := by
    intro s hs1 hs2
    have hs_nn : 0 ≤ s := hε_nn.trans hs1
    rw [abs_mul, abs_of_nonneg hs_nn]
    exact mul_le_mul hs2 (h_log_bd s hs1 hs2) (abs_nonneg _) hM_nn
  -- Pointwise convergence (P_s g) x → g x as s → 0+.
  have h_Ptg_tendsto : ∀ x,
      Tendsto (fun s => ouSemigroup s g x) (𝓝[Ici 0] 0) (𝓝 (g x)) := fun x =>
    tendsto_ouSemigroup_pointwise_atZero_local hg_cont h_gabs x
  have h_Ptdg_tendsto : ∀ x,
      Tendsto (fun s => ouSemigroup s (deriv g) x) (𝓝[Ici 0] 0) (𝓝 (deriv g x)) := fun x =>
    tendsto_ouSemigroup_pointwise_atZero_local hg'_cont hg'_bd x
  -- Continuity of the entropy at s = 0 (DCT).
  have h_entropy_tendsto :
      Tendsto (fun s => boltzmannEntropy (ouSemigroup s g))
        (𝓝[Ici 0] 0) (𝓝 (boltzmannEntropy g)) := by
    unfold boltzmannEntropy
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => K) ?_ ?_
      (integrable_const _) ?_
    · -- AEStronglyMeasurable for s in a neighborhood of 0 within Ici 0.
      filter_upwards [self_mem_nhdsWithin] with s _
      exact ((h_Ptg_meas s).mul (h_Ptg_meas s).log).aestronglyMeasurable
    · -- Pointwise bound |P_s g · log(P_s g)| ≤ K.
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs_nn : 0 ≤ s := hs
      filter_upwards with y
      show ‖ouSemigroup s g y * Real.log (ouSemigroup s g y)‖ ≤ K
      rw [Real.norm_eq_abs]
      have h_lo := h_Ptg_lo s hs_nn y
      have h_hi := h_Ptg_hi s hs_nn y
      exact h_slog_bd _ h_lo h_hi
    · -- Pointwise convergence at each y.
      filter_upwards with y
      have h_inner := h_Ptg_tendsto y
      have h_cont_at : ContinuousAt (fun u : ℝ => u * Real.log u) (g y) :=
        Real.continuous_mul_log.continuousAt
      exact h_cont_at.tendsto.comp h_inner
  -- Pointwise: (P_s g)'(x) = e^{-s} · P_s(g')(x), so
  -- ((P_s g)')²(x) / (P_s g)(x) = e^{-2s} · (P_s(g'))² / (P_s g).
  have h_deriv_Ptg : ∀ s, ∀ x,
      HasDerivAt (ouSemigroup s g)
        (Real.exp (-s) * ouSemigroup s (deriv g) x) x := fun s x =>
    hasDerivAt_ouSemigroup_C1 s hg hg_norm hg'_norm x
  have h_deriv_Ptg_eq : ∀ s, ∀ x,
      deriv (ouSemigroup s g) x = Real.exp (-s) * ouSemigroup s (deriv g) x :=
    fun s x => (h_deriv_Ptg s x).deriv
  -- Continuity of (fisherInfo (P_s g)) at s = 0+ via DCT.
  have h_fisher_tendsto :
      Tendsto (fun s => fisherInfo (ouSemigroup s g))
        (𝓝[Ici 0] 0) (𝓝 (fisherInfo g)) := by
    -- Rewrite fisherInfo (P_s g) using Mehler's derivative formula:
    -- ∫ ((P_s g)')² / (P_s g) dγ = ∫ (e^{-s} P_s(g'))² / (P_s g) dγ.
    have h_rewrite_fisher : ∀ s, 0 ≤ s →
        fisherInfo (ouSemigroup s g) =
          ∫ y, (Real.exp (-s) * ouSemigroup s (deriv g) y) ^ 2 / ouSemigroup s g y ∂γ := by
      intro s hs
      unfold fisherInfo
      apply integral_congr_ae
      filter_upwards with y
      rw [h_deriv_Ptg_eq s y]
    -- Pointwise convergence of integrand → (g'(y))² / g(y).
    -- And uniform bound M²/ε.
    have hMeps_nn : 0 ≤ M ^ 2 / ε := div_nonneg (sq_nonneg _) hε_nn
    set H : ℝ → ℝ → ℝ := fun s y =>
      (Real.exp (-s) * ouSemigroup s (deriv g) y) ^ 2 / ouSemigroup s g y with hH_def
    have h_tendsto_H :
        Tendsto (fun s => ∫ y, H s y ∂γ) (𝓝[Ici 0] 0)
          (𝓝 (∫ y, (deriv g y) ^ 2 / g y ∂γ)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => M ^ 2 / ε) ?_ ?_
        (integrable_const _) ?_
      · -- AEStronglyMeasurable for s in a neighborhood of 0 within Ici 0.
        filter_upwards [self_mem_nhdsWithin] with s _
        have h_meas_num : Measurable
            (fun y => (Real.exp (-s) * ouSemigroup s (deriv g) y) ^ 2) :=
          (measurable_const.mul (h_Ptdg_meas s)).pow_const 2
        exact (h_meas_num.div (h_Ptg_meas s)).aestronglyMeasurable
      · -- Pointwise bound.
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs_nn : 0 ≤ s := hs
        filter_upwards with y
        show ‖(Real.exp (-s) * ouSemigroup s (deriv g) y) ^ 2 /
          ouSemigroup s g y‖ ≤ M ^ 2 / ε
        have hPtg_pos := h_Ptg_pos s hs_nn y
        have hPtg_lo := h_Ptg_lo s hs_nn y
        have h_num_nn : 0 ≤ (Real.exp (-s) * ouSemigroup s (deriv g) y) ^ 2 := sq_nonneg _
        have h_quot_nn : 0 ≤ (Real.exp (-s) * ouSemigroup s (deriv g) y) ^ 2 /
            ouSemigroup s g y := div_nonneg h_num_nn hPtg_pos.le
        rw [Real.norm_eq_abs, abs_of_nonneg h_quot_nn]
        -- Numerator ≤ M².
        have h_exp_le : Real.exp (-s) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 by simp]
          exact Real.exp_le_exp.mpr (by linarith)
        have h_exp_nn : 0 ≤ Real.exp (-s) := (Real.exp_pos _).le
        have h_exp_abs : |Real.exp (-s)| ≤ 1 := by
          rw [abs_of_nonneg h_exp_nn]; exact h_exp_le
        have h_inner_abs : |Real.exp (-s) * ouSemigroup s (deriv g) y| ≤ M := by
          rw [abs_mul]
          calc |Real.exp (-s)| * |ouSemigroup s (deriv g) y|
              ≤ 1 * M :=
                mul_le_mul h_exp_abs (h_Ptg'_abs s hs_nn y) (abs_nonneg _) (by norm_num)
            _ = M := one_mul _
        have h_inner_sq_le : (Real.exp (-s) * ouSemigroup s (deriv g) y) ^ 2 ≤ M ^ 2 := by
          have h_eq : (Real.exp (-s) * ouSemigroup s (deriv g) y) ^ 2 =
              |Real.exp (-s) * ouSemigroup s (deriv g) y| ^ 2 := by rw [sq_abs]
          rw [h_eq]
          exact pow_le_pow_left₀ (abs_nonneg _) h_inner_abs 2
        calc (Real.exp (-s) * ouSemigroup s (deriv g) y) ^ 2 / ouSemigroup s g y
            ≤ M ^ 2 / ouSemigroup s g y :=
              div_le_div_of_nonneg_right h_inner_sq_le hPtg_pos.le
          _ ≤ M ^ 2 / ε := by
              apply div_le_div_of_nonneg_left (sq_nonneg _) hε hPtg_lo
      · -- Pointwise convergence of integrand at each y.
        filter_upwards with y
        -- exp(-s) → 1.
        have h_exp_lim : Tendsto (fun s : ℝ => Real.exp (-s)) (𝓝[Ici 0] 0) (𝓝 1) := by
          have h_cont : Continuous (fun s : ℝ => Real.exp (-s)) := by fun_prop
          have h := h_cont.continuousAt.tendsto (x := (0 : ℝ))
          have h_val : Real.exp (-(0 : ℝ)) = 1 := by simp
          rw [h_val] at h
          exact h.mono_left nhdsWithin_le_nhds
        -- exp(-s) * P_s(g')(y) → 1 * g'(y) = g'(y).
        have h_prod_lim : Tendsto (fun s => Real.exp (-s) * ouSemigroup s (deriv g) y)
            (𝓝[Ici 0] 0) (𝓝 (deriv g y)) := by
          have h := h_exp_lim.mul (h_Ptdg_tendsto y)
          simpa using h
        -- Square it.
        have h_sq_lim : Tendsto
            (fun s => (Real.exp (-s) * ouSemigroup s (deriv g) y) ^ 2)
            (𝓝[Ici 0] 0) (𝓝 ((deriv g y) ^ 2)) := by
          have h_cont_sq : ContinuousAt (fun u : ℝ => u ^ 2) (deriv g y) := by fun_prop
          exact h_cont_sq.tendsto.comp h_prod_lim
        -- P_s g (y) → g(y), and g(y) ≠ 0.
        have h_gy_ne : g y ≠ 0 := (h_gpos y).ne'
        have h_div_lim : Tendsto (fun s => H s y) (𝓝[Ici 0] 0)
            (𝓝 ((deriv g y) ^ 2 / g y)) := by
          have h := h_sq_lim.div (h_Ptg_tendsto y) h_gy_ne
          exact h
        exact h_div_lim
    -- Conclude.
    have h_eq_ev : ∀ᶠ s in 𝓝[Ici 0] 0,
        fisherInfo (ouSemigroup s g) = ∫ y, H s y ∂γ := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact h_rewrite_fisher s hs
    -- Use the eventual equality to transfer the tendsto.
    have h_target_eq : fisherInfo g = ∫ y, (deriv g y) ^ 2 / g y ∂γ := rfl
    rw [h_target_eq]
    refine h_tendsto_H.congr' ?_
    filter_upwards [h_eq_ev] with s hs_eq
    exact hs_eq.symm
  -- Apply hasDerivWithinAt_Ici_of_tendsto_deriv.
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
    (f := fun s => boltzmannEntropy (ouSemigroup s g))
    (e := -fisherInfo g) (a := 0) ?_ ?_ self_mem_nhdsWithin ?_
  · -- DifferentiableOn on Ioi 0.
    intro s hs
    have hs_pos : 0 < s := hs
    have h_deriv := hasDerivAt_entropy_ouSemigroup g hg hε hg_lo hg_hi hg'_bd hs_pos
    exact h_deriv.differentiableAt.differentiableWithinAt
  · -- ContinuousWithinAt at 0.
    have h_zero : ouSemigroup 0 g = g := by
      ext x
      simp only [ouSemigroup, neg_zero, Real.exp_zero, mul_zero, sub_self,
        Real.sqrt_zero, zero_mul, add_zero, one_mul]
      simp [integral_const]
    show ContinuousWithinAt (fun s => boltzmannEntropy (ouSemigroup s g)) (Ioi 0) 0
    have h_target : Tendsto (fun s => boltzmannEntropy (ouSemigroup s g))
        (𝓝[Ioi 0] 0) (𝓝 (boltzmannEntropy (ouSemigroup 0 g))) := by
      rw [h_zero]
      exact h_entropy_tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact h_target
  · -- Tendsto of deriv to -fisherInfo g.
    -- For s > 0: deriv (...) s = -fisherInfo (P_s g).
    have h_deriv_eq : ∀ s, 0 < s →
        deriv (fun s => boltzmannEntropy (ouSemigroup s g)) s =
          -fisherInfo (ouSemigroup s g) := by
      intro s hs
      exact (hasDerivAt_entropy_ouSemigroup g hg hε hg_lo hg_hi hg'_bd hs).deriv
    have h_fisher_neg_tendsto :
        Tendsto (fun s => -fisherInfo (ouSemigroup s g))
          (𝓝[Ici 0] 0) (𝓝 (-fisherInfo g)) := h_fisher_tendsto.neg
    have h_fisher_neg_tendsto' :
        Tendsto (fun s => -fisherInfo (ouSemigroup s g))
          (𝓝[Ioi 0] 0) (𝓝 (-fisherInfo g)) :=
      h_fisher_neg_tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    refine h_fisher_neg_tendsto'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (h_deriv_eq s hs).symm

end Gaussian1D

end
