/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Ornstein–Uhlenbeck generator (named)

G1 of the Gross-discharge plan (`plans/gross-discharge.md`). The OU
generator `L f = Δf − x·∇f` is currently only written *inline* in
`EuclideanStein.lean` (`hasDerivAt_t_ouSemigroup`,
`gaussian_dirichlet_form_bilinear`); it is defined nowhere in
markov-semigroups, gaussian-field, or the catalogs (verified
2026-05-16). This file names it (1D + nD) and restates the two proved
1D facts in terms of the named operator, so G2 (strong-L² generator
limit) and G4 (generator↔energy IBP, nD lift) become rewrites rather
than re-derivations.

`EuclideanFin` already imports `EuclideanStein`, so importing it alone
brings both `Gaussian1D` and `GaussianFin`.

## Main definitions

- `Gaussian1D.ouGenerator1D` — `L g = g'' − x·g'` on `ℝ`
- `GaussianFin.ouGeneratorFin` — `L f = Δf − x·∇f` on `Fin n → ℝ`

## Main results

- `Gaussian1D.hasDerivAt_t_ouSemigroup'` — heat equation, named form
- `Gaussian1D.gaussian_generator_ibp` — generator↔energy IBP, named form
-/

import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanFin

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Gaussian1D

/-- The one-dimensional Ornstein–Uhlenbeck generator `L g = g'' − x·g'`
(the operator written inline in `hasDerivAt_t_ouSemigroup` and
`gaussian_dirichlet_form_bilinear`). -/
def ouGenerator1D (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (deriv g) x - x * deriv g x

@[simp] theorem ouGenerator1D_apply (g : ℝ → ℝ) (x : ℝ) :
    ouGenerator1D g x = deriv (deriv g) x - x * deriv g x := rfl

/-- Heat equation for the OU semigroup, stated with the named
generator: for `t₀ > 0` and core `f`, `τ ↦ P_τ f x` is differentiable
at `t₀` with derivative `(L (P_{t₀} f)) x`. Restates the proved
`hasDerivAt_t_ouSemigroup`. -/
theorem hasDerivAt_t_ouSemigroup' (t₀ : ℝ) (ht₀ : 0 < t₀)
    {f : ℝ → ℝ} (hf : IsCore f) (x : ℝ) :
    HasDerivAt (fun τ => ouSemigroup τ f x)
      (ouGenerator1D (ouSemigroup t₀ f) x) t₀ := by
  simpa only [ouGenerator1D_apply] using hasDerivAt_t_ouSemigroup t₀ ht₀ hf x

/-- Gaussian integration-by-parts / generator–energy identity, stated
with the named generator: `∫ f · (L h) dγ = -∫ f' · h' dγ`. Restates
the proved `gaussian_dirichlet_form_bilinear`. -/
theorem gaussian_generator_ibp
    {f h : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {Mf : ℝ}
    (hf_bd : ∀ y, |f y| ≤ Mf) (hf'_bd : ∀ y, |deriv f y| ≤ Mf)
    (hh : ContDiff ℝ 2 h) {Mh Mh' Mh'' : ℝ}
    (hh_bd : ∀ y, |h y| ≤ Mh) (hh'_bd : ∀ y, |deriv h y| ≤ Mh')
    (hh''_bd : ∀ y, |deriv (deriv h) y| ≤ Mh'') :
    ∫ y, f y * ouGenerator1D h y ∂γ = -∫ y, deriv f y * deriv h y ∂γ := by
  simpa only [ouGenerator1D_apply] using
    gaussian_dirichlet_form_bilinear hf hf_bd hf'_bd hh hh_bd hh'_bd hh''_bd

end Gaussian1D

namespace GaussianFin

variable {n : ℕ}

/-- The `n`-dimensional Ornstein–Uhlenbeck generator
`L f = Δf − x·∇f = ∑ᵢ ∂ᵢ²f − ∑ᵢ xᵢ ∂ᵢf`, built from the
`secondPartial`/`partialDeriv` primitives (same convention as
`ouGammaFin`). -/
def ouGeneratorFin (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => (∑ i : Fin n, secondPartial i f x) - ∑ i : Fin n, x i * partialDeriv i f x

@[simp] theorem ouGeneratorFin_apply (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ouGeneratorFin f x =
      (∑ i : Fin n, secondPartial i f x) - ∑ i : Fin n, x i * partialDeriv i f x :=
  rfl

end GaussianFin

end
