/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Carré du Champ and Bakry-Émery Spaces

Layer 2 of the abstraction hierarchy. A `BakryEmerySpace` extends a
`DirichletSpace` with a carré du champ operator Γ (abstract "squared
gradient") and a curvature lower bound ρ > 0.

No manifold or metric is assumed. On a Riemannian manifold (M, g) with
generator L = Δ - ∇U · ∇:
  Γ(f, g) = ⟨∇f, ∇g⟩_g
  Γ₂(f, f) = ‖Hess f‖² + (Ric + Hess U)(∇f, ∇f)
  curvature ρ ↔ Ric + Hess U ≥ ρ g

But the abstract definition works for any diffusion generator where Γ
and Γ₂ make sense.

## Main definitions

- `BakryEmerySpace` — DirichletSpace + Γ + curvature bound

## Main theorems (proved)

- `BakryEmerySpace.satisfiesPoincare` — curvature ρ ⟹ Poincaré(ρ)
- `BakryEmerySpace.variance_decay` — Var(P_t f) ≤ e^{-2ρt} Var(f)

## References

- Bakry and Émery, "Diffusions hypercontractives," Séminaire de
  probabilités XIX, Springer LNM 1123 (1985), 177–206
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 1, 3, and 5
-/

import AcceleratedLogConcave.External.MarkovSemigroups.Abstract.DirichletForm
import Mathlib.Analysis.ODE.Gronwall

open MeasureTheory Filter Set

noncomputable section

/-- A Bakry-Émery space: a Dirichlet space equipped with a carré du
champ operator Γ and a curvature lower bound ρ > 0.

The carré du champ Γ(f, g)(x) is the abstract "pointwise squared
gradient." It satisfies:
- E(f, g) = ∫ Γ(f, g) dμ  (energy = integral of Γ)
- Γ(f, f) ≥ 0  (nonneg)
- Γ(fg, h) = f Γ(g, h) + g Γ(f, h)  (Leibniz / diffusion property)

The curvature condition Γ₂(f, f) ≥ ρ Γ(f, f) (where Γ₂ is defined
from Γ and the generator) implies both the Poincaré inequality and the
log-Sobolev inequality with constant ρ. This is the Bakry-Émery
criterion.

On ℝⁿ with standard Gaussian: Γ(f, g) = ⟨∇f, ∇g⟩, ρ = 1.
On T^d with GFF (mass m): Γ(f, g) = ⟨∇f, ∇g⟩, ρ = m².
On a finite graph: Γ(f, f)(x) = ½ Σ_{y~x} (f(y) - f(x))², ρ depends
on the graph. -/
class BakryEmerySpace (X : Type*) [MeasurableSpace X]
    extends DirichletSpace X where
  /-- Carré du champ: abstract pointwise "squared gradient." -/
  Γ : (X → ℝ) → (X → ℝ) → (X → ℝ)
  /-- Γ is symmetric. -/
  Γ_symm : ∀ f g, Γ f g = Γ g f
  /-- Γ is nonneg on the diagonal. -/
  Γ_nonneg : ∀ f x, 0 ≤ Γ f f x
  /-- Energy is the integral of Γ. -/
  energy_eq_integral_Γ : ∀ f g, energy f g = ∫ x, Γ f g x ∂μ
  /-- Core is closed under products. -/
  IsCore_mul : ∀ {f g}, IsCore f → IsCore g → IsCore (f * g)
  /-- Leibniz rule (diffusion property):
    Γ(fg, h) = f · Γ(g, h) + g · Γ(f, h) -/
  Γ_leibniz : ∀ f g h, IsCore f → IsCore g → IsCore h → ∀ x,
    Γ (f * g) h x = f x * Γ g h x + g x * Γ f h x
  /-- Γ of a constant is zero. -/
  Γ_const : ∀ (c : ℝ) f, Γ (fun _ => c) f = 0
  /-- The associated Markov semigroup P_t. -/
  semigroup : ℝ → (X → ℝ) → (X → ℝ)
  /-- Core is preserved by the semigroup. -/
  IsCore_semigroup : ∀ (t : ℝ), 0 ≤ t → ∀ {f}, IsCore f → IsCore (semigroup t f)
  /-- Curvature lower bound ρ > 0. -/
  ρ : ℝ
  hρ : 0 < ρ
  /-- The Bakry-Émery curvature condition (semigroup form):
    ∫ Γ(P_t f, P_t f) dμ ≤ e^{-2ρt} ∫ Γ(f, f) dμ -/
  gradient_decay : ∀ (f : X → ℝ) (t : ℝ), 0 ≤ t → IsCore f →
    ∫ x, Γ (semigroup t f) (semigroup t f) x ∂μ ≤
    Real.exp (-2 * ρ * t) * ∫ x, Γ f f x ∂μ
  /-- P_0 = id. -/
  semigroup_zero : ∀ f, semigroup 0 f = f
  /-- Semigroup property: P_{s+t} = P_s ∘ P_t.

  The `IsCore f` hypothesis ensures `f` is integrable against the
  semigroup's invariant measure on every kernel; without it the
  Mehler-style integrals can diverge and Lean's `integral`-returns-0
  default desyncs the two sides. All concrete instances we use only
  ever apply the semigroup to `IsCore` test functions. -/
  semigroup_add : ∀ s t f, 0 ≤ s → 0 ≤ t → IsCore f →
    semigroup (s + t) f = semigroup s (semigroup t f)
  /-- P_t is a contraction on L²(μ). -/
  semigroup_contraction : ∀ (f : X → ℝ) (t : ℝ), 0 ≤ t → IsCore f →
    ∫ x, (semigroup t f x) ^ 2 ∂μ ≤ ∫ x, (f x) ^ 2 ∂μ
  /-- P_t preserves the mean. -/
  semigroup_mean : ∀ (f : X → ℝ) (t : ℝ), 0 ≤ t → IsCore f →
    ∫ x, semigroup t f x ∂μ = ∫ x, f x ∂μ
  /-- P_t is self-adjoint on L²(μ). -/
  semigroup_selfAdjoint : ∀ (f g : X → ℝ) (t : ℝ), 0 ≤ t → IsCore f → IsCore g →
    ∫ x, semigroup t f x * g x ∂μ = ∫ x, f x * semigroup t g x ∂μ
  /-- Integrated gradient decay on L² norms:
    ∫f² - ∫(P_t f)² ≤ (1-e^{-2ρt})/ρ · E(f).
  Reference: BGL §4.7, integrated Proposition 4.7.1. -/
  semigroup_l2_decay_bound : ∀ (f : X → ℝ) (t : ℝ), 0 ≤ t → IsCore f →
    ∫ x, (f x) ^ 2 ∂μ - ∫ x, (semigroup t f x) ^ 2 ∂μ ≤
    (1 - Real.exp (-2 * ρ * t)) / ρ * energy f f
  /-- d/dt ∫(P_t f)² = -2 E(P_t f) (generator theory).
  Reference: BGL Proposition 4.7.1. -/
  semigroup_l2_sq_hasDerivWithinAt : ∀ (f : X → ℝ) (t : ℝ), 0 ≤ t → IsCore f →
    HasDerivWithinAt (fun s => ∫ x, (semigroup s f x) ^ 2 ∂μ)
                     (-2 * ∫ x, Γ (semigroup t f) (semigroup t f) x ∂μ)
                     (Ici 0) t
  /-- Ergodicity: Var(P_t f) → 0 as t → ∞.
  Reference: BGL Proposition 4.2.1. -/
  semigroup_ergodic : ∀ (f : X → ℝ), IsCore f →
    Tendsto (fun t => ∫ x, (semigroup t f x) ^ 2 ∂μ - (∫ x, f x ∂μ) ^ 2)
            atTop (nhds 0)
  /-- Integrated entropy decay for f²: the entropy decrease of P_t(f²)
  is bounded by the time-integrated Fisher information decay.

  This follows from d/dt Ent(P_t g) = -I(P_t g) (entropy derivative)
  combined with Fisher information gradient decay I(P_t g) ≤ e^{-2ρt} I(g)
  integrated from 0 to t. For g = f², I(f²) = 4 E(f,f) by the Leibniz
  rule for Γ, giving the factor 2/ρ.

  Reference: BGL §5.5, proof of Theorem 5.5.2. -/
  semigroup_entropy_sq_decay_bound : ∀ (f : X → ℝ) (t : ℝ), 0 ≤ t → IsCore f →
    DirichletSpace.entropy (ds := toDirichletSpace) (fun x => f x * f x) -
    DirichletSpace.entropy (ds := toDirichletSpace)
      (semigroup t (fun x => f x * f x)) ≤
    (1 - Real.exp (-2 * ρ * t)) * (2 / ρ) * energy f f
  /-- Entropy ergodicity: Ent(P_t(f²)) → 0 as t → ∞.
  Equivalently, P_t(f²) → ∫f² dμ in entropy.
  Reference: BGL Proposition 5.2.1. -/
  semigroup_entropy_sq_ergodic : ∀ (f : X → ℝ), IsCore f →
    Tendsto (fun t => DirichletSpace.entropy (ds := toDirichletSpace)
      (semigroup t (fun x => f x * f x))) atTop (nhds 0)

/-! ## Proved theorems -/

namespace BakryEmerySpace

variable {X : Type*} [MeasurableSpace X] [be : BakryEmerySpace X]

/-- Var(P_t f) = ∫(P_t f)² - (∫ f)² (mean preservation). -/
private theorem variance_semigroup_eq (f : X → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : be.IsCore f) :
    DirichletSpace.variance (ds := be.toDirichletSpace) (be.semigroup t f) =
    ∫ x, (be.semigroup t f x) ^ 2 ∂be.μ - (∫ x, f x ∂be.μ) ^ 2 := by
  unfold DirichletSpace.variance; rw [be.semigroup_mean f t ht hf]

/-- Var(f) ≤ (1/ρ) E(f) + Var(P_T f) for any T ≥ 0. -/
private theorem variance_le_energy_plus_tail (f : X → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hf : be.IsCore f) :
    DirichletSpace.variance (ds := be.toDirichletSpace) f ≤
    1 / be.ρ * be.energy f f +
    DirichletSpace.variance (ds := be.toDirichletSpace) (be.semigroup T f) := by
  have hvar_split : DirichletSpace.variance (ds := be.toDirichletSpace) f =
      (∫ x, (f x) ^ 2 ∂be.μ - ∫ x, (be.semigroup T f x) ^ 2 ∂be.μ) +
      DirichletSpace.variance (ds := be.toDirichletSpace) (be.semigroup T f) := by
    unfold DirichletSpace.variance; rw [be.semigroup_mean f T hT hf]; ring
  have hbound := be.semigroup_l2_decay_bound f T hT hf
  have h_factor_le : (1 - Real.exp (-2 * be.ρ * T)) / be.ρ ≤ 1 / be.ρ := by
    apply div_le_div_of_nonneg_right _ (le_of_lt be.hρ)
    linarith [Real.exp_nonneg (-2 * be.ρ * T)]
  linarith [mul_le_mul_of_nonneg_right h_factor_le (be.energy_nonneg f)]

/-- **Bakry-Émery Poincaré (BGL Thm 4.8.4).** PROVED.

Var(f) ≤ (1/ρ) E(f): for all T, Var(f) ≤ (1/ρ) E(f) + Var(P_T f),
and ergodicity gives Var(P_T f) → 0. -/
theorem satisfiesPoincare :
    DirichletSpace.SatisfiesPoincare (ds := be.toDirichletSpace) be.ρ := by
  refine ⟨be.hρ, fun f hf => ?_⟩
  -- Proof by contradiction: if Var(f) > (1/ρ)E(f), then ε > 0 but
  -- Var(f) ≤ (1/ρ)E(f) + Var(P_T f) < (1/ρ)E(f) + ε = Var(f). Contradiction.
  by_contra h
  push Not at h
  set ε := DirichletSpace.variance (ds := be.toDirichletSpace) f -
            1 / be.ρ * be.energy f f
  have hε_pos : 0 < ε := by linarith
  -- Ergodicity: Var(P_T f) → 0, so ∃ T with |Var(P_T f)| < ε
  have hergodic := be.semigroup_ergodic f hf
  rw [Metric.tendsto_atTop] at hergodic
  obtain ⟨T, hT_spec⟩ := hergodic ε hε_pos
  set T' := max T 0
  have hT'_nn : 0 ≤ T' := le_max_right T 0
  have h_dist := hT_spec T' (le_max_left T 0)
  rw [Real.dist_eq] at h_dist
  have hvar_small : DirichletSpace.variance (ds := be.toDirichletSpace)
      (be.semigroup T' f) < ε := by
    rw [variance_semigroup_eq f T' hT'_nn hf]
    have := (abs_lt.mp h_dist).2
    linarith
  linarith [variance_le_energy_plus_tail f T' hT'_nn hf]

/-- Ent(f²) ≤ (2/ρ) E(f) + Ent(P_T(f²)) for any T ≥ 0. -/
private theorem entropy_le_energy_plus_tail (f : X → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hf : be.IsCore f) :
    DirichletSpace.entropy (ds := be.toDirichletSpace) (fun x => f x * f x) ≤
    2 / be.ρ * be.energy f f +
    DirichletSpace.entropy (ds := be.toDirichletSpace)
      (be.semigroup T (fun x => f x * f x)) := by
  have hbound := be.semigroup_entropy_sq_decay_bound f T hT hf
  have h_factor_le : (1 - Real.exp (-2 * be.ρ * T)) ≤ 1 :=
    sub_le_self _ (Real.exp_nonneg _)
  have h_energy_nn := be.energy_nonneg f
  have hρ_pos := be.hρ
  have h_coeff_nn : 0 ≤ 2 / be.ρ := div_nonneg (by norm_num) (le_of_lt hρ_pos)
  nlinarith [mul_le_mul_of_nonneg_right h_factor_le (mul_nonneg h_coeff_nn h_energy_nn)]

/-- **Bakry-Émery log-Sobolev (BGL Thm 5.5.2).** PROVED.

Ent(f²) ≤ (2/ρ) E(f): for all T, Ent(f²) ≤ (2/ρ) E(f) + Ent(P_T(f²)),
and entropy ergodicity gives Ent(P_T(f²)) → 0. -/
theorem satisfiesLogSobolev :
    DirichletSpace.SatisfiesLogSobolev (ds := be.toDirichletSpace) be.ρ := by
  refine ⟨be.hρ, fun f hf => ?_⟩
  by_contra h
  push Not at h
  set ε := DirichletSpace.entropy (ds := be.toDirichletSpace) (fun x => f x * f x) -
            2 / be.ρ * be.energy f f
  have hε_pos : 0 < ε := by linarith
  have hff_core : be.IsCore (fun x => f x * f x) := by
    have : (fun x => f x * f x) = f * f := by ext x; rfl
    rw [this]
    exact be.IsCore_mul hf hf
  have hergodic := be.semigroup_entropy_sq_ergodic f hf
  rw [Metric.tendsto_atTop] at hergodic
  obtain ⟨T, hT_spec⟩ := hergodic ε hε_pos
  set T' := max T 0
  have hT'_nn : 0 ≤ T' := le_max_right T 0
  have h_dist := hT_spec T' (le_max_left T 0)
  rw [Real.dist_eq] at h_dist
  have hent_small : DirichletSpace.entropy (ds := be.toDirichletSpace)
      (be.semigroup T' (fun x => f x * f x)) < ε := by
    have := (abs_lt.mp h_dist).2; linarith
  linarith [entropy_le_energy_plus_tail f T' hT'_nn hf]

/-- HasDerivWithinAt for the variance function on Ici 0. -/
private theorem variance_hasDerivWithinAt (f : X → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : be.IsCore f) :
    HasDerivWithinAt
      (fun s => DirichletSpace.variance (ds := be.toDirichletSpace) (be.semigroup s f))
      (-2 * ∫ x, be.Γ (be.semigroup t f) (be.semigroup t f) x ∂be.μ)
      (Ici 0) t := by
  have heq : EqOn (fun s => DirichletSpace.variance (ds := be.toDirichletSpace)
      (be.semigroup s f))
      (fun s => ∫ x, (be.semigroup s f x) ^ 2 ∂be.μ - (∫ x, f x ∂be.μ) ^ 2) (Ici 0) :=
    fun s hs => variance_semigroup_eq f s hs hf
  exact HasDerivWithinAt.congr
    ((be.semigroup_l2_sq_hasDerivWithinAt f t ht hf).sub_const _)
    heq (variance_semigroup_eq f t ht hf)

/-- **Bakry-Émery variance decay (BGL Prop 4.8.1).** PROVED.

Var(P_t f) ≤ e^{-2ρt} Var(f) via Grönwall:
  d/dt Var(P_t f) = -2 E(P_t f) ≤ -2ρ Var(P_t f) (by Poincaré). -/
theorem variance_decay (f : X → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : be.IsCore f) :
    DirichletSpace.variance (ds := be.toDirichletSpace) (be.semigroup t f) ≤
    Real.exp (-2 * be.ρ * t) *
    DirichletSpace.variance (ds := be.toDirichletSpace) f := by
  set φ := fun s => DirichletSpace.variance (ds := be.toDirichletSpace)
    (be.semigroup s f)
  set φ' := fun s => -2 * ∫ x, be.Γ (be.semigroup s f) (be.semigroup s f) x ∂be.μ
  -- Apply Grönwall: φ(t) ≤ gronwallBound (φ 0) (-2ρ) 0 (t - 0)
  suffices h : φ t ≤ gronwallBound (φ 0) (-2 * be.ρ) 0 (t - 0) by
    rw [gronwallBound_ε0, sub_zero] at h
    simp only [φ, be.semigroup_zero] at h
    linarith
  apply le_gronwallBound_of_liminf_deriv_right_le (a := 0) (b := t) (f' := φ')
  -- 1. ContinuousOn φ (Icc 0 t)
  · intro s hs
    exact ((variance_hasDerivWithinAt f s (Icc_subset_Ici_self hs) hf).mono
      Icc_subset_Ici_self).continuousWithinAt
  -- 2. Liminf right derivative condition from HasDerivWithinAt
  · intro s hs r hr
    -- HasDerivWithinAt on Ici 0, restrict to Ici s (since s ≥ 0)
    have hd := (variance_hasDerivWithinAt f s hs.1 hf).mono (Ici_subset_Ici.mpr hs.1)
    -- liminf_right_slope_le gives: slope φ s z < r frequently
    have hslope := hd.liminf_right_slope_le hr
    -- slope for ℝ → ℝ is (f z - f x) / (z - x) = (z - x)⁻¹ * (f z - f x)
    exact hslope.mono fun z hz => by
      rwa [slope_def_field, div_eq_inv_mul] at hz
  -- 3. Initial condition: φ(0) ≤ φ(0)
  · exact le_refl _
  -- 4. Bound: φ'(s) ≤ -2ρ φ(s) + 0 (by Poincaré)
  · intro s hs; rw [add_zero]; simp only [φ, φ']
    have hs_core : be.IsCore (be.semigroup s f) := be.IsCore_semigroup s hs.1 hf
    have hP := satisfiesPoincare.2 (be.semigroup s f) hs_core
    rw [be.energy_eq_integral_Γ] at hP
    -- hP: variance ≤ (1/ρ) * ∫Γ, so ρ * variance ≤ ∫Γ
    have hρ_pos := be.hρ
    have hP' : be.ρ * DirichletSpace.variance (ds := be.toDirichletSpace)
        (be.semigroup s f) ≤
        ∫ x, be.Γ (be.semigroup s f) (be.semigroup s f) x ∂be.μ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hρ_pos] at hP
      linarith [mul_comm (DirichletSpace.variance (ds := be.toDirichletSpace)
        (be.semigroup s f)) be.ρ]
    nlinarith
  -- 5. Endpoint t ∈ Icc 0 t
  · exact right_mem_Icc.mpr ht

end BakryEmerySpace

end
