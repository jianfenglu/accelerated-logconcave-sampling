/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hypercontractivity and the Gross Equivalence

A *symmetric Markov semigroup* `P_t` on a probability space is
hypercontractive if it maps `L^p → L^q` for suitable `(p, q, t)`. Nelson
(1973) proved this for the OU semigroup; Gross (1975) showed the
equivalence with the log-Sobolev inequality.

## Main definitions

- `MarkovSemigroup` — a symmetric Markov semigroup on a probability
  space, carried by bounded linear operators on `L²(μ)`
  (`Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`).
- `DirichletMarkovSemigroup` — bundles a `MarkovSemigroup` with the
  semigroup's canonical Dirichlet form (the user supplies the form
  data plus the right-derivative-at-zero compatibility on a core
  algebra).
- `MarkovSemigroup.IsHypercontractive` — `‖P_t f‖_{L^q} ≤ ‖f‖_{L^p}`
  when `q ≤ 1 + (p − 1) e^{2ρt}`, formulated with an `L²` source plus
  an explicit `MemLp` hypothesis for the input `L^p` exponent.

## Local port boundary

The three unused upstream abstract postulates and their three wrapper
theorems are omitted. The concrete Gaussian result imports the proved
GrossODE route; no generic Gross equivalence is asserted in this port.

## Why bundle?

The form-vs-semigroup link `E(f, g) = -(d/dt)|_{t=0+} ⟨[f], P_t [g]⟩` is
essential for Gross. Without it the two are unrelated and Gross's
theorem has no content. Bundling them into a single structure
(`DirichletMarkovSemigroup`) makes the link a structural invariant
rather than a side hypothesis.

The semigroup is the *primary* datum: for symmetric Markov semigroups,
the Dirichlet form is canonically determined (Fukushima–Oshima–Takeda
construction). The user-supplied `energy`/`IsCore` fields are a
certified presentation of that canonical form on a chosen core
algebra.

## References

- Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973)
- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975)
- Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, §1.3-1.4 and §5.2
- Fukushima-Oshima-Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, de Gruyter, 1994, §1.3
- Simon, *The P(φ)₂ Euclidean QFT*, Princeton, 1974, Ch. I
-/

/- Port history note: inherited comments describing placeholders or legacy
postulates refer to earlier upstream development stages. Local proof status
is determined by the compiled axiom audit and the accompanying port note. -/

import AcceleratedLogConcave.External.MarkovSemigroups.Abstract.DirichletForm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ENNReal Set
open scoped ENNReal InnerProductSpace

noncomputable section

/-- A *symmetric Markov semigroup* on a probability space `(X, μ)`.

This is the standard setup for Gross's LSI/HC equivalence: a strongly
continuous *symmetric* contraction semigroup on `L²(μ)` preserving
positivity and any a.e.-constant-`1` element.

Time parameter `t : ℝ` is conventionally only meaningful for `t ≥ 0` —
all properties below are stated under that condition. Restricting to
`t ≥ 0` (rather than allowing all of `ℝ`) avoids the trap where a
two-sided contraction semigroup is forced by Stone's theorem to be a
group of isometries with skew-adjoint generator, incompatible with the
self-adjointness implied by symmetry. -/
structure MarkovSemigroup (X : Type*) [MeasurableSpace X] where
  /-- Reference probability measure. -/
  μ : Measure X
  /-- The measure is a probability measure. -/
  hμ : IsProbabilityMeasure μ
  /-- Bounded linear operator on `L²(μ)` at each time `t`. -/
  P : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  /-- `P 0 = id`. -/
  P_zero : P 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)
  /-- Semigroup property (for `s, t ≥ 0`). -/
  P_semigroup : ∀ s t, 0 ≤ s → 0 ≤ t → P (s + t) = (P s).comp (P t)
  /-- Strong continuity at `t = 0+`. -/
  P_strong_cont : ∀ f : Lp ℝ 2 μ,
    Filter.Tendsto (fun t : ℝ => P t f) (nhdsWithin 0 (Set.Ici 0)) (nhds f)
  /-- Operator-norm contraction on `L²(μ)`. -/
  P_contraction : ∀ t, 0 ≤ t → ‖P t‖ ≤ 1
  /-- Markov property: `P_t` fixes any a.e.-constant-`1` element of `L²(μ)`. -/
  P_conservation : ∀ t, 0 ≤ t → ∀ f : Lp ℝ 2 μ,
    (∀ᵐ x ∂μ, (f : X → ℝ) x = 1) → P t f = f
  /-- Positivity preservation on `L²(μ)`. -/
  P_positivity : ∀ t, 0 ≤ t → ∀ f : Lp ℝ 2 μ, 0 ≤ f → 0 ≤ P t f
  /-- Symmetry of `P_t` on `L²(μ)`. -/
  P_symmetric : ∀ t, 0 ≤ t → ∀ f g : Lp ℝ 2 μ,
    ⟪f, P t g⟫_ℝ = ⟪P t f, g⟫_ℝ

attribute [instance] MarkovSemigroup.hμ

namespace MarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- Each `P_t` is self-adjoint on `L²(μ)` by the symmetry field. -/
lemma isSelfAdjoint (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t) :
    IsSelfAdjoint (S.P t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  simpa using (S.P_symmetric t ht f g).symm

/-- **L^∞-contraction.** For a symmetric Markov semigroup with conservation
of constants (i.e., `P_t 1 = 1`), if `|f y| ≤ M` a.e. then
`|(P_t f) y| ≤ M` a.e. Standard textbook fact derivable purely from the
existing `MarkovSemigroup` fields (no extra hypothesis needed): the trick
is `0 ≤ Lp.const M - f` (a.e. from the bound) + `P_positivity` +
`P_conservation` (used to deduce `P_t (Lp.const M) = Lp.const M` via
`Lp.const M = M • Lp.const 1`). -/
lemma Linfty_contraction (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 S.μ} {M : ℝ}
    (hf : ∀ᵐ y ∂S.μ, |(f : X → ℝ) y| ≤ M) :
    ∀ᵐ y ∂S.μ, |(S.P t f : X → ℝ) y| ≤ M := by
  have : IsFiniteMeasure S.μ := inferInstance
  set Mlp : Lp ℝ 2 S.μ := Lp.const 2 S.μ M with hMlp_def
  have hMlp_coe : (Mlp : X → ℝ) =ᵐ[S.μ] fun _ => M := Lp.coeFn_const 2 S.μ M
  -- Conservation: P_t (Lp.const 1) = Lp.const 1.
  have hPt_const1 : S.P t (Lp.const 2 S.μ (1:ℝ)) = Lp.const 2 S.μ (1:ℝ) := by
    refine S.P_conservation t ht _ ?_
    filter_upwards [Lp.coeFn_const 2 S.μ (1:ℝ)] with x hx
    exact hx
  -- Lp.const M = M • Lp.const 1 (Lp identifies a.e. equal functions).
  have hMlp_smul : Mlp = M • Lp.const 2 S.μ (1:ℝ) := by
    refine Lp.ext ?_
    filter_upwards [hMlp_coe, Lp.coeFn_smul M (Lp.const 2 S.μ (1:ℝ)),
                    Lp.coeFn_const 2 S.μ (1:ℝ)] with y h1 h2 _
    simp [h1, h2]
  -- Hence P_t (Lp.const M) = Lp.const M.
  have hPt_Mlp : S.P t Mlp = Mlp := by
    calc S.P t Mlp
        = S.P t (M • Lp.const 2 S.μ (1:ℝ)) := by rw [hMlp_smul]
      _ = M • S.P t (Lp.const 2 S.μ (1:ℝ)) := (S.P t).map_smul M _
      _ = M • Lp.const 2 S.μ (1:ℝ) := by rw [hPt_const1]
      _ = Mlp := hMlp_smul.symm
  -- Upper bound: P_t f ≤ M pointwise a.e. via 0 ≤ Mlp - f in Lp.
  have h_upper : ∀ᵐ y ∂S.μ, (S.P t f : X → ℝ) y ≤ M := by
    -- The a.e.-pointwise nonneg of ↑↑(Mlp - f), via Lp.coeFn_sub bridge.
    have h_diff_ae : 0 ≤ᵐ[S.μ] (↑↑(Mlp - f) : X → ℝ) := by
      filter_upwards [hf, hMlp_coe, Lp.coeFn_sub Mlp f] with y hy hMy hSubY
      have : (↑↑(Mlp - f) : X → ℝ) y = M - (f : X → ℝ) y := by
        rw [hSubY]; simp [hMy]
      rw [Pi.zero_apply, this]
      linarith [le_of_abs_le hy]
    have h_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ Mlp - f := (Lp.coeFn_nonneg _).mp h_diff_ae
    have h_pt_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ S.P t (Mlp - f) :=
      S.P_positivity t ht _ h_diff_nn
    have h_pt_orbit_sub : S.P t (Mlp - f) = Mlp - S.P t f := by
      rw [map_sub, hPt_Mlp]
    rw [h_pt_orbit_sub] at h_pt_diff_nn
    have h_ae := (Lp.coeFn_nonneg _).mpr h_pt_diff_nn
    filter_upwards [h_ae, Lp.coeFn_sub Mlp (S.P t f), hMlp_coe] with y hy hSub hMy
    have h_pt : (↑↑(Mlp - S.P t f) : X → ℝ) y = M - (S.P t f : X → ℝ) y := by
      rw [hSub]; simp [hMy]
    rw [Pi.zero_apply, h_pt] at hy
    linarith
  -- Lower bound: -M ≤ P_t f pointwise a.e. via 0 ≤ Mlp + f in Lp.
  have h_lower : ∀ᵐ y ∂S.μ, (-M : ℝ) ≤ (S.P t f : X → ℝ) y := by
    have h_sum_ae : 0 ≤ᵐ[S.μ] (↑↑(Mlp + f) : X → ℝ) := by
      filter_upwards [hf, hMlp_coe, Lp.coeFn_add Mlp f] with y hy hMy hAddY
      have : (↑↑(Mlp + f) : X → ℝ) y = M + (f : X → ℝ) y := by
        rw [hAddY]; simp [hMy]
      rw [Pi.zero_apply, this]
      linarith [neg_le_of_abs_le hy]
    have h_sum_nn : (0 : Lp ℝ 2 S.μ) ≤ Mlp + f := (Lp.coeFn_nonneg _).mp h_sum_ae
    have h_pt_sum_nn : (0 : Lp ℝ 2 S.μ) ≤ S.P t (Mlp + f) :=
      S.P_positivity t ht _ h_sum_nn
    have h_pt_orbit_add : S.P t (Mlp + f) = Mlp + S.P t f := by
      rw [map_add, hPt_Mlp]
    rw [h_pt_orbit_add] at h_pt_sum_nn
    have h_ae := (Lp.coeFn_nonneg _).mpr h_pt_sum_nn
    filter_upwards [h_ae, Lp.coeFn_add Mlp (S.P t f), hMlp_coe] with y hy hAdd hMy
    have h_pt : (↑↑(Mlp + S.P t f) : X → ℝ) y = M + (S.P t f : X → ℝ) y := by
      rw [hAdd]; simp [hMy]
    rw [Pi.zero_apply, h_pt] at hy
    linarith
  filter_upwards [h_upper, h_lower] with y hyu hyl
  exact abs_le.mpr ⟨hyl, hyu⟩

/-- **L^∞ orbit ⇒ all L^p memberships.** Companion to `Linfty_contraction`:
once the orbit is uniformly bounded a.e., it lies in every `MemLp p` on
the finite measure `S.μ`. -/
lemma orbit_memLp (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 S.μ} {M : ℝ}
    (hf : ∀ᵐ y ∂S.μ, |(f : X → ℝ) y| ≤ M) (p : ℝ≥0∞) :
    MemLp ((S.P t f : X → ℝ)) p S.μ := by
  have : IsFiniteMeasure S.μ := inferInstance
  refine MemLp.of_bound (Lp.aestronglyMeasurable _) M ?_
  filter_upwards [S.Linfty_contraction ht hf] with y hy
  simpa using hy

/-- **Lower-bound contraction.** Companion to `Linfty_contraction`: if
`f ≥ ε` a.e., then `(P_t f) ≥ ε` a.e. (for `t ≥ 0`). Same template:
`0 ≤ f - Lp.const ε` (a.e.) + `P_positivity` + `P_t (Lp.const ε) = Lp.const ε`
(via conservation + scalar). The dual of `Linfty_contraction`, but stated
in *one-sided* form because Gross-style positivity arguments only need
the lower bound `(P_s f) ≥ ε`, not |·| ≤ M. -/
lemma orbit_lower_bound (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 S.μ} {ε : ℝ}
    (hf : ∀ᵐ y ∂S.μ, ε ≤ (f : X → ℝ) y) :
    ∀ᵐ y ∂S.μ, ε ≤ (S.P t f : X → ℝ) y := by
  have : IsFiniteMeasure S.μ := inferInstance
  set εlp : Lp ℝ 2 S.μ := Lp.const 2 S.μ ε with hεlp_def
  have hεlp_coe : (εlp : X → ℝ) =ᵐ[S.μ] fun _ => ε := Lp.coeFn_const 2 S.μ ε
  have hPt_const1 : S.P t (Lp.const 2 S.μ (1:ℝ)) = Lp.const 2 S.μ (1:ℝ) := by
    refine S.P_conservation t ht _ ?_
    filter_upwards [Lp.coeFn_const 2 S.μ (1:ℝ)] with x hx
    exact hx
  have hεlp_smul : εlp = ε • Lp.const 2 S.μ (1:ℝ) := by
    refine Lp.ext ?_
    filter_upwards [hεlp_coe, Lp.coeFn_smul ε (Lp.const 2 S.μ (1:ℝ)),
                    Lp.coeFn_const 2 S.μ (1:ℝ)] with y h1 h2 _
    simp [h1, h2]
  have hPt_εlp : S.P t εlp = εlp := by
    calc S.P t εlp
        = S.P t (ε • Lp.const 2 S.μ (1:ℝ)) := by rw [hεlp_smul]
      _ = ε • S.P t (Lp.const 2 S.μ (1:ℝ)) := (S.P t).map_smul ε _
      _ = ε • Lp.const 2 S.μ (1:ℝ) := by rw [hPt_const1]
      _ = εlp := hεlp_smul.symm
  -- 0 ≤ f - εlp via the a.e. bound.
  have h_diff_ae : 0 ≤ᵐ[S.μ] (↑↑(f - εlp) : X → ℝ) := by
    filter_upwards [hf, hεlp_coe, Lp.coeFn_sub f εlp] with y hy hMy hSubY
    have : (↑↑(f - εlp) : X → ℝ) y = (f : X → ℝ) y - ε := by
      rw [hSubY]; simp [hMy]
    rw [Pi.zero_apply, this]
    linarith
  have h_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ f - εlp := (Lp.coeFn_nonneg _).mp h_diff_ae
  have h_pt_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ S.P t (f - εlp) :=
    S.P_positivity t ht _ h_diff_nn
  have h_pt_orbit_sub : S.P t (f - εlp) = S.P t f - εlp := by
    rw [map_sub, hPt_εlp]
  rw [h_pt_orbit_sub] at h_pt_diff_nn
  have h_ae := (Lp.coeFn_nonneg _).mpr h_pt_diff_nn
  filter_upwards [h_ae, Lp.coeFn_sub (S.P t f) εlp, hεlp_coe] with y hy hSub hMy
  have h_pt : (↑↑(S.P t f - εlp) : X → ℝ) y = (S.P t f : X → ℝ) y - ε := by
    rw [hSub]; simp [hMy]
  rw [Pi.zero_apply, h_pt] at hy
  linarith

/-- **Strong continuity at any `s ≥ 0`.** `P_strong_cont` gives this at
`t = 0`; the semigroup property + `P_contraction` (`‖P t‖ ≤ 1`)
upgrade it to every `s ≥ 0`, via the standard textbook argument:
* Approach from above: for `σ = s + t` with `t > 0`,
  `‖P σ g - P s g‖ = ‖P s (P t g) - P s g‖ ≤ ‖P t g - g‖ → 0`.
* Approach from below: for `σ < s`, `P s g = P σ (P (s-σ) g)`, so
  `‖P σ g - P s g‖ = ‖P σ (g - P (s-σ) g)‖ ≤ ‖g - P (s-σ) g‖ → 0`. -/
lemma strong_cont_at (S : MarkovSemigroup X) (g : Lp ℝ 2 S.μ) {s : ℝ}
    (hs : 0 ≤ s) :
    Filter.Tendsto (fun σ : ℝ => S.P σ g) (nhdsWithin s (Set.Ici 0))
      (nhds (S.P s g)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hcont0 := S.P_strong_cont g
  rw [Metric.tendsto_nhdsWithin_nhds] at hcont0
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont0 ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro σ hσ_in hσ_dist
  rcases lt_trichotomy σ s with hσ_lt | hσ_eq | hσ_gt
  · -- σ < s: P s g = P σ (P (s-σ) g), so P σ g - P s g = P σ (g - P (s-σ) g).
    have hr_pos : 0 < s - σ := sub_pos.mpr hσ_lt
    have hr_dist : dist (s - σ) 0 < δ := by
      have : dist (s - σ) 0 = s - σ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hr_pos]
      rw [this]
      have habsσ : |σ - s| < δ := by simpa [Real.dist_eq] using hσ_dist
      have := abs_lt.mp habsσ; linarith
    have h_g_close : dist (S.P (s - σ) g) g < ε := hδ hr_pos.le hr_dist
    have h_decomp : S.P s g = S.P σ (S.P (s - σ) g) := by
      have h_sg : S.P (σ + (s - σ)) = (S.P σ).comp (S.P (s - σ)) :=
        S.P_semigroup σ (s - σ) hσ_in hr_pos.le
      calc S.P s g = S.P (σ + (s - σ)) g := by rw [show σ + (s - σ) = s from by ring]
        _ = ((S.P σ).comp (S.P (s - σ))) g := by rw [h_sg]
        _ = S.P σ (S.P (s - σ) g) := rfl
    rw [h_decomp]
    -- dist (P σ g) (P σ (P (s-σ) g)) ≤ ‖P σ‖ · dist g (P (s-σ) g) ≤ dist g (P (s-σ) g) < ε.
    calc dist (S.P σ g) (S.P σ (S.P (s - σ) g))
        ≤ ‖S.P σ‖ * dist g (S.P (s - σ) g) := by
          simpa [dist_eq_norm] using (S.P σ).lipschitzWith.norm_sub_le g (S.P (s - σ) g)
      _ ≤ dist g (S.P (s - σ) g) :=
          mul_le_of_le_one_left dist_nonneg (S.P_contraction σ hσ_in)
      _ = dist (S.P (s - σ) g) g := dist_comm _ _
      _ < ε := h_g_close
  · -- σ = s.
    subst hσ_eq; simpa using hε
  · -- σ > s: P σ g = P s (P (σ-s) g).
    have hr_pos : 0 < σ - s := sub_pos.mpr hσ_gt
    have hr_dist : dist (σ - s) 0 < δ := by
      have : dist (σ - s) 0 = σ - s := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hr_pos]
      rw [this]
      have habsσ : |σ - s| < δ := by simpa [Real.dist_eq] using hσ_dist
      linarith [abs_lt.mp habsσ]
    have h_g_close : dist (S.P (σ - s) g) g < ε := hδ hr_pos.le hr_dist
    have h_decomp : S.P σ g = S.P s (S.P (σ - s) g) := by
      have h_sg : S.P (s + (σ - s)) = (S.P s).comp (S.P (σ - s)) :=
        S.P_semigroup s (σ - s) hs hr_pos.le
      calc S.P σ g = S.P (s + (σ - s)) g := by rw [show s + (σ - s) = σ from by ring]
        _ = ((S.P s).comp (S.P (σ - s))) g := by rw [h_sg]
        _ = S.P s (S.P (σ - s) g) := rfl
    rw [h_decomp]
    calc dist (S.P s (S.P (σ - s) g)) (S.P s g)
        ≤ ‖S.P s‖ * dist (S.P (σ - s) g) g := by
          simpa [dist_eq_norm] using (S.P s).lipschitzWith.norm_sub_le (S.P (σ - s) g) g
      _ ≤ dist (S.P (σ - s) g) g := mul_le_of_le_one_left dist_nonneg (S.P_contraction s hs)
      _ < ε := h_g_close

/-- **Orbit has right derivative `P_s Af` at any `s ≥ 0`.** From the
strong-L² derivative `Af` at `t = 0` (given by e.g. `GeneratorCompat`),
the orbit `σ ↦ P_σ f` is differentiable at every `s ≥ 0` (within
`Ici 0`) with derivative `P_s Af`. Standard semigroup commutation
trick + `strong_cont_at`:
* For `σ > s`: write `σ = s + t`, then
  `(σ-s)⁻¹ • (P_σ f - P_s f) = P_s (t⁻¹ • (P_t f - f)) → P_s Af`
  by linearity of `P_s` and the `t→0+` limit.
* For `σ < s`: write `s = σ + r`, then
  `(σ-s)⁻¹ • (P_σ f - P_s f) = P_σ (r⁻¹ • (P_r f - f))`,
  and we need the joint limit `P_σ (x_σ) → P_s (Af)` where
  `x_σ → Af` and `P_σ → P_s` strongly. The standard triangle bound
  `‖P_σ x_σ - P_s Af‖ ≤ ‖P_σ‖·‖x_σ - Af‖ + ‖P_σ Af - P_s Af‖` plus
  `‖P_σ‖ ≤ 1` + `strong_cont_at` closes it. -/
lemma orbit_hasDerivWithinAt (S : MarkovSemigroup X)
    {f Af : Lp ℝ 2 S.μ}
    (hAf : Filter.Tendsto (fun t : ℝ => t⁻¹ • (S.P t f - f))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Af))
    {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun σ : ℝ => S.P σ f) (S.P s Af) (Set.Ici 0) s := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  -- Goal: Tendsto (slope (fun σ => P σ f) s) (𝓝[Ici 0 \ {s}] s) (𝓝 (P s Af))
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- From hAf in metric form.
  have hAf_metric :
      ∀ ε' > 0, ∃ δ' > 0, ∀ t, 0 < t → dist t 0 < δ' →
        dist (t⁻¹ • (S.P t f - f)) Af < ε' := by
    intro ε' hε'
    rw [Metric.tendsto_nhdsWithin_nhds] at hAf
    obtain ⟨δ, hδ, h⟩ := hAf ε' hε'
    exact ⟨δ, hδ, fun t ht hdt => h ht hdt⟩
  -- From strong_cont_at at s for Af.
  have hcont := S.strong_cont_at Af hs
  rw [Metric.tendsto_nhdsWithin_nhds] at hcont
  obtain ⟨δ_cont, hδ_cont_pos, hδ_cont⟩ := hcont (ε / 2) (by linarith)
  obtain ⟨δ_Af, hδ_Af_pos, hδ_Af⟩ := hAf_metric (ε / 2) (by linarith)
  refine ⟨min δ_cont δ_Af, by positivity, ?_⟩
  intro σ hσ_in hσ_dist
  -- hσ_in : σ ∈ Ici 0 \ {s}.
  obtain ⟨hσ_ge0, hσ_ne⟩ := hσ_in
  simp only [Set.mem_singleton_iff] at hσ_ne
  have hσ_dist_cont : dist σ s < δ_cont :=
    lt_of_lt_of_le hσ_dist (min_le_left _ _)
  have hσ_dist_Af : dist σ s < δ_Af :=
    lt_of_lt_of_le hσ_dist (min_le_right _ _)
  -- Slope: (σ - s)⁻¹ • (P σ f - P s f)
  show dist (slope (fun σ => S.P σ f) s σ) (S.P s Af) < ε
  rw [slope_def_module]
  rcases lt_or_gt_of_ne hσ_ne with hσ_lt | hσ_gt
  · -- σ < s: write s = σ + (s - σ), use P s = P σ ∘ P (s-σ).
    have hr_pos : 0 < s - σ := sub_pos.mpr hσ_lt
    have hr_dist : dist (s - σ) 0 < δ_Af := by
      have : |s - σ| = s - σ := abs_of_pos hr_pos
      have : dist (s - σ) 0 = s - σ := by rw [Real.dist_eq, sub_zero, this]
      rw [this]
      have habsσ : |σ - s| < δ_Af := by simpa [Real.dist_eq] using hσ_dist_Af
      linarith [abs_lt.mp habsσ]
    have h_close_inner :
        dist ((s - σ)⁻¹ • (S.P (s - σ) f - f)) Af < ε / 2 :=
      hδ_Af _ hr_pos hr_dist
    -- P s f = P σ (P (s - σ) f).
    have hP_decomp : S.P s f = S.P σ (S.P (s - σ) f) := by
      have h := S.P_semigroup σ (s - σ) hσ_ge0 hr_pos.le
      have : S.P (σ + (s - σ)) f = (S.P σ).comp (S.P (s - σ)) f := by
        rw [h]
      simpa [show σ + (s - σ) = s from by ring] using this
    -- Slope: (σ - s)⁻¹ • (P σ f - P s f) = (σ - s)⁻¹ • (P σ f - P σ (P (s-σ) f))
    --      = (σ - s)⁻¹ • P σ (f - P (s-σ) f)
    --      = - (s - σ)⁻¹ • P σ (f - P (s-σ) f)
    --      = (s - σ)⁻¹ • P σ (P (s-σ) f - f)
    --      = P σ ((s - σ)⁻¹ • (P (s-σ) f - f))
    have h_slope_eq : (σ - s)⁻¹ • (S.P σ f - S.P s f)
        = S.P σ ((s - σ)⁻¹ • (S.P (s - σ) f - f)) := by
      rw [hP_decomp, ← map_sub (S.P σ), ← map_smul]
      congr 1
      calc (σ - s)⁻¹ • (f - S.P (s - σ) f)
          = -((s - σ)⁻¹) • (f - S.P (s - σ) f) := by
              rw [show σ - s = -(s - σ) from by ring, inv_neg]
        _ = -((s - σ)⁻¹ • (f - S.P (s - σ) f)) := by rw [neg_smul]
        _ = (s - σ)⁻¹ • -(f - S.P (s - σ) f) := by rw [← smul_neg]
        _ = (s - σ)⁻¹ • (S.P (s - σ) f - f) := by rw [neg_sub]
    rw [h_slope_eq]
    set inner := (s - σ)⁻¹ • (S.P (s - σ) f - f)
    -- Step 1: dist (P σ inner) (P σ Af) ≤ ‖P σ‖ * dist inner Af ≤ dist inner Af.
    have h1 : dist (S.P σ inner) (S.P σ Af) ≤ dist inner Af := by
      have hnorm : ‖S.P σ inner - S.P σ Af‖ ≤ ‖S.P σ‖ * ‖inner - Af‖ := by
        rw [← map_sub]; exact (S.P σ).le_opNorm _
      calc dist (S.P σ inner) (S.P σ Af)
          = ‖S.P σ inner - S.P σ Af‖ := dist_eq_norm _ _
        _ ≤ ‖S.P σ‖ * ‖inner - Af‖ := hnorm
        _ ≤ 1 * ‖inner - Af‖ := by
            have hle : ‖S.P σ‖ ≤ 1 := S.P_contraction σ hσ_ge0
            have hnn : 0 ≤ ‖inner - Af‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_right hle hnn
        _ = ‖inner - Af‖ := one_mul _
        _ = dist inner Af := (dist_eq_norm _ _).symm
    -- Step 2: dist (P σ Af) (P s Af) < ε / 2 by strong continuity at s.
    have h2 : dist (S.P σ Af) (S.P s Af) < ε / 2 := hδ_cont hσ_ge0 hσ_dist_cont
    -- Triangle: < ε/2 + ε/2.
    calc dist (S.P σ inner) (S.P s Af)
        ≤ dist (S.P σ inner) (S.P σ Af) + dist (S.P σ Af) (S.P s Af) :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by linarith [h1, h_close_inner]
      _ = ε := by ring
  · -- σ > s: write σ = s + (σ - s), use P σ = P s ∘ P (σ-s).
    have ht_pos : 0 < σ - s := sub_pos.mpr hσ_gt
    have ht_dist : dist (σ - s) 0 < δ_Af := by
      have : |σ - s| = σ - s := abs_of_pos ht_pos
      have heq : dist (σ - s) 0 = σ - s := by rw [Real.dist_eq, sub_zero, this]
      rw [heq]
      have habsσ : |σ - s| < δ_Af := by simpa [Real.dist_eq] using hσ_dist_Af
      linarith [abs_lt.mp habsσ]
    have h_close_inner :
        dist ((σ - s)⁻¹ • (S.P (σ - s) f - f)) Af < ε / 2 :=
      hδ_Af _ ht_pos ht_dist
    -- P σ f = P s (P (σ - s) f).
    have hP_decomp : S.P σ f = S.P s (S.P (σ - s) f) := by
      have h := S.P_semigroup s (σ - s) hs ht_pos.le
      have : S.P (s + (σ - s)) f = (S.P s).comp (S.P (σ - s)) f := by rw [h]
      simpa [show s + (σ - s) = σ from by ring] using this
    -- Slope: (σ - s)⁻¹ • (P σ f - P s f) = (σ - s)⁻¹ • (P s (P (σ-s) f) - P s f)
    --      = P s ((σ - s)⁻¹ • (P (σ-s) f - f))
    have h_slope_eq : (σ - s)⁻¹ • (S.P σ f - S.P s f)
        = S.P s ((σ - s)⁻¹ • (S.P (σ - s) f - f)) := by
      rw [hP_decomp, ← map_sub (S.P s), ← map_smul]
    rw [h_slope_eq]
    set inner := (σ - s)⁻¹ • (S.P (σ - s) f - f)
    have hnorm : ‖S.P s inner - S.P s Af‖ ≤ ‖S.P s‖ * ‖inner - Af‖ := by
      rw [← map_sub]; exact (S.P s).le_opNorm _
    calc dist (S.P s inner) (S.P s Af)
        = ‖S.P s inner - S.P s Af‖ := dist_eq_norm _ _
      _ ≤ ‖S.P s‖ * ‖inner - Af‖ := hnorm
      _ ≤ 1 * ‖inner - Af‖ := by
          have hle : ‖S.P s‖ ≤ 1 := S.P_contraction s hs
          exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ = ‖inner - Af‖ := one_mul _
      _ = dist inner Af := (dist_eq_norm _ _).symm
      _ < ε / 2 := h_close_inner
      _ < ε := by linarith

/-- A symmetric Markov semigroup is *hypercontractive* with rate `ρ > 0`
if `P_t : L^p → L^q` is a contraction whenever
`q ≤ 1 + (p − 1) · e^{2ρt}`:

  `‖P_t f‖_{L^q(μ)} ≤ ‖f‖_{L^p(μ)}`.

The source is the `L²(μ)` carrier, together with an explicit `MemLp`
hypothesis at exponent `p`. This handles both `p < 2` and `p > 2`
without changing the abstract carrier. -/
def IsHypercontractive (S : MarkovSemigroup X) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ (p q t : ℝ),
    1 < p → p ≤ q → 0 < t →
    q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t) →
    ∀ f : Lp ℝ 2 S.μ,
      MemLp ((⇑f) : X → ℝ) (ENNReal.ofReal p) S.μ →
      eLpNorm (((S.P t f) : X → ℝ)) (ENNReal.ofReal q) S.μ ≤
        eLpNorm ((⇑f) : X → ℝ) (ENNReal.ofReal p) S.μ

end MarkovSemigroup

/-- A *Dirichlet-Markov semigroup*: a symmetric Markov semigroup
bundled with its canonical Dirichlet form.

For a symmetric Markov semigroup the Dirichlet form is uniquely
determined by the semigroup as

  `E(f, g) = lim_{t↘0} (1/t) · ⟨[f], (I − P_t)[g]⟩
          = -(d/dt)|_{t=0+} ⟨[f], P_t[g]⟩`

(Fukushima–Oshima–Takeda construction). The user supplies a candidate
form `energy` together with an admissible core algebra `IsCore`, and
asserts via `energy_eq_deriv` that the candidate equals the canonical
form on the core (as a right-derivative at `0`). -/
structure DirichletMarkovSemigroup (X : Type*) [MeasurableSpace X]
    extends MarkovSemigroup X where
  /-- The Dirichlet form `E(f, g)`. -/
  energy : (X → ℝ) → (X → ℝ) → ℝ
  /-- Energy is symmetric. -/
  energy_symm : ∀ f g, energy f g = energy g f
  /-- Energy is nonnegative on the diagonal. -/
  energy_nonneg : ∀ f, 0 ≤ energy f f
  /-- Admissible core functions. -/
  IsCore : (X → ℝ) → Prop
  /-- Constants are core. -/
  IsCore_const : ∀ c : ℝ, IsCore (fun _ => c)
  /-- Core is closed under addition. -/
  IsCore_add : ∀ {f g}, IsCore f → IsCore g → IsCore (f + g)
  /-- Core is closed under scalar multiplication. -/
  IsCore_smul : ∀ (c : ℝ) {f}, IsCore f → IsCore (c • f)
  /-- **Strict-positive rpow closure** (Gross's strictly-positive escape).
  When `f` is in the core and `f ≥ ε > 0` a.e. for some explicit
  `ε > 0`, then `x ↦ f x ^ r` is also in the core for any real `r`. This
  is the standard "Markovian core" closure under smooth functional
  calculus, restricted to strictly positive elements (which is all we
  need for the Gross argument — see
  `plans/archive/gross-design-strictly-positive-escape.md`). Note that the
  axiom uses `Real.rpow` directly (the syntactic form appearing in
  `grossPow`), so no a.e./pointwise bridging is needed; the null set
  where `f y ≤ 0` is benign because `rpow_def_of_neg` matches the
  convention used everywhere in this file (compare BGL Ch 1, "algebra
  of admissible test functions"). Mathematically, for concrete cores
  like `C^∞_b(ℝ^n)` on Gaussian measure, this is immediate: adding a
  positive constant to a `C^∞_b` element gives `f ≥ ε > 0` *everywhere*,
  and `f^r` is then `C^∞_b` by chain rule. -/
  IsCore_rpow_pos_strict : ∀ {f : X → ℝ} (_ : IsCore f) {ε : ℝ} (_ : 0 < ε),
    (∀ᵐ y ∂μ, ε ≤ f y) → ∀ (r : ℝ), IsCore (fun x => f x ^ r)
  /-- **L^∞ membership.** Every core function is essentially bounded.
  This is the standard BGL hypothesis on the "algebra of admissible
  test functions" (cf. BGL §1.4: "an algebra of *bounded* functions
  in the generator domain"). For `C^∞_b`-style cores (`IsCoreFin`,
  Schwartz-with-Gaussian-tweaks, polynomial cores on probability
  measures) this is immediate from the bounded-derivatives part of
  the definition. Needed by `grossPow_hasDerivWithinAt` to invoke
  `hasDerivAt_integral_rpow_exponent` (which requires a uniform
  bound `|w y| ≤ M` on the integrand) and to combine with `hf_pos`
  for `ε ≤ f ≤ M` framing. -/
  IsCore_memLp_top : ∀ {f : X → ℝ}, IsCore f → ∃ M : ℝ, ∀ᵐ y ∂μ, |f y| ≤ M
  /-- Energy is bilinear on the left. -/
  energy_add_left : ∀ f₁ f₂ g, IsCore f₁ → IsCore f₂ → IsCore g →
    energy (f₁ + f₂) g = energy f₁ g + energy f₂ g
  /-- Energy is homogeneous on the left. -/
  energy_smul_left : ∀ (c : ℝ) f g, IsCore f → IsCore g →
    energy (c • f) g = c * energy f g
  /-- Constants have zero energy. -/
  energy_const : ∀ c : ℝ, energy (fun _ => c) (fun _ => c) = 0
  /-- Every core function lies in `L²(μ)`. -/
  IsCore_memLp : ∀ {f}, IsCore f → MemLp f 2 μ
  /-- **Generator–Dirichlet-form compatibility.** The energy form is
  the (negated) right-derivative-at-zero of the `L²(μ)` pairing
  `⟨[f], P_t[g]⟩`. -/
  energy_eq_deriv : ∀ f g (hf : IsCore f) (hg : IsCore g),
    let coreToL2 : ∀ {h : X → ℝ}, IsCore h → Lp ℝ 2 μ :=
      fun {h} hh => (IsCore_memLp hh).toLp h
    HasDerivWithinAt
      (fun t : ℝ => ⟪coreToL2 hf, P t (coreToL2 hg)⟫_ℝ)
      (-energy f g) (Set.Ici 0) 0

namespace DirichletMarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- View a core function as an element of `L²(μ)`. -/
def coreToL2 (D : DirichletMarkovSemigroup X) {f : X → ℝ} (hf : D.IsCore f) :
    Lp ℝ 2 D.μ :=
  (D.IsCore_memLp hf).toLp f

/-- The Dirichlet form data of a `DirichletMarkovSemigroup` packages
into a `DirichletSpace`. -/
@[reducible]
def toDirichletSpace (D : DirichletMarkovSemigroup X) : DirichletSpace X where
  μ := D.μ
  hμ := D.hμ
  energy := D.energy
  energy_symm := D.energy_symm
  energy_nonneg := D.energy_nonneg
  IsCore := D.IsCore
  IsCore_const := D.IsCore_const
  IsCore_add := D.IsCore_add
  IsCore_smul := D.IsCore_smul
  energy_add_left := D.energy_add_left
  energy_smul_left := D.energy_smul_left
  energy_const := D.energy_const

/-- LSI for the bundled structure: LSI for the underlying Dirichlet form. -/
def SatisfiesLogSobolev (D : DirichletMarkovSemigroup X) (ρ : ℝ) : Prop :=
  let _ : DirichletSpace X := D.toDirichletSpace
  DirichletSpace.SatisfiesLogSobolev (X := X) ρ

/-- Hypercontractivity for the bundled structure: hypercontractivity
of the underlying `L²` semigroup. -/
def IsHypercontractive (D : DirichletMarkovSemigroup X) (ρ : ℝ) : Prop :=
  D.toMarkovSemigroup.IsHypercontractive ρ

end DirichletMarkovSemigroup

/-! The local port omits three unused upstream abstract postulates.
The concrete Gaussian theorem uses the proved GrossODE route instead. -/

/-! ## H0 — hypothesis-parameterised Gross (Route A scaffold)

The discharge route for `gross_lsi_implies_hypercontractive` keeps the
abstract `DirichletMarkovSemigroup` (and its shipped sorry-free
GaussianFin instance) **unchanged**: the strong-generator facts are
explicit `Prop` hypotheses, not new structural fields — the same
leaf-placement design already used for `stroock_varopoulos`,
Gemini-vetted (passes 1–4). They are discharged per instance at the
call-site (GaussianFin in gaussian-hilbert). See
`plans/gross-discharge.md` (§2–§3) and
`plans/gaussianfin-0b-readiness.md`. -/

variable {X : Type*} [MeasurableSpace X]

/-- **Core invariance under the semigroup.** Applying the `L²`
semigroup `P_t` (`t ≥ 0`) to (the `L²` class of) a core function
yields the `L²` class of *some* core function. Phrased `L²`-side
because the abstract structure exposes only the `Lp` operator, not a
function-level action. Discharged for GaussianFin by
`ouSemigroupFin_preserves_IsCore` (`g' := ouSemigroupFin t g`). -/
def CoreSemigroupInvariant (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ {g : X → ℝ} (hg : D.IsCore g),
    ∃ (g' : X → ℝ) (hg' : D.IsCore g'),
      D.P t (D.coreToL2 hg) = D.coreToL2 hg'

/-- **Generator–form compatibility (strong).** `coreToL2 f ∈ dom(A)`
with the difference quotient converging in `L²`-*norm* (not merely
weakly), and the generator value `Af` pinned by the Dirichlet form
against every core test function. Strengthens `energy_eq_deriv`
(weak, scalar-paired). Gemini pass-3 green-lit; uses the explicit
`nhdsWithin (0:ℝ) (Set.Ioi 0)` / `nhds` idiom of this file (matching
`P_strong_cont`). Discharged for GaussianFin via the proved 1D linear
heat equation lifted + pointwise→strong-`L²` DCT. -/
def GeneratorCompat (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {f : X → ℝ} (hf : D.IsCore f), ∃ Af : Lp ℝ 2 D.μ,
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (D.P t (D.coreToL2 hf) - D.coreToL2 hf))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Af)
    ∧ ∀ {g : X → ℝ} (hg : D.IsCore g),
        ⟪D.coreToL2 hg, Af⟫_ℝ = - D.energy g f

/-- **Stroock–Varopoulos, generator-paired** (Gemini pass-3 trap fix:
`u^{q-1} ∉ core` makes the abstract `E(u,u^{q-1})` unusable; pass-4
binding fix: `GeneratorCompat` is existential, so the generator
element `Au` + its strong-limit witness are passed explicitly rather
than via a global `A`). The core-power hypotheses match the existing
`stroock_varopoulos` axiom (cleaner than `MemLp.toLp` packaging and
equivalent for the GaussianFin discharge, which has the core
powers). `_hq`/`_hu_half` are contract antecedents (the inequality is
claimed for `q > 1` with `u^{q/2}` core — this is the full range the
Gross interpolation path `q(s) = 1+(p-1)e^{2ρs}` visits for `p > 1`, and
S–V holds throughout: for diffusion/gradient forms it is in fact an
equality `(4(q-1)/q²)Γ(u^{q/2}) = Γ(u,u^{q-1})`. The `2 ≤ q → 1 < q`
relaxation is deep-think vetted, rating Standard — see
`plans/archive/sv-q-relaxation-vetting.md`); `_`-prefixed per the
Mathlib convention for binders required by the statement's shape but
not referenced in the body — the discharger still supplies them
positionally. -/
def StroockVaropoulos (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {u : X → ℝ} (hu : D.IsCore u) (_hu_pos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ y ∂D.μ, ε ≤ u y)
    (q : ℝ) (_hq : 1 < q)
    (_hu_half : D.IsCore (fun x => u x ^ (q / 2)))
    (hu_one : D.IsCore (fun x => u x ^ (q - 1)))
    (Au : Lp ℝ 2 D.μ),
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (D.P t (D.coreToL2 hu) - D.coreToL2 hu))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Au) →
    (4 * (q - 1) / q ^ 2) *
        D.energy (fun x => u x ^ (q / 2)) (fun x => u x ^ (q / 2))
      ≤ ⟪D.coreToL2 hu_one, - Au⟫_ℝ

/-- **Core `L^p`/`L²` density** (per-instance hypothesis, Gemini-vetted
2026-05-21 — `plans/archive/corelpapprox-vetting.md`). Every nonnegative
`f ∈ L²(μ) ∩ L^p(μ)` is approximated by a sequence of *core, pointwise
strictly-positive* functions `gₙ` converging to `f` in **both** `L^p` and
`L²`. This is the density input the abstract structure cannot supply; the
orbit convergence needed for hypercontractivity is recovered abstractly from
`L²`-contraction of the semigroup (so neither `t` nor `P_t` appears here).
Discharged per instance — e.g. for the Gaussian/OU semigroup by mollified
bounded truncations `+ 1/n` (smooth, bounded, `≥ 1/n` everywhere, hence
core and pointwise strictly positive). -/
def CoreLpL2Approx (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {p : ℝ}, 1 ≤ p → ∀ (f : Lp ℝ 2 D.μ),
    MemLp ((f : X → ℝ)) (ENNReal.ofReal p) D.μ → 0 ≤ f →
    ∃ (g : ℕ → X → ℝ) (_hg : ∀ n, D.IsCore (g n)),
      (∀ n, ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε ≤ g n x) ∧
      Filter.Tendsto (fun n => eLpNorm ((f : X → ℝ) - g n) (ENNReal.ofReal p) D.μ)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => eLpNorm ((f : X → ℝ) - g n) 2 D.μ)
        Filter.atTop (nhds 0)

/-! **Gross 1975, Theorem 1 — hypothesis-parameterised (Route A
target).** The predicates `CoreSemigroupInvariant` / `GeneratorCompat`
/ `StroockVaropoulos` (above) live here; the **theorem and its proof**
`gross_lsi_implies_hypercontractive_of_hypotheses` (LSI ⇒
hypercontractivity given those three; Gross's differentiation
argument — Phases P2/P3 of `plans/gross-discharge.md`) are relocated
to `MarkovSemigroups.Abstract.GrossODE` (which imports this file), so
the heavy ODE scaffolding does not bloat this module. The existing
`gross_lsi_implies_hypercontractive` axiom is retained (non-breaking —
downstream `gaussian-hilbert` keeps compiling) until the relocated
theorem is proved and the call-site is rewired. -/

namespace DirichletMarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-! ## Direct consequence: the semigroup improves integrability -/

/-- Direct application of hypercontractivity to an `L²(μ)` function
that also lies in `L^p(μ)`:

  `‖P_t f‖_{L^q(μ)} ≤ ‖f‖_{L^p(μ)}`

whenever `q ≤ 1 + (p − 1) e^{2ρt}`. -/
theorem semigroup_lp_improvement (D : DirichletMarkovSemigroup X)
    (ρ : ℝ) (h_hyp : D.IsHypercontractive ρ)
    (f : Lp ℝ 2 D.μ) (p q : ℝ)
    (hf_memLp : MemLp ((⇑f) : X → ℝ) (ENNReal.ofReal p) D.μ)
    (hp : 1 < p) (hpq : p ≤ q)
    (t : ℝ) (ht : 0 < t)
    (h_bound : q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t)) :
    eLpNorm (((D.P t f) : X → ℝ)) (ENNReal.ofReal q) D.μ ≤
      eLpNorm ((⇑f) : X → ℝ) (ENNReal.ofReal p) D.μ :=
  h_hyp.2 p q t hp hpq ht h_bound f hf_memLp

end DirichletMarkovSemigroup

end
