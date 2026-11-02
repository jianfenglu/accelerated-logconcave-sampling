/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Discharge of `ouSemigroup_entropy_sq_decay_bound`

This file derives BGL Theorem 5.5.2 — the dynamic entropy decay bound

  `Ent(f²) - Ent(P_t f²) ≤ 2(1 - e^{-2t}) E(f, f)`

— as a theorem, from the two atomic axioms in
`MarkovSemigroups/General/OUEntropyDecomposition.lean`:

* `ouSemigroup_fisher_info_decay` (A1): `I(P_t g) ≤ e^{-2t} I(g)`.
* `hasDerivAt_entropy_ouSemigroup` (A2): `(d/dt) H(P_t g) = -I(P_t g)`.

## Proof outline

For `f` `IsCore` with `|f|, |f'|, |f''| ≤ M`, fix `ε > 0` and set
`g_ε := f² + ε`. Then:

1. `g_ε` is C¹ with `ε ≤ g_ε ≤ M² + ε`, `|g_ε'| = |2 f · f'| ≤ 2 M²`.
   So A1, A2 apply with the natural bounds.
2. By A2 + FTC, `H(g_ε) - H(P_t g_ε) = ∫_0^t I(P_s g_ε) ds`.
3. By A1, `I(P_s g_ε) ≤ exp(-2s) · I(g_ε)`, so the integral is bounded
   by `(1 - e^{-2t})/2 · I(g_ε)`.
4. `I(g_ε) = ∫ (2 f f')² / (f² + ε) dγ ≤ ∫ 4 (f')² dγ = 4 E(f, f)`
   (using `f²/(f² + ε) ≤ 1`).
5. So `H(g_ε) - H(P_t g_ε) ≤ 2 (1 - e^{-2t}) E(f, f)`.
6. Take ε → 0: `H(g_ε) → H(f²)` (DCT, `s log s` continuous on
   `[0, M² + 1]`). Same for `H(P_t g_ε) → H(P_t f²)`.
7. Conclude `H(f²) - H(P_t f²) ≤ 2(1 - e^{-2t}) E(f, f)`.
8. By γ-invariance `∫ P_t f² dγ = ∫ f² dγ`, the subtraction terms in
   `DirichletSpace.entropy` cancel, so the same bound holds for
   `entropy` (not just `boltzmannEntropy`).
-/

import AcceleratedLogConcave.External.MarkovSemigroups.General.OUEntropyDecomposition
import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanHermite
import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanStein

open MeasureTheory Filter Set Real ProbabilityTheory Topology

open scoped ContDiff

noncomputable section

namespace Gaussian1D

/-! ## Auxiliary: f² + ε satisfies the A1/A2 hypotheses -/

/-- For `IsCore f` and `ε > 0`, the function `g_ε(x) = f(x)² + ε`
satisfies the regularization bundle used by A1, A2: `C¹`,
`ε ≤ g_ε ≤ M² + ε`, `|g_ε'| ≤ 2 M²`. -/
structure RegularizedSquare (f : ℝ → ℝ) (M ε : ℝ) where
  /-- The regularized function. -/
  toFun : ℝ → ℝ := fun x => f x ^ 2 + ε
  /-- C¹ smoothness. -/
  contDiff : ContDiff ℝ 1 toFun
  /-- Positive lower bound. -/
  lo : ∀ x, ε ≤ toFun x
  /-- Upper bound `M² + ε`. -/
  hi : ∀ x, toFun x ≤ M ^ 2 + ε
  /-- Derivative bound `2 M²` (using `g_ε' = 2 f f'`). -/
  deriv_bd : ∀ x, |deriv toFun x| ≤ 2 * M ^ 2

/-- The regularized square of an IsCore function. -/
def regularizedSquare {f : ℝ → ℝ} (hf : IsCore f) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M ∧ ‖deriv f x‖ ≤ M ∧ ‖deriv (deriv f) x‖ ≤ M)
    {ε : ℝ} (_hε : 0 < ε) :
    RegularizedSquare f M ε where
  toFun := fun x => f x ^ 2 + ε
  contDiff := by
    have hf_C1 : ContDiff ℝ 1 f :=
      hf.contDiff.of_le (by simp : ((1 : WithTop ℕ∞)) ≤ ∞)
    exact (hf_C1.pow 2).add contDiff_const
  lo := fun x => by
    show ε ≤ f x ^ 2 + ε
    have : 0 ≤ f x ^ 2 := sq_nonneg _
    linarith
  hi := fun x => by
    show f x ^ 2 + ε ≤ M ^ 2 + ε
    have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
    have hfx : |f x| ≤ M := by
      rw [← Real.norm_eq_abs]; exact (hM x).1
    have : f x ^ 2 ≤ M ^ 2 := by
      rw [sq_abs (f x) |>.symm]
      exact sq_le_sq' (by linarith [abs_nonneg (f x)]) hfx
    linarith
  deriv_bd := fun x => by
    have hf_C1 : ContDiff ℝ 1 f :=
      hf.contDiff.of_le (by simp : ((1 : WithTop ℕ∞)) ≤ ∞)
    have hf_diff : DifferentiableAt ℝ f x :=
      (hf_C1.differentiable (by simp)).differentiableAt
    -- HasDerivAt f at x with value (deriv f x).
    have hf_deriv : HasDerivAt f (deriv f x) x := hf_diff.hasDerivAt
    -- HasDerivAt (f^2) at x with value 2 * f x * deriv f x.
    have hf_sq : HasDerivAt (fun y => f y ^ 2) (2 * f x ^ 1 * deriv f x) x := by
      convert hf_deriv.pow 2 using 1
    -- Adding the constant ε.
    have hf_sq_add : HasDerivAt (fun y => f y ^ 2 + ε) (2 * f x ^ 1 * deriv f x) x :=
      hf_sq.add_const ε
    have h_deriv : deriv (fun y => f y ^ 2 + ε) x = 2 * f x * deriv f x := by
      have := hf_sq_add.deriv
      simpa using this
    rw [h_deriv]
    have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
    have hfx : |f x| ≤ M := by rw [← Real.norm_eq_abs]; exact (hM x).1
    have hf'x : |deriv f x| ≤ M := by rw [← Real.norm_eq_abs]; exact (hM x).2.1
    calc |2 * f x * deriv f x| = 2 * |f x| * |deriv f x| := by
            rw [abs_mul, abs_mul]
            simp
      _ ≤ 2 * M * M := by
            apply mul_le_mul (mul_le_mul (le_refl 2) hfx (abs_nonneg _) (by norm_num))
              hf'x (abs_nonneg _) (by positivity)
      _ = 2 * M ^ 2 := by ring

/-! ## Discharge of `ouSemigroup_entropy_sq_decay_bound`

The proof packages the above and combines A1, A2 to derive the bound. -/

/-! ### Helper: integrability and bounds for `f² + ε` under `IsCore` -/

/-- A pointwise bound on `s log s` and its absolute value for `s ∈ [0, A]`,
extracted as a uniform constant via compactness. -/
private lemma exists_mul_log_bound (A : ℝ) (_hA : 0 ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc (0 : ℝ) A, |s * Real.log s| ≤ B := by
  have h_compact : IsCompact (Set.Icc (0 : ℝ) A) := isCompact_Icc
  have h_cont_abs : Continuous (fun s => |s * Real.log s|) :=
    Real.continuous_mul_log.abs
  have h_im_compact : IsCompact ((fun s => |s * Real.log s|) '' Set.Icc 0 A) :=
    h_compact.image h_cont_abs
  obtain ⟨B, hB⟩ := h_im_compact.bddAbove
  refine ⟨max B 0, le_max_right _ _, fun s hs => ?_⟩
  exact (hB ⟨s, hs, rfl⟩).trans (le_max_left _ _)

/-- For `IsCore f`, the OU semigroup applied to `f² + ε` equals
`ouSemigroup t (f²) + ε`. -/
private lemma ouSemigroup_sq_add_const {f : ℝ → ℝ} (hf : IsCore f) (ε : ℝ)
    (t : ℝ) (_ht : 0 ≤ t) :
    ouSemigroup t (fun x => f x ^ 2 + ε) =
    fun x => ouSemigroup t (fun x => f x ^ 2) x + ε := by
  ext x
  show ∫ y, (f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)) ^ 2 + ε ∂γ
      = (∫ y, (f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)) ^ 2 ∂γ) + ε
  obtain ⟨h_smooth, M, hM⟩ := hf
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  have hf_meas : Measurable f := h_smooth.continuous.measurable
  have h_int_sq : Integrable
      (fun y => (f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2*t)) * y)) ^ 2) γ := by
    refine Integrable.mono' (integrable_const (M ^ 2)) ?_ ?_
    · refine ((hf_meas.comp
        (measurable_const.add (measurable_const.mul measurable_id))).pow_const 2).aestronglyMeasurable
    · filter_upwards with y
      have hbd : |f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2*t)) * y)| ≤ M := by
        rw [← Real.norm_eq_abs]; exact (hM _).1
      have hsq : (f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2*t)) * y)) ^ 2 ≤ M ^ 2 := by
        have h_abs_sq :
            |f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2*t)) * y)| ^ 2 ≤ M ^ 2 := by
          have hnn : 0 ≤ |f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2*t)) * y)| :=
            abs_nonneg _
          nlinarith
        rwa [sq_abs] at h_abs_sq
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsq
  rw [integral_add h_int_sq (integrable_const ε)]
  simp

/-- **General 1D Boltzmann-entropy decay bound.**

For a `C¹` function `g` with `ε ≤ g ≤ M` and `|g'| ≤ M` (so the
Fisher-information regularization hypotheses of A1/A2 hold), and `t ≥ 0`,
`H(g) - H(P_t g) ≤ (1 - e^{-2t})/2 · I(g)`, where `H` is the Boltzmann
entropy `∫ g log g dγ` and `I` is the Fisher information `∫ (g')²/g dγ`.

This is the atomic FTC assembly of A1 (`ouSemigroup_fisher_info_decay`)
and A2 (`hasDerivAt_entropy_ouSemigroup` plus its boundary form). It is
strictly more general than the squared specialization
`ouSemigroup_entropy_sq_decay_bound_proved`, which it powers, and is the
per-coordinate building block for the multivariate tensor lift. -/
theorem boltzmannEntropy_ouSemigroup_decay_le
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    boltzmannEntropy g - boltzmannEntropy (ouSemigroup t g) ≤
      (1 - Real.exp (-2 * t)) / 2 * fisherInfo g := by
  -- The function `H(s) := H(P_s g)` and the Fisher information `I(g)`.
  set H : ℝ → ℝ := fun s => boltzmannEntropy (ouSemigroup s g) with hH_def
  set I : ℝ := fisherInfo g with hI_def
  -- Derivative of `H` on `Ioo 0 t`: by A2, `(d/ds) H(s) = -I(P_s g)`.
  have hH_deriv_pos : ∀ s ∈ Set.Ioo 0 t,
      HasDerivWithinAt H (-fisherInfo (ouSemigroup s g)) (Set.Ioi s) s := by
    intro s hs
    have h := hasDerivAt_entropy_ouSemigroup g hg hε hg_lo hg_hi hg'_bd hs.1
    exact h.hasDerivWithinAt
  -- Boundary right-derivative at 0 is `-I(g)`.
  have hH_deriv_zero : HasDerivWithinAt H (-I) (Set.Ici 0) 0 := by
    have h := hasDerivWithinAt_entropy_ouSemigroup_zero g hg hε hg_lo hg_hi hg'_bd
    exact h
  -- Continuity of `H` on `Icc 0 t`.
  have hH_cont : ContinuousOn H (Set.Icc 0 t) := by
    intro s hs
    rcases lt_or_eq_of_le hs.1 with hs_pos | hs_zero
    · have h := hasDerivAt_entropy_ouSemigroup g hg hε hg_lo hg_hi hg'_bd hs_pos
      exact (h.hasDerivWithinAt (s := Set.Icc 0 t)).continuousWithinAt
    · have hs_eq : s = 0 := hs_zero.symm
      subst hs_eq
      exact hH_deriv_zero.continuousWithinAt.mono (fun x hx => hx.1)
  -- Pointwise inequality `-e^{-2s} I(g) ≤ -I(P_s g)` for `s ∈ Ioo 0 t`.
  have h_fisher_le : ∀ s, 0 ≤ s →
      fisherInfo (ouSemigroup s g) ≤ Real.exp (-2 * s) * I := by
    intro s hs
    exact ouSemigroup_fisher_info_decay g hg hε hg_lo hg_hi hg'_bd s hs
  have h_ineq_pointwise : ∀ s ∈ Set.Ioo 0 t,
      -Real.exp (-2 * s) * I ≤ -fisherInfo (ouSemigroup s g) := by
    intro s hs
    have hfish := h_fisher_le s hs.1.le
    linarith
  -- `φ(s) := -e^{-2s} I` is continuous, hence integrable on `Icc 0 t`.
  set φ : ℝ → ℝ := fun s => -Real.exp (-2 * s) * I with hφ_def
  have hφ_cont : Continuous φ := by
    show Continuous (fun s => -Real.exp (-2 * s) * I); fun_prop
  have hφ_int : MeasureTheory.IntegrableOn φ (Set.Icc 0 t) :=
    hφ_cont.continuousOn.integrableOn_Icc
  -- FTC inequality: `∫₀ᵗ φ s ds ≤ H(t) - H(0)`.
  have hFTC : ∫ s in (0)..t, φ s ≤ H t - H 0 := by
    refine intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le ht hH_cont ?_
      hφ_int h_ineq_pointwise
    intro s hs
    exact hH_deriv_pos s hs
  -- Evaluate `∫₀ᵗ -e^{-2s} ds = (e^{-2t} - 1)/2`.
  have hderiv_exp : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => Real.exp (-2 * u) / 2) (-Real.exp (-2 * s)) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => -2 * u) (-2 : ℝ) s := by
      simpa using (hasDerivAt_id s).const_mul (-2 : ℝ)
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-2 * u))
        (Real.exp (-2 * s) * (-2)) s := (Real.hasDerivAt_exp (-2 * s)).comp s h1
    have h3 : HasDerivAt (fun u : ℝ => Real.exp (-2 * u) / 2)
        (Real.exp (-2 * s) * (-2) / 2) s := h2.div_const 2
    convert h3 using 1; ring
  have hint_phi : ∫ s in (0)..t, -Real.exp (-2 * s) =
      Real.exp (-2 * t) / 2 - Real.exp (-2 * 0) / 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u => Real.exp (-2 * u) / 2)
      (f' := fun u => -Real.exp (-2 * u)) (a := 0) (b := t)
      (fun s _ => hderiv_exp s)
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).neg.intervalIntegrable 0 t)
  have hint_phi_simp : ∫ s in (0)..t, -Real.exp (-2 * s) =
      (Real.exp (-2 * t) - 1) / 2 := by
    rw [hint_phi]; have : Real.exp (-2 * 0) = 1 := by simp
    rw [this]; ring
  have hint_φ : ∫ s in (0)..t, φ s = I * ((Real.exp (-2 * t) - 1) / 2) := by
    show ∫ s in (0)..t, -Real.exp (-2 * s) * I = I * ((Real.exp (-2 * t) - 1) / 2)
    rw [intervalIntegral.integral_mul_const, hint_phi_simp]; ring
  rw [hint_φ] at hFTC
  -- `H 0 = boltzmannEntropy g` and `H t = boltzmannEntropy (P_t g)`.
  have hH_0 : H 0 = boltzmannEntropy g := by
    show boltzmannEntropy (ouSemigroup 0 g) = boltzmannEntropy g
    rw [ouSemigroup_zero]
  have hH_t : H t = boltzmannEntropy (ouSemigroup t g) := rfl
  rw [hH_0, hH_t] at hFTC
  -- Rearrange: `H(g) - H(P_t g) ≤ I · (1 - e^{-2t})/2`.
  have he : (1 - Real.exp (-2 * t)) / 2 * I = -(I * ((Real.exp (-2 * t) - 1) / 2)) := by
    ring
  rw [he]
  linarith

/-- **Entropy decay for `f²` under OU (BGL Theorem 5.5.2)** — PROVED
(was axiom).

For `IsCore f` and `t ≥ 0`,
  `Ent_γ(f²) - Ent_γ(P_t(f²)) ≤ 2 (1 - e^{-2t}) · E(f, f)`.

Discharged via A1 (Fisher info decay) + A2 (de Bruijn identity) +
ε-regularization `g_ε := f² + ε` + FTC + DCT-based `ε → 0` limit. -/
theorem ouSemigroup_entropy_sq_decay_bound_proved (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCore f) :
    DirichletSpace.entropy (ds := dirichletSpace) (fun x => f x * f x) -
    DirichletSpace.entropy (ds := dirichletSpace)
      (ouSemigroup t (fun x => f x * f x)) ≤
      (1 - Real.exp (-2 * 1 * t)) * (2 / 1) * ouEnergy f f := by
  -- Setup: extract the IsCore data and bounds.
  obtain ⟨h_smooth, M, hM⟩ := hf
  have hf_core : IsCore f := ⟨h_smooth, M, hM⟩
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0).1
  have hf_meas : Measurable f := h_smooth.continuous.measurable
  have hf_cont : Continuous f := h_smooth.continuous
  -- Bound: |f| ≤ M, |f'| ≤ M.
  have hf_le : ∀ x, |f x| ≤ M := fun x => by rw [← Real.norm_eq_abs]; exact (hM x).1
  have hf'_le : ∀ x, |deriv f x| ≤ M := fun x => by rw [← Real.norm_eq_abs]; exact (hM x).2.1
  -- The squared function g(x) = f(x)² is bounded by M² and continuous (in fact C^∞).
  set g : ℝ → ℝ := fun x => f x ^ 2 with hg_def
  have hg_cont : Continuous g := hf_cont.pow 2
  have hg_meas : Measurable g := hg_cont.measurable
  have hg_nn : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
  have hg_bdd : ∀ x, g x ≤ M ^ 2 := fun x => by
    show f x ^ 2 ≤ M ^ 2
    rw [sq_abs (f x) |>.symm]
    exact sq_le_sq' (by linarith [abs_nonneg (f x)]) (hf_le x)
  -- The pointwise equality `g x = f x * f x`.
  have hg_mul : (fun x => f x * f x) = g := by ext x; show f x * f x = f x ^ 2; ring
  -- The Dirichlet energy `E(f, f) = ∫ (f')² dγ`.
  set Ef : ℝ := ouEnergy f f with hEf_def
  have hEf_nn : 0 ≤ Ef :=
    integral_nonneg (fun x => mul_self_nonneg _)
  -- The OU semigroup applied to `g = f²` is bounded by `M²` pointwise.
  -- Construct `P_t g` for any `s ≥ 0`.
  have hPg_bdd : ∀ s, 0 ≤ s → ∀ x, 0 ≤ ouSemigroup s g x ∧ ouSemigroup s g x ≤ M ^ 2 := by
    intro s hs x
    have hint : Integrable (fun y => g (Real.exp (-s) * x +
        Real.sqrt (1 - Real.exp (-2 * s)) * y)) γ := by
      refine Integrable.mono' (integrable_const (M ^ 2)) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]; exact hg_bdd _
    refine ⟨?_, ?_⟩
    · show 0 ≤ ∫ y, g (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂γ
      exact integral_nonneg (fun y => hg_nn _)
    · show ∫ y, g (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂γ ≤ M ^ 2
      calc ∫ y, _ ∂γ
          ≤ ∫ _y, M ^ 2 ∂γ :=
            integral_mono hint (integrable_const _) (fun y => hg_bdd _)
        _ = M ^ 2 := by simp
  -- Mean preservation: ∫ P_t g dγ = ∫ g dγ.
  have h_mean : ∫ x, ouSemigroup t g x ∂γ = ∫ x, g x ∂γ := by
    set a := Real.exp (-t)
    set b := Real.sqrt (1 - Real.exp (-2 * t))
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ : Measurable φ := Measurable.add
      (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)
    have hmap := ou_kernel_map t ht
    have hg_int : Integrable g γ := by
      refine Integrable.mono' (integrable_const (M ^ 2))
        hg_meas.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]
      exact hg_bdd _
    have hgφ_int : Integrable (g ∘ φ) (γ.prod γ) := by
      have hasm' : AEStronglyMeasurable g ((γ.prod γ).map φ) := by
        rw [hmap]; exact hg_meas.aestronglyMeasurable
      have hint' : Integrable g ((γ.prod γ).map φ) := by rw [hmap]; exact hg_int
      exact (integrable_map_measure hasm' hφ.aemeasurable).mp hint'
    show ∫ x, ouSemigroup t g x ∂γ = ∫ x, g x ∂γ
    simp only [ouSemigroup]
    rw [show (∫ x, (∫ y, g (a * x + b * y) ∂γ) ∂γ) = ∫ p, g (φ p) ∂(γ.prod γ) from
      (integral_prod (g ∘ φ) hgφ_int).symm]
    have hlaw : HasLaw φ γ (γ.prod γ) := ⟨hφ.aemeasurable, hmap⟩
    exact hlaw.integral_comp hg_meas.aestronglyMeasurable
  -- DirichletSpace.entropy h = ∫ h log h dγ - (∫h) log (∫h).
  -- By mean preservation, the (∫h)log(∫h) terms for h = g and h = P_t g coincide.
  -- So LHS = ∫ g log g - ∫ P_t g · log(P_t g).
  -- This is the Boltzmann entropy difference `H(g) - H(P_t g)`.
  set Eg : ℝ := ∫ x, g x ∂γ with hEg_def
  have hEntropy_diff :
      DirichletSpace.entropy (ds := dirichletSpace) (fun x => f x * f x) -
        DirichletSpace.entropy (ds := dirichletSpace)
          (ouSemigroup t (fun x => f x * f x)) =
      (∫ x, g x * Real.log (g x) ∂γ) -
        (∫ x, ouSemigroup t g x * Real.log (ouSemigroup t g x) ∂γ) := by
    -- Rewrite f x * f x as g x = f x ^ 2 globally.
    have h2 : (fun x => f x * f x) = g := hg_mul
    have h3 : ouSemigroup t (fun x => f x * f x) = ouSemigroup t g := by rw [h2]
    show ((∫ x, f x * f x * Real.log (f x * f x) ∂γ) -
            (∫ x, f x * f x ∂γ) * Real.log (∫ x, f x * f x ∂γ)) -
          ((∫ x, ouSemigroup t (fun x => f x * f x) x *
              Real.log (ouSemigroup t (fun x => f x * f x) x) ∂γ) -
            (∫ x, ouSemigroup t (fun x => f x * f x) x ∂γ) *
              Real.log (∫ x, ouSemigroup t (fun x => f x * f x) x ∂γ)) =
        (∫ x, g x * Real.log (g x) ∂γ) -
          (∫ x, ouSemigroup t g x * Real.log (ouSemigroup t g x) ∂γ)
    rw [h3]
    have h1 : (fun x => f x * f x * Real.log (f x * f x)) =
              (fun x => g x * Real.log (g x)) := by
      ext x; show f x * f x * Real.log (f x * f x) = g x * Real.log (g x)
      simp [g, sq]
    have h1b : (fun x => f x * f x) = (fun x => g x) := h2
    rw [h1, h1b]
    -- (∫ g) log(∫ g) = (∫ P_t g) log(∫ P_t g) by mean preservation.
    rw [h_mean]
    ring
  rw [hEntropy_diff]
  -- Goal: H(g) - H(P_t g) ≤ 2(1-e^{-2t}) E(f,f)  where H = boltzmannEntropy.
  -- The strategy: for each ε > 0, build g_ε = g + ε = f² + ε, prove
  --   H(g_ε) - H(P_t g_ε) ≤ 2(1-e^{-2t}) E(f,f)  (Step A: FTC + A1 + A2)
  -- Then take ε → 0 (Step B: DCT) to get the inequality for g.
  -- ============================================================
  -- Per-ε bound H(g_ε) - H(P_t g_ε) ≤ 2(1-e^{-2t}) E(f,f).
  -- ============================================================
  -- We package this as a `have` parameterized by ε.
  have h_perEps : ∀ ε : ℝ, 0 < ε →
      (∫ x, (g x + ε) * Real.log (g x + ε) ∂γ) -
        (∫ x, (ouSemigroup t g x + ε) * Real.log (ouSemigroup t g x + ε) ∂γ) ≤
      (1 - Real.exp (-2 * 1 * t)) * (2 / 1) * Ef := by
    intro ε hε
    -- Build the regularized square g_ε = f² + ε via the RegularizedSquare structure.
    -- We use the structure to extract the four key facts (C¹, lo, hi, deriv_bd).
    set g_ε : ℝ → ℝ := (regularizedSquare hf_core hM hε).toFun with hg_ε_def
    have hg_ε_eq : g_ε = fun x => g x + ε := by
      show (regularizedSquare hf_core hM hε).toFun = fun x => g x + ε
      ext x
      show f x ^ 2 + ε = g x + ε
      rfl
    have hg_ε_eq_sq : g_ε = fun x => f x ^ 2 + ε := by
      show (regularizedSquare hf_core hM hε).toFun = fun x => f x ^ 2 + ε
      rfl
    -- A pointwise uniform M' bound covering both g_ε ≤ M² + ε and |g_ε'| ≤ 2M².
    set M' : ℝ := max (M ^ 2 + ε) (2 * M ^ 2) with hM'_def
    have hM'_ge_hi : M ^ 2 + ε ≤ M' := le_max_left _ _
    have hM'_ge_deriv : 2 * M ^ 2 ≤ M' := le_max_right _ _
    have hM'_nn : 0 ≤ M' := by
      have : 0 ≤ 2 * M ^ 2 := by positivity
      linarith
    -- Lift the RegularizedSquare data to use M' uniformly.
    have hg_ε_C1 : ContDiff ℝ 1 g_ε := (regularizedSquare hf_core hM hε).contDiff
    have hg_ε_lo : ∀ x, ε ≤ g_ε x := (regularizedSquare hf_core hM hε).lo
    have hg_ε_hi : ∀ x, g_ε x ≤ M' := fun x =>
      ((regularizedSquare hf_core hM hε).hi x).trans hM'_ge_hi
    have hg_ε_deriv_bd : ∀ x, |deriv g_ε x| ≤ M' := fun x =>
      ((regularizedSquare hf_core hM hε).deriv_bd x).trans hM'_ge_deriv
    -- The function `H_ε(s) := H(P_s g_ε)`.
    set Hε : ℝ → ℝ := fun s => boltzmannEntropy (ouSemigroup s g_ε) with hHε_def
    -- The Fisher information `I(g_ε)`.
    set Iε : ℝ := fisherInfo g_ε with hIε_def
    -- Derivative of H_ε on Ioi 0: by A2, (d/ds) H_ε(s) = -I(P_s g_ε).
    -- For the FTC inequality we use HasDerivWithinAt on Ioi.
    have hHε_deriv_pos : ∀ s ∈ Set.Ioo 0 t,
        HasDerivWithinAt Hε (-fisherInfo (ouSemigroup s g_ε)) (Set.Ioi s) s := by
      intro s hs
      have h_pos : 0 < s := hs.1
      have h := hasDerivAt_entropy_ouSemigroup g_ε hg_ε_C1 hε hg_ε_lo hg_ε_hi
        hg_ε_deriv_bd h_pos
      exact h.hasDerivWithinAt
    -- Boundary at 0: H_ε right-derivative at 0 is -I(g_ε).
    have hHε_deriv_zero : HasDerivWithinAt Hε (-Iε) (Set.Ici 0) 0 := by
      have h := hasDerivWithinAt_entropy_ouSemigroup_zero g_ε hg_ε_C1 hε
        hg_ε_lo hg_ε_hi hg_ε_deriv_bd
      exact h
    -- Continuity of H_ε on Icc 0 t.
    have hHε_cont : ContinuousOn Hε (Set.Icc 0 t) := by
      intro s hs
      rcases lt_or_eq_of_le hs.1 with hs_pos | hs_zero
      · -- s > 0 case: H_ε is differentiable there.
        have h := hasDerivAt_entropy_ouSemigroup g_ε hg_ε_C1 hε hg_ε_lo hg_ε_hi
          hg_ε_deriv_bd hs_pos
        have hd : HasDerivWithinAt Hε
            (-fisherInfo (ouSemigroup s g_ε)) (Set.Icc 0 t) s := h.hasDerivWithinAt
        exact hd.continuousWithinAt
      · -- s = 0 case: use the right-derivative.
        have hs_eq : s = 0 := hs_zero.symm
        subst hs_eq
        have h := hHε_deriv_zero
        exact h.continuousWithinAt.mono (fun x hx => hx.1)
    -- Pointwise inequality: -e^{-2s} · I(g_ε) ≤ -I(P_s g_ε) for s ∈ Ioo 0 t.
    have h_fisher_le : ∀ s, 0 ≤ s → fisherInfo (ouSemigroup s g_ε) ≤
        Real.exp (-2 * s) * Iε := by
      intro s hs
      exact ouSemigroup_fisher_info_decay g_ε hg_ε_C1 hε hg_ε_lo hg_ε_hi
        hg_ε_deriv_bd s hs
    have h_ineq_pointwise : ∀ s ∈ Set.Ioo 0 t,
        -Real.exp (-2 * s) * Iε ≤ -fisherInfo (ouSemigroup s g_ε) := by
      intro s hs
      have h_pos : 0 ≤ s := hs.1.le
      have hfish := h_fisher_le s h_pos
      linarith
    -- φ(s) := -e^{-2s} · I(g_ε), continuous, hence integrable on Icc 0 t.
    set φ : ℝ → ℝ := fun s => -Real.exp (-2 * s) * Iε with hφ_def
    have hφ_cont : Continuous φ := by
      show Continuous (fun s => -Real.exp (-2 * s) * Iε)
      fun_prop
    have hφ_int : MeasureTheory.IntegrableOn φ (Set.Icc 0 t) :=
      hφ_cont.continuousOn.integrableOn_Icc
    -- FTC inequality: ∫₀ᵗ φ s ds ≤ H_ε(t) - H_ε(0).
    have hFTC : ∫ s in (0)..t, φ s ≤ Hε t - Hε 0 := by
      refine intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le ht hHε_cont ?_
        hφ_int h_ineq_pointwise
      intro s hs
      have h := hHε_deriv_pos s hs
      exact h
    -- Compute ∫₀ᵗ -e^{-2s} · I(g_ε) ds = I(g_ε) · (e^{-2t} - 1) / 2.
    have hderiv_exp : ∀ s : ℝ,
        HasDerivAt (fun u : ℝ => Real.exp (-2 * u) / 2) (-Real.exp (-2 * s)) s := by
      intro s
      have h1 : HasDerivAt (fun u : ℝ => -2 * u) (-2 : ℝ) s := by
        simpa using (hasDerivAt_id s).const_mul (-2 : ℝ)
      have h2 : HasDerivAt (fun u : ℝ => Real.exp (-2 * u))
          (Real.exp (-2 * s) * (-2)) s :=
        (Real.hasDerivAt_exp (-2 * s)).comp s h1
      have h3 : HasDerivAt (fun u : ℝ => Real.exp (-2 * u) / 2)
          (Real.exp (-2 * s) * (-2) / 2) s := h2.div_const 2
      convert h3 using 1; ring
    have hint_phi : ∫ s in (0)..t, -Real.exp (-2 * s) =
        Real.exp (-2 * t) / 2 - Real.exp (-2 * 0) / 2 := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u => Real.exp (-2 * u) / 2)
        (f' := fun u => -Real.exp (-2 * u))
        (a := 0) (b := t) (fun s _ => hderiv_exp s)
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).neg.intervalIntegrable 0 t)
      exact this
    have hint_phi_simp : ∫ s in (0)..t, -Real.exp (-2 * s) =
        (Real.exp (-2 * t) - 1) / 2 := by
      rw [hint_phi]; have : Real.exp (-2 * 0) = 1 := by simp
      rw [this]; ring
    have hint_φ : ∫ s in (0)..t, φ s = Iε * ((Real.exp (-2 * t) - 1) / 2) := by
      show ∫ s in (0)..t, -Real.exp (-2 * s) * Iε = Iε * ((Real.exp (-2 * t) - 1) / 2)
      rw [intervalIntegral.integral_mul_const, hint_phi_simp]
      ring
    rw [hint_φ] at hFTC
    -- hFTC: Iε · (e^{-2t} - 1) / 2 ≤ Hε(t) - Hε(0)
    -- We want: Hε(0) - Hε(t) ≤ Iε · (1 - e^{-2t}) / 2.
    -- (Then bound by 4 E(f,f) using I(g_ε) ≤ 4 E(f,f).)
    -- Hε(0) = H(g_ε) since P_0 g_ε = g_ε.
    have hHε_0 : Hε 0 = boltzmannEntropy g_ε := by
      show boltzmannEntropy (ouSemigroup 0 g_ε) = boltzmannEntropy g_ε
      rw [ouSemigroup_zero]
    -- Hε(t) = boltzmannEntropy (ouSemigroup t g_ε)
    have hHε_t_eq : Hε t = boltzmannEntropy (ouSemigroup t g_ε) := rfl
    rw [hHε_0, hHε_t_eq] at hFTC
    -- Convert boltzmannEntropy g_ε to integrals over `g + ε`.
    have hbE_g_ε : boltzmannEntropy g_ε = ∫ x, (g x + ε) * Real.log (g x + ε) ∂γ := by
      show ∫ x, g_ε x * Real.log (g_ε x) ∂γ = ∫ x, (g x + ε) * Real.log (g x + ε) ∂γ
      apply integral_congr_ae
      filter_upwards with x
      show g_ε x * Real.log (g_ε x) = (g x + ε) * Real.log (g x + ε)
      rfl
    have hbE_Pt_g_ε : boltzmannEntropy (ouSemigroup t g_ε) =
        ∫ x, (ouSemigroup t g x + ε) * Real.log (ouSemigroup t g x + ε) ∂γ := by
      show ∫ x, ouSemigroup t g_ε x * Real.log (ouSemigroup t g_ε x) ∂γ =
        ∫ x, (ouSemigroup t g x + ε) * Real.log (ouSemigroup t g x + ε) ∂γ
      have h_eq : ouSemigroup t g_ε = fun x => ouSemigroup t g x + ε := by
        have := ouSemigroup_sq_add_const hf_core ε t ht
        exact this
      rw [h_eq]
    rw [hbE_g_ε, hbE_Pt_g_ε] at hFTC
    -- Now bound Iε ≤ 4 * E(f, f).
    -- I(g_ε) = ∫ (g_ε')² / g_ε dγ.
    -- g_ε' = 2 f f' so (g_ε')² = 4 f² (f')², and g_ε = f² + ε ≥ f², so
    -- (g_ε')² / g_ε = 4 f² (f')² / (f² + ε) ≤ 4 (f')². Integrating, I(g_ε) ≤ 4 E(f,f).
    have hI_le : Iε ≤ 4 * Ef := by
      show fisherInfo g_ε ≤ 4 * Ef
      -- Pointwise: (deriv g_ε x)² / g_ε x ≤ 4 * (deriv f x)².
      have hg_ε_diff : Differentiable ℝ g_ε := hg_ε_C1.differentiable (by simp)
      have hf_diff : Differentiable ℝ f := hf_core.differentiable
      have hf'_diff : Differentiable ℝ (deriv f) := hf_core.differentiable_deriv
      -- Compute deriv g_ε x = 2 * f x * deriv f x.
      have h_deriv_g_ε : ∀ x, deriv g_ε x = 2 * f x * deriv f x := by
        intro x
        have hf_deriv : HasDerivAt f (deriv f x) x := (hf_diff x).hasDerivAt
        have hf_sq : HasDerivAt (fun y => f y ^ 2) (2 * f x ^ 1 * deriv f x) x := by
          convert hf_deriv.pow 2 using 1
        have h := hf_sq.add_const ε
        have := h.deriv
        show deriv g_ε x = 2 * f x * deriv f x
        rw [show g_ε = (fun y => f y ^ 2 + ε) from rfl]
        rw [this]; ring
      -- Pointwise bound.
      have h_ptwise : ∀ x, (deriv g_ε x) ^ 2 / g_ε x ≤ 4 * (deriv f x) ^ 2 := by
        intro x
        rw [h_deriv_g_ε x]
        have h_pos : 0 < g_ε x := lt_of_lt_of_le hε (hg_ε_lo x)
        have h_pos_ne : g_ε x ≠ 0 := ne_of_gt h_pos
        -- (2 f f')² / (f² + ε) ≤ 4 (f')².
        -- Rewrite (2 f f')² = 4 f² (f')².
        have h_num : (2 * f x * deriv f x) ^ 2 = 4 * f x ^ 2 * (deriv f x) ^ 2 := by ring
        rw [h_num]
        -- Want: 4 * f x ^ 2 * (deriv f x) ^ 2 / g_ε x ≤ 4 * (deriv f x) ^ 2.
        -- This is equivalent to f x ^ 2 / g_ε x ≤ 1 multiplied by 4 (deriv f x)² ≥ 0.
        have h_frac : f x ^ 2 / g_ε x ≤ 1 := by
          rw [div_le_one h_pos]
          show f x ^ 2 ≤ f x ^ 2 + ε
          linarith
        have h_df_sq_nn : 0 ≤ (deriv f x) ^ 2 := sq_nonneg _
        have h_fxsq_nn : 0 ≤ f x ^ 2 := sq_nonneg _
        have hmul_nn : 0 ≤ 4 * (deriv f x) ^ 2 := by positivity
        have h_rewrite : 4 * f x ^ 2 * (deriv f x) ^ 2 / g_ε x =
            (f x ^ 2 / g_ε x) * (4 * (deriv f x) ^ 2) := by
          field_simp
        rw [h_rewrite]
        calc (f x ^ 2 / g_ε x) * (4 * (deriv f x) ^ 2)
            ≤ 1 * (4 * (deriv f x) ^ 2) :=
              mul_le_mul_of_nonneg_right h_frac hmul_nn
          _ = 4 * (deriv f x) ^ 2 := one_mul _
      -- Now integrate the pointwise bound.
      have h_int_lhs : Integrable (fun x => (deriv g_ε x) ^ 2 / g_ε x) γ := by
        -- The numerator (deriv g_ε)² is bounded (by (M')² = max(M²+ε, 2M²)²) and the
        -- denominator g_ε ≥ ε > 0. So integrand bounded by (M')²/ε; constants are integrable.
        refine Integrable.mono' (integrable_const ((M' ^ 2) / ε))
          ?_ ?_
        · -- Measurability: g_ε is continuous (C¹), so its derivative is measurable.
          have h_deriv_cont : Continuous (deriv g_ε) := hg_ε_C1.continuous_deriv (by norm_num)
          have h_deriv_meas : Measurable (deriv g_ε) := h_deriv_cont.measurable
          have h_g_ε_cont : Continuous g_ε := hg_ε_C1.continuous
          have h_g_ε_meas : Measurable g_ε := h_g_ε_cont.measurable
          exact ((h_deriv_meas.pow_const 2).div h_g_ε_meas).aestronglyMeasurable
        · filter_upwards with x
          have h_pos : 0 < g_ε x := lt_of_lt_of_le hε (hg_ε_lo x)
          have h_num_bd : (deriv g_ε x) ^ 2 ≤ M' ^ 2 := by
            have := hg_ε_deriv_bd x
            have hnn : 0 ≤ |deriv g_ε x| := abs_nonneg _
            have h_sq : (deriv g_ε x) ^ 2 = |deriv g_ε x| ^ 2 := (sq_abs _).symm
            rw [h_sq]
            nlinarith
          have h_num_nn : 0 ≤ (deriv g_ε x) ^ 2 := sq_nonneg _
          have h_ratio_nn : 0 ≤ (deriv g_ε x) ^ 2 / g_ε x :=
            div_nonneg h_num_nn h_pos.le
          rw [Real.norm_eq_abs, abs_of_nonneg h_ratio_nn]
          have h_eps_le : ε ≤ g_ε x := hg_ε_lo x
          calc (deriv g_ε x) ^ 2 / g_ε x
              ≤ M' ^ 2 / g_ε x :=
                div_le_div_of_nonneg_right h_num_bd h_pos.le |>.trans (le_refl _)
            _ ≤ M' ^ 2 / ε := by
                apply div_le_div_of_nonneg_left (by positivity) hε h_eps_le
      have h_int_rhs : Integrable (fun x => 4 * (deriv f x) ^ 2) γ := by
        have h_df_meas : Measurable (deriv f) :=
          (h_smooth.continuous_deriv (by simp : ((1 : WithTop ℕ∞)) ≤ ∞)).measurable
        have h_df_bd : ∀ x, |deriv f x| ≤ M := hf'_le
        refine Integrable.mono' (integrable_const (4 * M ^ 2)) ?_ ?_
        · exact ((h_df_meas.pow_const 2).const_mul 4).aestronglyMeasurable
        · filter_upwards with x
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * (deriv f x) ^ 2)]
          have hbd : (deriv f x) ^ 2 ≤ M ^ 2 := by
            have := hf'_le x
            have hnn : 0 ≤ |deriv f x| := abs_nonneg _
            have h_sq : (deriv f x) ^ 2 = |deriv f x| ^ 2 := (sq_abs _).symm
            rw [h_sq]; nlinarith
          linarith
      -- Use integral_mono.
      have h_int_mono := integral_mono h_int_lhs h_int_rhs h_ptwise
      -- ∫ 4 (deriv f)² = 4 ∫ (deriv f)² = 4 E(f, f).
      have h_int_4 : ∫ x, 4 * (deriv f x) ^ 2 ∂γ = 4 * Ef := by
        rw [integral_const_mul]
        congr 1
        show ∫ x, (deriv f x) ^ 2 ∂γ = ouEnergy f f
        unfold ouEnergy
        refine integral_congr_ae ?_
        filter_upwards with x; show (deriv f x) ^ 2 = deriv f x * deriv f x; ring
      show fisherInfo g_ε ≤ 4 * Ef
      unfold fisherInfo
      rw [← h_int_4]
      exact h_int_mono
    -- Combine FTC with the Fisher info bound.
    -- hFTC: Iε · (e^{-2t} - 1) / 2 ≤ ∫(g+ε)log(g+ε) - ∫(P_t g+ε)log(...)... wait
    -- Actually hFTC says Iε * ((exp(-2t) - 1) / 2) ≤ Hε(t) - Hε(0)
    --   = ∫ (Pg+ε) log(Pg+ε) - ∫ (g+ε) log(g+ε).
    -- We want: ∫(g+ε)log(g+ε) - ∫(Pg+ε)log(Pg+ε) ≤ (1 - e^{-2*1*t}) * (2/1) * Ef
    --   = 2(1 - e^{-2t}) Ef.
    -- From hFTC: -(Hε(t) - Hε(0)) ≤ -Iε * ((exp(-2t)-1)/2) = Iε * ((1-exp(-2t))/2).
    -- i.e., Hε(0) - Hε(t) ≤ Iε * ((1 - exp(-2t)) / 2).
    -- We have hI_le: Iε ≤ 4 Ef. The factor (1 - exp(-2t))/2 ≥ 0 since 0 ≤ t.
    have h_factor_nn : 0 ≤ (1 - Real.exp (-2 * t)) / 2 := by
      have h_exp_le : Real.exp (-2 * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      linarith
    have h_bound :
        ((∫ x, (g x + ε) * Real.log (g x + ε) ∂γ) -
          (∫ x, (ouSemigroup t g x + ε) * Real.log (ouSemigroup t g x + ε) ∂γ)) ≤
        Iε * ((1 - Real.exp (-2 * t)) / 2) := by
      have h := hFTC
      -- h: Iε * ((exp(-2t) - 1) / 2) ≤ ∫(Pg+ε)log(Pg+ε) - ∫(g+ε)log(g+ε)
      linarith
    have h_final : Iε * ((1 - Real.exp (-2 * t)) / 2) ≤ 4 * Ef * ((1 - Real.exp (-2 * t)) / 2) :=
      mul_le_mul_of_nonneg_right hI_le h_factor_nn
    have h_rw : 4 * Ef * ((1 - Real.exp (-2 * t)) / 2) =
        (1 - Real.exp (-2 * 1 * t)) * (2 / 1) * Ef := by
      have he : Real.exp (-2 * 1 * t) = Real.exp (-2 * t) := by congr 1; ring
      rw [he]; ring
    linarith [h_rw, h_final, h_bound]
  -- ============================================================
  -- ε → 0 limit (DCT).
  -- ============================================================
  -- Define `F : ℝ → ℝ` by `F ε := lhs(ε) - 2(1-e^{-2t}) E(f,f)`. We have `F ε ≤ 0`
  -- for all `ε > 0` by `h_perEps`. Taking `ε → 0+`, by DCT the integrals converge to
  -- their `g`-values (since `s log s` is continuous on `[0, M²+1]`, hence bounded).
  -- The limit gives the desired inequality.
  -- We make this precise by showing the LHS at ε = 0 is the limit of the ε-LHS.
  -- Pick ε_n = 1/(n+1) tending to 0 and use DCT.
  -- ---
  -- Pointwise convergence: ∀ x, (g x + ε) log(g x + ε) → g x log(g x) as ε → 0+.
  have h_log_cont : Continuous (fun s => s * Real.log s) := Real.continuous_mul_log
  -- Dominator: |s log s| ≤ B on [0, M² + 1] for some B.
  have h_M2_p1_nn : (0 : ℝ) ≤ M ^ 2 + 1 := by positivity
  obtain ⟨B, hB_nn, hB⟩ := exists_mul_log_bound (M ^ 2 + 1) h_M2_p1_nn
  -- Tendsto: as ε → 0+ over Ioi 0, the integrals tend to the un-regularized integrals.
  -- We work with the filter `nhdsWithin 0 (Set.Ioi 0)` for ε.
  -- LHS(ε) := ∫ (g+ε) log(g+ε) dγ - ∫ (P_t g + ε) log(P_t g + ε) dγ.
  -- LHS(0) := ∫ g log g dγ - ∫ P_t g · log(P_t g) dγ (which is the goal LHS).
  -- We show: Tendsto LHS(ε) (𝓝[>] 0) (𝓝 LHS(0)).
  -- ∫ (g+ε) log(g+ε) → ∫ g log g.
  have h_meas_log_g : Measurable (fun x => g x * Real.log (g x)) :=
    hg_meas.mul (Real.measurable_log.comp hg_meas)
  have h_Ptg_meas : Measurable (ouSemigroup t g) := by
    -- P_t g(x) is a parametric integral of a measurable function.
    have hjoint_meas : Measurable
        (fun p : ℝ × ℝ => g (Real.exp (-t) * p.1 +
          Real.sqrt (1 - Real.exp (-2 * t)) * p.2)) :=
      hg_meas.comp ((measurable_const.mul measurable_fst).add
        (measurable_const.mul measurable_snd))
    exact (hjoint_meas.stronglyMeasurable.integral_prod_right').measurable
  have h_meas_log_Ptg : Measurable (fun x => ouSemigroup t g x * Real.log (ouSemigroup t g x)) :=
    h_Ptg_meas.mul (Real.measurable_log.comp h_Ptg_meas)
  -- Bounded for ε ∈ (0, 1].
  -- Tendsto for the first integral.
  have h_lim_g : Tendsto (fun ε : ℝ => ∫ x, (g x + ε) * Real.log (g x + ε) ∂γ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x, g x * Real.log (g x) ∂γ)) := by
    -- We apply DCT via `tendsto_integral_filter_of_dominated_convergence`.
    -- The dominator function: const B (γ-integrable since γ is a probability).
    -- Pointwise: (g x + ε)log(g x + ε) → g x · log(g x) as ε → 0.
    -- Bound: For ε ∈ (0, 1], g x + ε ∈ [0, M² + 1], so |(g x + ε) log(g x + ε)| ≤ B.
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B) ?_ ?_ (integrable_const _) ?_
    · -- AEStronglyMeasurable.
      filter_upwards [self_mem_nhdsWithin] with ε hε_pos
      have h_meas_eps : Measurable (fun x => (g x + ε) * Real.log (g x + ε)) :=
        (hg_meas.add_const ε).mul (Real.measurable_log.comp (hg_meas.add_const ε))
      exact h_meas_eps.aestronglyMeasurable
    · -- bound: ‖(g x + ε) log(g x + ε)‖ ≤ B for ε ∈ (0, 1].
      filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε_range
      filter_upwards with x
      have h_range : g x + ε ∈ Set.Icc (0 : ℝ) (M ^ 2 + 1) := by
        refine ⟨?_, ?_⟩
        · have hε_pos : 0 < ε := hε_range.1
          linarith [hg_nn x]
        · have hε_le : ε ≤ 1 := le_of_lt hε_range.2
          linarith [hg_bdd x]
      rw [Real.norm_eq_abs]
      exact hB _ h_range
    · -- Pointwise.
      filter_upwards with x
      -- As ε → 0 with ε ∈ Ioi 0, g x + ε → g x.
      have h_tendsto : Tendsto (fun ε : ℝ => g x + ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g x)) := by
        have hh : Tendsto (fun ε : ℝ => g x + ε) (nhds 0) (nhds (g x + 0)) :=
          (tendsto_const_nhds (x := g x)).add tendsto_id
        simpa using hh.mono_left nhdsWithin_le_nhds
      exact (h_log_cont.tendsto (g x)).comp h_tendsto
  -- Tendsto for the second integral.
  have h_lim_Ptg : Tendsto (fun ε : ℝ => ∫ x, (ouSemigroup t g x + ε) *
        Real.log (ouSemigroup t g x + ε) ∂γ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, ouSemigroup t g x * Real.log (ouSemigroup t g x) ∂γ)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B) ?_ ?_ (integrable_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε_pos
      have h_meas_eps : Measurable (fun x => (ouSemigroup t g x + ε) *
          Real.log (ouSemigroup t g x + ε)) :=
        (h_Ptg_meas.add_const ε).mul (Real.measurable_log.comp (h_Ptg_meas.add_const ε))
      exact h_meas_eps.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε_range
      filter_upwards with x
      have h_Ptg := hPg_bdd t ht x
      have h_range : ouSemigroup t g x + ε ∈ Set.Icc (0 : ℝ) (M ^ 2 + 1) := by
        refine ⟨?_, ?_⟩
        · have hε_pos : 0 < ε := hε_range.1
          linarith [h_Ptg.1]
        · have hε_le : ε ≤ 1 := le_of_lt hε_range.2
          linarith [h_Ptg.2]
      rw [Real.norm_eq_abs]
      exact hB _ h_range
    · filter_upwards with x
      have h_tendsto : Tendsto (fun ε : ℝ => ouSemigroup t g x + ε)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (ouSemigroup t g x)) := by
        have hh : Tendsto (fun ε : ℝ => ouSemigroup t g x + ε) (nhds 0)
            (nhds (ouSemigroup t g x + 0)) :=
          (tendsto_const_nhds (x := ouSemigroup t g x)).add tendsto_id
        simpa using hh.mono_left nhdsWithin_le_nhds
      exact (h_log_cont.tendsto (ouSemigroup t g x)).comp h_tendsto
  -- Combine: LHS(ε) tends to (∫g log g - ∫P_t g log P_t g).
  have h_lim_LHS : Tendsto
      (fun ε : ℝ =>
        (∫ x, (g x + ε) * Real.log (g x + ε) ∂γ) -
        (∫ x, (ouSemigroup t g x + ε) * Real.log (ouSemigroup t g x + ε) ∂γ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((∫ x, g x * Real.log (g x) ∂γ) -
             (∫ x, ouSemigroup t g x * Real.log (ouSemigroup t g x) ∂γ))) :=
    h_lim_g.sub h_lim_Ptg
  -- LHS(ε) is bounded above by the constant `(1 - exp(-2*1*t)) * (2/1) * Ef` for ε > 0.
  have h_upper_const :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (∫ x, (g x + ε) * Real.log (g x + ε) ∂γ) -
        (∫ x, (ouSemigroup t g x + ε) * Real.log (ouSemigroup t g x + ε) ∂γ) ≤
        (1 - Real.exp (-2 * 1 * t)) * (2 / 1) * Ef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    exact h_perEps ε hε_pos
  -- Take the limit: the limit ≤ the constant bound.
  have h_limit_le := le_of_tendsto h_lim_LHS h_upper_const
  exact h_limit_le

/-! ## BakryEmerySpace instance (relocated from EuclideanStein.lean)

Moved here so that `semigroup_entropy_sq_decay_bound` can use the
proved theorem `ouSemigroup_entropy_sq_decay_bound_proved` rather than
the original axiom (now deleted from `Euclidean.lean`). -/

/-- The BakryEmerySpace instance for ℝ with standard Gaussian and OU semigroup. -/
@[reducible]
def bakryEmerySpace : BakryEmerySpace ℝ where
  toDirichletSpace := dirichletSpace
  Γ := ouGamma
  Γ_symm := fun f g => by ext x; simp only [ouGamma]; ring
  Γ_nonneg := fun f x => by simp only [ouGamma]; exact mul_self_nonneg _
  energy_eq_integral_Γ := fun f g => by
    simp only [ouGamma]; rfl
  IsCore_mul := by
    rintro f g hf hg
    obtain ⟨hf_smooth, Mf, hfM⟩ := hf
    obtain ⟨hg_smooth, Mg, hgM⟩ := hg
    refine ⟨hf_smooth.mul hg_smooth, ⟨Mf * Mg + 2 * (Mf * Mg) + Mf * Mg, fun x => ?_⟩⟩
    have hf_core : IsCore f := ⟨hf_smooth, Mf, hfM⟩
    have hg_core : IsCore g := ⟨hg_smooth, Mg, hgM⟩
    have hdf := hf_core.differentiable
    have hdg := hg_core.differentiable
    have hdf' := hf_core.differentiable_deriv
    have hdg' := hg_core.differentiable_deriv
    have h1 : ∀ y, deriv (f * g) y = deriv f y * g y + f y * deriv g y := fun y =>
      deriv_mul (hdf y) (hdg y)
    have h2 : deriv (f * g) = fun y => deriv f y * g y + f y * deriv g y := by
      ext y; exact h1 y
    have h3 : deriv (deriv (f * g)) x =
        deriv (deriv f) x * g x + deriv f x * deriv g x +
        (deriv f x * deriv g x + f x * deriv (deriv g) x) := by
      rw [h2]
      have hA : DifferentiableAt ℝ (fun y => deriv f y * g y) x :=
        (hdf' x).mul (hdg x)
      have hB : DifferentiableAt ℝ (fun y => f y * deriv g y) x :=
        (hdf x).mul (hdg' x)
      rw [deriv_fun_add hA hB]
      congr 1
      · exact deriv_fun_mul (hdf' x) (hdg x)
      · exact deriv_fun_mul (hdf x) (hdg' x)
    have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (hfM 0).1
    have hMg_nn : 0 ≤ Mg := (norm_nonneg _).trans (hgM 0).1
    refine ⟨?_, ?_, ?_⟩
    · show ‖f x * g x‖ ≤ Mf * Mg + 2 * (Mf * Mg) + Mf * Mg
      have : ‖f x * g x‖ ≤ Mf * Mg := by
        rw [norm_mul]
        exact mul_le_mul (hfM x).1 (hgM x).1 (norm_nonneg _) hMf_nn
      nlinarith
    · rw [h1]
      have h_le : ‖deriv f x * g x + f x * deriv g x‖ ≤ Mf * Mg + Mf * Mg := by
        calc ‖deriv f x * g x + f x * deriv g x‖
            ≤ ‖deriv f x * g x‖ + ‖f x * deriv g x‖ := norm_add_le _ _
          _ = ‖deriv f x‖ * ‖g x‖ + ‖f x‖ * ‖deriv g x‖ := by rw [norm_mul, norm_mul]
          _ ≤ Mf * Mg + Mf * Mg := by
              gcongr
              · exact (hfM x).2.1
              · exact (hgM x).1
              · exact (hfM x).1
              · exact (hgM x).2.1
      nlinarith
    · rw [h3]
      have h_le : ‖deriv (deriv f) x * g x + deriv f x * deriv g x +
            (deriv f x * deriv g x + f x * deriv (deriv g) x)‖
          ≤ Mf * Mg + 2 * (Mf * Mg) + Mf * Mg := by
        have e1 : ‖deriv (deriv f) x * g x‖ ≤ Mf * Mg := by
          rw [norm_mul]; exact mul_le_mul (hfM x).2.2 (hgM x).1 (norm_nonneg _) hMf_nn
        have e2 : ‖deriv f x * deriv g x‖ ≤ Mf * Mg := by
          rw [norm_mul]; exact mul_le_mul (hfM x).2.1 (hgM x).2.1 (norm_nonneg _) hMf_nn
        have e3 : ‖f x * deriv (deriv g) x‖ ≤ Mf * Mg := by
          rw [norm_mul]; exact mul_le_mul (hfM x).1 (hgM x).2.2 (norm_nonneg _) hMf_nn
        calc ‖deriv (deriv f) x * g x + deriv f x * deriv g x +
                (deriv f x * deriv g x + f x * deriv (deriv g) x)‖
            ≤ ‖deriv (deriv f) x * g x‖ + ‖deriv f x * deriv g x‖ +
                (‖deriv f x * deriv g x‖ + ‖f x * deriv (deriv g) x‖) := by
              exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
          _ ≤ Mf * Mg + Mf * Mg + (Mf * Mg + Mf * Mg) := by
              gcongr
          _ = Mf * Mg + 2 * (Mf * Mg) + Mf * Mg := by ring
      exact h_le
  IsCore_semigroup := fun t ht _ hf => ouSemigroup_preserves_IsCore t ht hf
  Γ_leibniz := fun f g h hf hg _ x => by
    simp only [ouGamma]
    have hdf : DifferentiableAt ℝ f x := hf.differentiable.differentiableAt
    have hdg : DifferentiableAt ℝ g x := hg.differentiable.differentiableAt
    have : deriv (f * g) x = deriv f x * g x + f x * deriv g x := deriv_mul hdf hdg
    rw [this]; ring
  Γ_const := fun c f => by
    ext x; simp only [ouGamma, deriv_const, Pi.zero_apply]; ring
  semigroup := ouSemigroup
  ρ := 1
  hρ := one_pos
  gradient_decay := fun f t ht hf => by
    show ∫ x, ouGamma (ouSemigroup t f) (ouSemigroup t f) x ∂γ ≤
        Real.exp (-2 * 1 * t) * ∫ x, ouGamma f f x ∂γ
    simpa [ouGamma] using ouSemigroup_gradient_decay f t ht hf
  semigroup_zero := fun f => by
    ext x
    simp only [ouSemigroup, neg_zero, exp_zero, mul_zero, sub_self, sqrt_zero,
               zero_mul, add_zero, one_mul]
    simp [integral_const]
  semigroup_add := fun s t _ hs ht hf => ouSemigroup_compose s t hs ht hf
  semigroup_contraction := fun f t ht hf_core => by
    set a := exp (-t)
    set b := sqrt (1 - exp (-2 * t))
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ : Measurable φ := Measurable.add
      (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)
    have hmap := ou_kernel_map t ht
    have hf_meas : Measurable f := hf_core.measurable
    have hf_cont : Continuous f := hf_core.continuous
    obtain ⟨M, hM⟩ := hf_core.bounded
    have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
    have hf2_int : Integrable (fun x => f x ^ 2) γ := by
      refine Integrable.mono' (integrable_const (M^2))
        ((hf_meas.pow_const 2).aemeasurable.aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 : |f x| ≤ M := by rw [← Real.norm_eq_abs]; exact hM x
      have h2 : (f x)^2 ≤ M^2 := by
        have : |f x|^2 ≤ M^2 := by nlinarith [abs_nonneg (f x)]
        rwa [sq_abs] at this
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have : ‖M^2‖ = M^2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      linarith
    have hf2_φ_int : Integrable (fun p => (f (φ p))^2) (γ.prod γ) := by
      have hlaw : HasLaw φ γ (γ.prod γ) := ⟨hφ.aemeasurable, hmap⟩
      have hf2_aesm : AEStronglyMeasurable (fun x => f x ^ 2) ((γ.prod γ).map φ) := by
        rw [hmap]; exact (hf_meas.pow_const 2).aestronglyMeasurable
      have hf2_int' : Integrable (fun x => f x ^ 2) ((γ.prod γ).map φ) := by
        rw [hmap]; exact hf2_int
      exact (integrable_map_measure hf2_aesm hφ.aemeasurable).mp hf2_int'
    have hfφ_int : ∀ x, Integrable (fun y => f (a * x + b * y)) γ := by
      intro x
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hf_meas.comp (measurable_const.add (measurable_const.mul measurable_id')))
          |>.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun y => (hM (a*x + b*y)))
    have h_convex : ConvexOn ℝ Set.univ (fun x : ℝ => x^2) :=
      Even.convexOn_pow (Nat.even_iff.mpr rfl)
    have h_cont : ContinuousOn (fun x : ℝ => x^2) Set.univ :=
      (continuous_pow 2).continuousOn
    have h_closed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
    have hJensen : ∀ x, (∫ y, f (a*x + b*y) ∂γ)^2 ≤ ∫ y, (f (a*x + b*y))^2 ∂γ := by
      intro x
      have hfφ_aesm : ∀ᵐ y ∂γ, f (a*x + b*y) ∈ (Set.univ : Set ℝ) :=
        Filter.Eventually.of_forall (fun y => Set.mem_univ _)
      have hfφ2_int : Integrable (fun y => (f (a*x + b*y))^2) γ := by
        refine Integrable.mono' (integrable_const (M^2)) ?_ ?_
        · exact ((hf_meas.comp (measurable_const.add (measurable_const.mul measurable_id')))
            |>.pow_const 2).aestronglyMeasurable
        · refine Filter.Eventually.of_forall (fun y => ?_)
          have hnn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have h1 : |f (a*x + b*y)| ≤ M := by
            rw [← Real.norm_eq_abs]; exact hM (a*x + b*y)
          have h2 : (f (a*x + b*y))^2 ≤ M^2 := by
            have : |f (a*x + b*y)|^2 ≤ M^2 := by nlinarith [abs_nonneg (f (a*x + b*y))]
            rwa [sq_abs] at this
          have : ‖M^2‖ = M^2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          linarith
      exact ConvexOn.map_integral_le h_convex h_cont h_closed hfφ_aesm (hfφ_int x) hfφ2_int
    show ∫ x, (ouSemigroup t f x) ^ 2 ∂γ ≤ ∫ x, (f x) ^ 2 ∂γ
    simp only [ouSemigroup]
    calc ∫ x, (∫ y, f (a * x + b * y) ∂γ) ^ 2 ∂γ
        ≤ ∫ x, ∫ y, (f (a*x + b*y))^2 ∂γ ∂γ := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
          · exact hf2_φ_int.integral_prod_left
          · exact Filter.Eventually.of_forall hJensen
      _ = ∫ p, (f (φ p))^2 ∂(γ.prod γ) := (integral_prod _ hf2_φ_int).symm
      _ = ∫ x, (f x)^2 ∂γ := by
          have hlaw : HasLaw φ γ (γ.prod γ) := ⟨hφ.aemeasurable, hmap⟩
          exact hlaw.integral_comp (hf_meas.pow_const 2).aestronglyMeasurable
  semigroup_mean := fun f t ht hf_core => by
    show ∫ x, ouSemigroup t f x ∂γ = ∫ x, f x ∂γ
    simp only [ouSemigroup]
    set a := exp (-t)
    set b := sqrt (1 - exp (-2 * t))
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ : Measurable φ := Measurable.add
      (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)
    have hmap := ou_kernel_map t ht
    have hlaw : HasLaw φ γ (γ.prod γ) := ⟨hφ.aemeasurable, hmap⟩
    have hf : AEStronglyMeasurable f γ :=
      hf_core.stronglyMeasurable.aestronglyMeasurable
    have hint : Integrable f γ := hf_core.integrable
    have hcomp : ∫ p, f (φ p) ∂(γ.prod γ) = ∫ x, f x ∂γ :=
      hlaw.integral_comp hf
    rw [← hcomp]
    have hasm' : AEStronglyMeasurable f ((γ.prod γ).map φ) := by rwa [hmap]
    have hint' : Integrable f ((γ.prod γ).map φ) := by rwa [hmap]
    have hfφ : Integrable (f ∘ φ) (γ.prod γ) :=
      (integrable_map_measure hasm' hφ.aemeasurable).mp hint'
    exact (integral_prod (f ∘ φ) hfφ).symm
  semigroup_selfAdjoint := fun f g t ht hf hg => by
    show ∫ x, ouSemigroup t f x * g x ∂γ = ∫ x, f x * ouSemigroup t g x ∂γ
    simp only [ouSemigroup]
    set a := exp (-t)
    set b := sqrt (1 - exp (-2 * t))
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ : Measurable φ := Measurable.add
      (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)
    have hmap := ou_kernel_map t ht
    have hab : a ^ 2 + b ^ 2 = 1 := by
      simp only [a, b]
      rw [sq_sqrt (one_sub_exp_nonneg t ht), sq, ← exp_add,
        show -t + -t = -2 * t from by ring]
      ring
    obtain ⟨Mf, hMf⟩ := hf.bounded
    obtain ⟨Mg, hMg⟩ := hg.bounded
    have hfφ_int : Integrable (fun p => f (φ p)) (γ.prod γ) :=
      Integrable.mono' (integrable_const Mf)
        ((hf.measurable.comp hφ).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => hMf (φ p))
    have hgφ_int : Integrable (fun p => g (φ p)) (γ.prod γ) :=
      Integrable.mono' (integrable_const Mg)
        ((hg.measurable.comp hφ).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => hMg (φ p))
    have hf_fst_int : Integrable (fun p : ℝ × ℝ => f p.1) (γ.prod γ) :=
      Integrable.mono' (integrable_const Mf)
        ((hf.measurable.comp measurable_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => hMf p.1)
    have hMf_nn : 0 ≤ Mf := le_trans (norm_nonneg _) (hMf 0)
    have hMg_nn : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg 0)
    have hfg1_int : Integrable (fun p : ℝ × ℝ => f (φ p) * g p.1) (γ.prod γ) :=
      Integrable.mono' (integrable_const (Mf * Mg))
        (((hf.measurable.comp hφ).mul (hg.measurable.comp measurable_fst)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => by
          rw [norm_mul]; exact mul_le_mul (hMf _) (hMg _) (norm_nonneg _) hMf_nn)
    have hfg2_int : Integrable (fun p : ℝ × ℝ => f p.1 * g (φ p)) (γ.prod γ) :=
      Integrable.mono' (integrable_const (Mf * Mg))
        (((hf.measurable.comp measurable_fst).mul (hg.measurable.comp hφ)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => by
          rw [norm_mul]; exact mul_le_mul (hMf _) (hMg _) (norm_nonneg _) hMf_nn)
    have hLHS : ∫ x, (∫ y, f (a*x + b*y) ∂γ) * g x ∂γ =
        ∫ p, f (φ p) * g p.1 ∂(γ.prod γ) := by
      have h1 : ∫ p, f (φ p) * g p.1 ∂(γ.prod γ) =
          ∫ x, (∫ y, f (a * x + b * y) * g x ∂γ) ∂γ :=
        integral_prod _ hfg1_int
      rw [h1]; congr 1; ext x
      rw [integral_mul_const]
    have hRHS : ∫ x, f x * (∫ y, g (a*x + b*y) ∂γ) ∂γ =
        ∫ p, f p.1 * g (φ p) ∂(γ.prod γ) := by
      have h1 : ∫ p, f p.1 * g (φ p) ∂(γ.prod γ) =
          ∫ x, (∫ y, f x * g (a * x + b * y) ∂γ) ∂γ :=
        integral_prod _ hfg2_int
      rw [h1]; congr 1; ext x
      rw [integral_const_mul]
    rw [hLHS, hRHS]
    set T : ℝ × ℝ → ℝ × ℝ := fun p => (a * p.1 + b * p.2, b * p.1 - a * p.2)
    have hT_φ_to_fst : ∀ p : ℝ × ℝ, φ (T p) = p.1 := by
      intro p; simp only [φ, T]
      have : a * (a * p.1 + b * p.2) + b * (b * p.1 - a * p.2) =
          (a ^ 2 + b ^ 2) * p.1 := by ring
      rw [this, hab, one_mul]
    have hT_fst_to_φ : ∀ p : ℝ × ℝ, (T p).1 = φ p := fun p => rfl
    have hT_preserves : (γ.prod γ).map T = γ.prod γ :=
      gaussian2D_orthogonal_invariance a b hab
    have hT_meas : Measurable T := by
      apply Measurable.prod
      · exact (measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)
      · exact (measurable_const.mul measurable_fst).sub (measurable_const.mul measurable_snd)
    have hfg1_aesm_map : AEStronglyMeasurable (fun p => f (φ p) * g p.1)
        ((γ.prod γ).map T) := by rw [hT_preserves]; exact hfg1_int.aestronglyMeasurable
    calc ∫ p, f (φ p) * g p.1 ∂(γ.prod γ)
        = ∫ p, f (φ (T p)) * g (T p).1 ∂(γ.prod γ) := by
          conv_lhs => rw [← hT_preserves]
          exact integral_map hT_meas.aemeasurable hfg1_aesm_map
      _ = ∫ p, f p.1 * g (φ p) ∂(γ.prod γ) := by
          congr 1; ext p; rw [hT_φ_to_fst, hT_fst_to_φ]
  semigroup_l2_decay_bound := fun f t ht hf =>
    ouSemigroup_l2_decay_bound f t ht hf
  semigroup_l2_sq_hasDerivWithinAt := fun f t ht hf => by
    have h := ouSemigroup_l2_sq_hasDerivWithinAt_proved f t ht hf
    convert h using 1
  semigroup_ergodic := fun f hf => ouSemigroup_ergodic f hf
  semigroup_entropy_sq_decay_bound := fun f t ht hf =>
    ouSemigroup_entropy_sq_decay_bound_proved f t ht hf
  semigroup_entropy_sq_ergodic := fun f hf => ouSemigroup_entropy_sq_ergodic f hf

end Gaussian1D

end
