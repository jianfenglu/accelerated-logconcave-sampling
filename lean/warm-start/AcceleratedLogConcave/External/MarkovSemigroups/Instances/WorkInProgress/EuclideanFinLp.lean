/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lp-valued multivariate Gaussian OU semigroup
-/

import AcceleratedLogConcave.External.MarkovSemigroups.Abstract.Hypercontractivity
import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanFin
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.HasLaw

open MeasureTheory Filter Set Real ProbabilityTheory
open scoped ENNReal Topology InnerProductSpace

-- Port elaboration compatibility only; kernel checking and linters remain enabled.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GaussianFin

variable {n : ℕ}

private theorem gaussian1D_ouSemigroup_pointwise_tendsto_zero_of_bound
    {g : ℝ → ℝ} (hg_cont : Continuous g) {M : ℝ} (hg_bd : ∀ y, |g y| ≤ M) (x : ℝ) :
    Tendsto (fun s => Gaussian1D.ouSemigroup s g x) (𝓝[Ici 0] 0) (𝓝 (g x)) := by
  have h_rewrite : (fun s : ℝ => Gaussian1D.ouSemigroup s g x) =
      fun s => ∫ y, g (Real.exp (-s) * x +
        Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂Gaussian1D.γ := rfl
  rw [h_rewrite]
  have h_target : g x = ∫ _y : ℝ, g x ∂Gaussian1D.γ := by simp
  rw [h_target]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with s _
    exact (hg_cont.comp ((continuous_const.mul continuous_const).add
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s _
    filter_upwards with y
    show ‖g (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y)‖ ≤ M
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

private theorem gaussian1D_pairing_tendsto_atZero_of_bound
    {f g : ℝ → ℝ} (hf_cont : Continuous f) (hg_cont : Continuous g)
    {Mf Mg : ℝ} (hf_bd : ∀ x, |f x| ≤ Mf) (hg_bd : ∀ y, |g y| ≤ Mg) :
    Tendsto (fun s => ∫ x, f x * Gaussian1D.ouSemigroup s g x ∂Gaussian1D.γ)
      (𝓝[Ici 0] 0)
      (𝓝 (∫ x, f x * g x ∂Gaussian1D.γ)) := by
  have hMf_nn : 0 ≤ Mf := (abs_nonneg _).trans (hf_bd 0)
  have hPg_meas : ∀ s, Measurable (Gaussian1D.ouSemigroup s g) := fun s => by
    show Measurable fun x => ∫ y, g (Real.exp (-s) * x +
      Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂Gaussian1D.γ
    apply StronglyMeasurable.measurable
    have h_inner : StronglyMeasurable
        (fun p : ℝ × ℝ => g (Real.exp (-s) * p.1 +
          Real.sqrt (1 - Real.exp (-2 * s)) * p.2)) :=
      (hg_cont.comp ((continuous_const.mul continuous_fst).add
        (continuous_const.mul continuous_snd))).stronglyMeasurable
    exact h_inner.integral_prod_right' (ν := Gaussian1D.γ)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => Mf * Mg) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with s _
    exact ((hf_cont.measurable).mul (hPg_meas s)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s _
    filter_upwards with x
    show ‖f x * Gaussian1D.ouSemigroup s g x‖ ≤ Mf * Mg
    rw [Real.norm_eq_abs, abs_mul]
    have h_int : Integrable (fun y => g (Real.exp (-s) * x +
        Real.sqrt (1 - Real.exp (-2 * s)) * y)) Gaussian1D.γ := by
      refine Integrable.mono' (integrable_const Mg) ?_ ?_
      · exact (hg_cont.comp ((continuous_const.add
          (continuous_const.mul continuous_id)))).aestronglyMeasurable
      · filter_upwards with y
        show ‖g (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y)‖ ≤ Mg
        rw [Real.norm_eq_abs]
        exact hg_bd _
    have hPg : |Gaussian1D.ouSemigroup s g x| ≤ Mg := by
      show |∫ y, g (Real.exp (-s) * x +
        Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂Gaussian1D.γ| ≤ Mg
      calc
        |∫ y, g (Real.exp (-s) * x +
            Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂Gaussian1D.γ|
            ≤ ∫ y, |g (Real.exp (-s) * x +
                Real.sqrt (1 - Real.exp (-2 * s)) * y)| ∂Gaussian1D.γ :=
              abs_integral_le_integral_abs
        _ ≤ ∫ _, Mg ∂Gaussian1D.γ := by
            refine integral_mono h_int.abs (integrable_const _) ?_
            intro y
            exact hg_bd _
        _ = Mg := by simp
    exact mul_le_mul (hf_bd x) hPg (abs_nonneg _) hMf_nn
  · filter_upwards with x
    exact tendsto_const_nhds.mul
      (gaussian1D_ouSemigroup_pointwise_tendsto_zero_of_bound hg_cont hg_bd x)

private theorem gaussian1D_pairing_hasDerivAt_pos
    (t₀ : ℝ) (ht₀ : 0 < t₀) {f g : ℝ → ℝ}
    (hf : Gaussian1D.IsCore f) (hg : Gaussian1D.IsCore g) :
    HasDerivAt (fun s => ∫ x, f x * Gaussian1D.ouSemigroup s g x ∂Gaussian1D.γ)
      (-(∫ x, deriv f x * deriv (Gaussian1D.ouSemigroup t₀ g) x ∂Gaussian1D.γ)) t₀ := by
  obtain ⟨hf_smooth, Mf, hfM⟩ := hf
  obtain ⟨hg_smooth, Mg, hgM⟩ := hg
  have hf_core : Gaussian1D.IsCore f := ⟨hf_smooth, Mf, hfM⟩
  have hg_core : Gaussian1D.IsCore g := ⟨hg_smooth, Mg, hgM⟩
  have hMf_nn : 0 ≤ Mf := (abs_nonneg _).trans (by
    rw [← Real.norm_eq_abs]
    exact (hfM 0).1)
  set ε : ℝ := t₀ / 2 with hε_def
  have hε_pos : 0 < ε := half_pos ht₀
  have hε_lt : ε < t₀ := half_lt_self ht₀
  have h_nbhd : Set.Ioo ε (t₀ + 1) ∈ nhds t₀ := Ioo_mem_nhds hε_lt (by linarith)
  set F : ℝ → ℝ → ℝ := fun s x => f x * Gaussian1D.ouSemigroup s g x
  set F' : ℝ → ℝ → ℝ := fun s x => f x *
    (deriv (deriv (Gaussian1D.ouSemigroup s g)) x -
      x * deriv (Gaussian1D.ouSemigroup s g) x)
  set bound : ℝ → ℝ := fun x => Mf * Mg * (1 + |x|)
  have h_id_int : Integrable (fun x : ℝ => x) Gaussian1D.γ :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have h_bound_int : Integrable bound Gaussian1D.γ := by
    have h_eq : bound = (fun x => Mf * Mg + (Mf * Mg) * |x|) := by
      funext x
      simp [bound]
      ring
    rw [h_eq]
    exact (integrable_const _).add (h_id_int.abs.const_mul _)
  have h_bounds : ∀ s, 0 ≤ s → ∀ x,
      ‖Gaussian1D.ouSemigroup s g x‖ ≤ Mg ∧
      ‖deriv (Gaussian1D.ouSemigroup s g) x‖ ≤ Mg ∧
      ‖deriv (deriv (Gaussian1D.ouSemigroup s g)) x‖ ≤ Mg :=
    fun s hs x => Gaussian1D.ouSemigroup_preserves_bounds hg_smooth hgM s hs x
  have hPsg_meas : ∀ s, 0 ≤ s → Measurable (Gaussian1D.ouSemigroup s g) := fun s hs => by
    exact (Gaussian1D.ouSemigroup_preserves_IsCore s hs hg_core).measurable
  have hF_meas : ∀ s ∈ Set.Ioo ε (t₀ + 1), AEStronglyMeasurable (F s) Gaussian1D.γ := by
    intro s hs
    have hs_pos : 0 < s := lt_of_lt_of_le hε_pos hs.1.le
    exact ((hf_smooth.continuous.measurable).mul (hPsg_meas s hs_pos.le)).aestronglyMeasurable
  have hF_int : Integrable (F t₀) Gaussian1D.γ := by
    refine Integrable.mono' (integrable_const (Mf * Mg)) (hF_meas t₀
      ⟨hε_lt, by linarith⟩) ?_
    filter_upwards with x
    show ‖f x * Gaussian1D.ouSemigroup t₀ g x‖ ≤ Mf * Mg
    rw [Real.norm_eq_abs, abs_mul]
    have hPg : |Gaussian1D.ouSemigroup t₀ g x| ≤ Mg := by
      rw [← Real.norm_eq_abs]
      exact (h_bounds t₀ ht₀.le x).1
    exact mul_le_mul
      (by
        rw [← Real.norm_eq_abs]
        exact (hfM x).1)
      hPg (abs_nonneg _) hMf_nn
  have hF'_meas : AEStronglyMeasurable (F' t₀) Gaussian1D.γ := by
    have hcore_t₀ : Gaussian1D.IsCore (Gaussian1D.ouSemigroup t₀ g) :=
      Gaussian1D.ouSemigroup_preserves_IsCore t₀ ht₀.le hg_core
    have hmeas1 : Measurable (deriv (Gaussian1D.ouSemigroup t₀ g)) := by
      exact (Gaussian1D.IsCore.contDiff_deriv hcore_t₀).continuous.measurable
    have hmeas2 : Measurable (deriv (deriv (Gaussian1D.ouSemigroup t₀ g))) := by
      exact ((Gaussian1D.IsCore.contDiff_deriv hcore_t₀).continuous_deriv (by norm_num)).measurable
    exact ((hf_smooth.continuous.measurable).mul (hmeas2.sub (measurable_id.mul hmeas1))).aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂Gaussian1D.γ, ∀ s ∈ Set.Ioo ε (t₀ + 1), ‖F' s x‖ ≤ bound x := by
    filter_upwards with x s hs
    have hs_nonneg : 0 ≤ s := (lt_of_lt_of_le hε_pos hs.1.le).le
    obtain ⟨hPs, hDPs, hDDPs⟩ := h_bounds s hs_nonneg x
    show ‖f x * (deriv (deriv (Gaussian1D.ouSemigroup s g)) x -
        x * deriv (Gaussian1D.ouSemigroup s g) x)‖ ≤ Mf * Mg * (1 + |x|)
    rw [Real.norm_eq_abs, abs_mul]
    have hf_abs : |f x| ≤ Mf := by
      rw [← Real.norm_eq_abs]
      exact (hfM x).1
    have hL :
        |deriv (deriv (Gaussian1D.ouSemigroup s g)) x -
            x * deriv (Gaussian1D.ouSemigroup s g) x| ≤ Mg * (1 + |x|) := by
      calc
        |deriv (deriv (Gaussian1D.ouSemigroup s g)) x -
            x * deriv (Gaussian1D.ouSemigroup s g) x|
            ≤ |deriv (deriv (Gaussian1D.ouSemigroup s g)) x|
              + |x * deriv (Gaussian1D.ouSemigroup s g) x| := by
                rw [sub_eq_add_neg]
                exact (abs_add_le _ _).trans (by rw [abs_neg])
        _ = |deriv (deriv (Gaussian1D.ouSemigroup s g)) x|
              + |x| * |deriv (Gaussian1D.ouSemigroup s g) x| := by
                rw [abs_mul]
        _ ≤ Mg + |x| * Mg := by
              gcongr
              · rw [← Real.norm_eq_abs]
                exact hDDPs
              · rw [← Real.norm_eq_abs]
                exact hDPs
        _ = Mg * (1 + |x|) := by ring
    calc
      |f x| * |deriv (deriv (Gaussian1D.ouSemigroup s g)) x -
          x * deriv (Gaussian1D.ouSemigroup s g) x|
          ≤ Mf * (Mg * (1 + |x|)) := mul_le_mul hf_abs hL (abs_nonneg _) hMf_nn
      _ = Mf * Mg * (1 + |x|) := by ring
  have h_diff :
      ∀ᵐ x ∂Gaussian1D.γ, ∀ s ∈ Set.Ioo ε (t₀ + 1), HasDerivAt (fun r => F r x) (F' s x) s := by
    filter_upwards with x s hs
    have hs_pos : 0 < s := lt_of_lt_of_le hε_pos hs.1.le
    simpa [F, F'] using
      (Gaussian1D.hasDerivAt_t_ouSemigroup s hs_pos hg_core x).const_mul (f x)
  have hF_meas_ev : ∀ᶠ s in nhds t₀, AEStronglyMeasurable (F s) Gaussian1D.γ :=
    Filter.eventually_of_mem h_nbhd hF_meas
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le h_nbhd
      hF_meas_ev hF_int hF'_meas h_bound h_bound_int h_diff
  have hcore_t₀ : Gaussian1D.IsCore (Gaussian1D.ouSemigroup t₀ g) :=
    Gaussian1D.ouSemigroup_preserves_IsCore t₀ ht₀.le hg_core
  have h_dir :
      ∫ x, f x *
        (deriv (deriv (Gaussian1D.ouSemigroup t₀ g)) x -
          x * deriv (Gaussian1D.ouSemigroup t₀ g) x) ∂Gaussian1D.γ
        = -∫ x, deriv f x * deriv (Gaussian1D.ouSemigroup t₀ g) x ∂Gaussian1D.γ := by
    have hf_bd : ∀ y, |f y| ≤ Mf := by
      intro y
      rw [← Real.norm_eq_abs]
      exact (hfM y).1
    have hf'_bd : ∀ y, |deriv f y| ≤ Mf := by
      intro y
      rw [← Real.norm_eq_abs]
      exact (hfM y).2.1
    have hh_bd : ∀ y, |Gaussian1D.ouSemigroup t₀ g y| ≤ Mg := by
      intro y
      rw [← Real.norm_eq_abs]
      exact (h_bounds t₀ ht₀.le y).1
    have hh'_bd : ∀ y, |deriv (Gaussian1D.ouSemigroup t₀ g) y| ≤ Mg := by
      intro y
      rw [← Real.norm_eq_abs]
      exact (h_bounds t₀ ht₀.le y).2.1
    have hh''_bd : ∀ y, |deriv (deriv (Gaussian1D.ouSemigroup t₀ g)) y| ≤ Mg := by
      intro y
      rw [← Real.norm_eq_abs]
      exact (h_bounds t₀ ht₀.le y).2.2
    have hf_C1 : ContDiff ℝ 1 f := by
      have h : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) := by
        exact WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ by simp)
      exact hf_smooth.of_le h
    have hPtg_C2 : ContDiff ℝ 2 (Gaussian1D.ouSemigroup t₀ g) := by
      have h : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) := by
        exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ by simp)
      exact hcore_t₀.contDiff.of_le h
    simpa using Gaussian1D.gaussian_dirichlet_form_bilinear
      (f := f) (h := Gaussian1D.ouSemigroup t₀ g)
      (hf := hf_C1) hf_bd hf'_bd hPtg_C2 hh_bd hh'_bd hh''_bd
  rw [h_dir] at h_deriv
  simpa using h_deriv

private theorem gaussian1D_pairing_hasDerivWithinAt_zero
    {f g : ℝ → ℝ} (hf : Gaussian1D.IsCore f) (hg : Gaussian1D.IsCore g) :
    HasDerivWithinAt (fun s => ∫ x, f x * Gaussian1D.ouSemigroup s g x ∂Gaussian1D.γ)
      (-(∫ x, deriv f x * deriv g x ∂Gaussian1D.γ)) (Ici 0) 0 := by
  obtain ⟨hf_smooth, Mf, hfM⟩ := hf
  obtain ⟨hg_smooth, Mg, hgM⟩ := hg
  have hf_core : Gaussian1D.IsCore f := ⟨hf_smooth, Mf, hfM⟩
  have hg_core : Gaussian1D.IsCore g := ⟨hg_smooth, Mg, hgM⟩
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
    (f := fun s => ∫ x, f x * Gaussian1D.ouSemigroup s g x ∂Gaussian1D.γ)
    (e := -(∫ x, deriv f x * deriv g x ∂Gaussian1D.γ)) (a := 0) ?_ ?_ self_mem_nhdsWithin ?_
  · intro t ht
    exact (gaussian1D_pairing_hasDerivAt_pos t ht hf_core hg_core).differentiableAt.differentiableWithinAt
  · have hf_bd : ∀ x, |f x| ≤ Mf := by
      intro x
      rw [← Real.norm_eq_abs]
      exact (hfM x).1
    have hg_bd : ∀ y, |g y| ≤ Mg := by
      intro y
      rw [← Real.norm_eq_abs]
      exact (hgM y).1
    have h := gaussian1D_pairing_tendsto_atZero_of_bound hf_smooth.continuous hg_smooth.continuous hf_bd hg_bd
    show ContinuousWithinAt (fun s => ∫ x, f x * Gaussian1D.ouSemigroup s g x ∂Gaussian1D.γ) (Ioi 0) 0
    have h0 :
        ∫ x, f x * Gaussian1D.ouSemigroup 0 g x ∂Gaussian1D.γ = ∫ x, f x * g x ∂Gaussian1D.γ := by
      have hzero : Gaussian1D.ouSemigroup 0 g = g := by
        ext x
        simp [Gaussian1D.ouSemigroup, integral_const]
      rw [hzero]
    rw [ContinuousWithinAt, h0]
    exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  · have hf'_bd : ∀ x, |deriv f x| ≤ Mf := by
      intro x
      rw [← Real.norm_eq_abs]
      exact (hfM x).2.1
    have hg'_bd : ∀ y, |deriv g y| ≤ Mg := by
      intro y
      rw [← Real.norm_eq_abs]
      exact (hgM y).2.1
    have hpair_lim :=
      gaussian1D_pairing_tendsto_atZero_of_bound
        (Gaussian1D.IsCore.contDiff_deriv hf_core).continuous
        (Gaussian1D.IsCore.contDiff_deriv hg_core).continuous
        hf'_bd hg'_bd
    have h_exp_Ici : Tendsto (fun s : ℝ => Real.exp (-s)) (𝓝[Ici 0] 0) (𝓝 1) := by
      have h_cont : Continuous (fun s : ℝ => Real.exp (-s)) := by fun_prop
      have h := h_cont.continuousAt.tendsto (x := (0 : ℝ))
      simpa using h.mono_left nhdsWithin_le_nhds
    have h_exp : Tendsto (fun s : ℝ => Real.exp (-s)) (𝓝[Ioi 0] 0) (𝓝 1) :=
      h_exp_Ici.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have hpair_lim_Ioi :
        Tendsto (fun s => ∫ x, deriv f x * Gaussian1D.ouSemigroup s (deriv g) x ∂Gaussian1D.γ)
          (𝓝[Ioi 0] 0) (𝓝 (∫ x, deriv f x * deriv g x ∂Gaussian1D.γ)) :=
      hpair_lim.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h_mul := h_exp.mul hpair_lim_Ioi
    have htarget :
        Tendsto (fun s =>
          -(Real.exp (-s) * ∫ x, deriv f x * Gaussian1D.ouSemigroup s (deriv g) x ∂Gaussian1D.γ))
          (𝓝[Ioi 0] 0) (𝓝 (-(∫ x, deriv f x * deriv g x ∂Gaussian1D.γ))) := by
      simpa using h_mul.neg
    refine htarget.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hderiv : deriv (fun r => ∫ x, f x * Gaussian1D.ouSemigroup r g x ∂Gaussian1D.γ) s =
        -(Real.exp (-s) * ∫ x, deriv f x * Gaussian1D.ouSemigroup s (deriv g) x ∂Gaussian1D.γ) := by
      rw [(gaussian1D_pairing_hasDerivAt_pos s hs hf_core hg_core).deriv]
      have hmehler : ∀ x, deriv (Gaussian1D.ouSemigroup s g) x =
          Real.exp (-s) * Gaussian1D.ouSemigroup s (deriv g) x := by
        intro x
        exact congrFun (Gaussian1D.deriv_ouSemigroup_eq hg_core s) x
      have h_int :
          ∫ x, deriv f x * deriv (Gaussian1D.ouSemigroup s g) x ∂Gaussian1D.γ =
            Real.exp (-s) * ∫ x, deriv f x * Gaussian1D.ouSemigroup s (deriv g) x ∂Gaussian1D.γ := by
        have hrw :
            (fun x => deriv f x * deriv (Gaussian1D.ouSemigroup s g) x) =
              (fun x => Real.exp (-s) * (deriv f x * Gaussian1D.ouSemigroup s (deriv g) x)) := by
          funext x
          rw [hmehler x]
          ring
        rw [hrw, integral_const_mul]
      rw [h_int]
    exact hderiv.symm

private theorem integralProdRight_sq_le
    (F : Lp ℝ 2 ((γFin n).prod (γFin n))) :
    ∫ x, (∫ y, F (x, y) ∂γFin n) ^ 2 ∂γFin n ≤
      ∫ z, (F z) ^ 2 ∂((γFin n).prod (γFin n)) := by
  have hF_mem : MemLp (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z) 2 ((γFin n).prod (γFin n)) :=
    Lp.memLp F
  have hF_int : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z) ((γFin n).prod (γFin n)) :=
    memLp_one_iff_integrable.mp (hF_mem.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hF2_int : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (F z) ^ 2)
      ((γFin n).prod (γFin n)) := hF_mem.integrable_sq
  have h_convex : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow (Nat.even_iff.mpr rfl)
  have h_cont : ContinuousOn (fun x : ℝ => x ^ 2) Set.univ := (continuous_pow 2).continuousOn
  have h_closed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  have hJensen :
      ∀ᵐ x ∂γFin n, (∫ y, F (x, y) ∂γFin n) ^ 2 ≤ ∫ y, (F (x, y)) ^ 2 ∂γFin n := by
    filter_upwards [hF_int.prod_right_ae, hF2_int.prod_right_ae] with x hx hx2
    have hmem : ∀ᵐ y ∂γFin n, F (x, y) ∈ (Set.univ : Set ℝ) :=
      Filter.Eventually.of_forall fun _ => Set.mem_univ _
    exact ConvexOn.map_integral_le h_convex h_cont h_closed hmem hx hx2
  have h_rhs_int : Integrable (fun x => ∫ y, (F (x, y)) ^ 2 ∂γFin n) (γFin n) :=
    hF2_int.integral_prod_left
  have h_sq_sm :
      AEStronglyMeasurable (fun x => (∫ y, F (x, y) ∂γFin n) ^ 2) (γFin n) := by
    exact (Lp.aestronglyMeasurable F).integral_prod_right'.pow 2
  have h_sq_int :
      Integrable (fun x => (∫ y, F (x, y) ∂γFin n) ^ 2) (γFin n) := by
    refine Integrable.mono' h_rhs_int h_sq_sm ?_
    filter_upwards [hJensen] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  calc
    ∫ x, (∫ y, F (x, y) ∂γFin n) ^ 2 ∂γFin n
      ≤ ∫ x, ∫ y, (F (x, y)) ^ 2 ∂γFin n ∂γFin n := by
          exact integral_mono_ae h_sq_int h_rhs_int hJensen
    _ = ∫ z, (F z) ^ 2 ∂((γFin n).prod (γFin n)) := by
          simpa using
            (integral_prod
              (f := fun z : (Fin n → ℝ) × (Fin n → ℝ) => (F z) ^ 2) hF2_int).symm

private theorem memLp_integralProdRight
    (F : Lp ℝ 2 ((γFin n).prod (γFin n))) :
    MemLp (fun x : Fin n → ℝ => ∫ y, F (x, y) ∂γFin n) 2 (γFin n) := by
  have h_sm :
      AEStronglyMeasurable (fun x : Fin n → ℝ => ∫ y, F (x, y) ∂γFin n) (γFin n) :=
    (Lp.aestronglyMeasurable F).integral_prod_right'
  refine (memLp_two_iff_integrable_sq h_sm).2 ?_
  have h_rhs_int : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (F z) ^ 2)
      ((γFin n).prod (γFin n)) := (Lp.memLp F).integrable_sq
  have h_sq_sm :
      AEStronglyMeasurable (fun x : Fin n → ℝ => (∫ y, F (x, y) ∂γFin n) ^ 2) (γFin n) := by
    exact h_sm.pow 2
  refine Integrable.mono' (h_rhs_int.integral_prod_left) h_sq_sm ?_
  have hF_mem : MemLp (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z) 2 ((γFin n).prod (γFin n)) :=
    Lp.memLp F
  have hF_int : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z) ((γFin n).prod (γFin n)) :=
    memLp_one_iff_integrable.mp (hF_mem.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hJensen :
      ∀ᵐ x ∂γFin n, (∫ y, F (x, y) ∂γFin n) ^ 2 ≤ ∫ y, (F (x, y)) ^ 2 ∂γFin n := by
    filter_upwards [hF_int.prod_right_ae, h_rhs_int.prod_right_ae] with x hx hx2
    have hmem : ∀ᵐ y ∂γFin n, F (x, y) ∈ (Set.univ : Set ℝ) :=
      Filter.Eventually.of_forall fun _ => Set.mem_univ _
    have h_convex : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
      Even.convexOn_pow (Nat.even_iff.mpr rfl)
    have h_cont : ContinuousOn (fun x : ℝ => x ^ 2) Set.univ := (continuous_pow 2).continuousOn
    have h_closed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
    exact ConvexOn.map_integral_le h_convex h_cont h_closed hmem hx hx2
  filter_upwards [hJensen] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hx

private def fstPullL2 :
    Lp ℝ 2 (γFin n) →L[ℝ] Lp ℝ 2 ((γFin n).prod (γFin n)) :=
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℝ) (p := 2)
    Prod.fst measurePreserving_fst).toContinuousLinearMap

private def integralProdRightL2 :
    Lp ℝ 2 ((γFin n).prod (γFin n)) →L[ℝ] Lp ℝ 2 (γFin n) :=
  (fstPullL2 (n := n)).adjoint

private theorem integralProdRightL2_coeFn_ae
    (F : Lp ℝ 2 ((γFin n).prod (γFin n))) :
    (integralProdRightL2 (n := n) F : (Fin n → ℝ) → ℝ) =ᵐ[γFin n]
      fun x => ∫ y, F (x, y) ∂γFin n := by
  let G : Lp ℝ 2 (γFin n) :=
    (memLp_integralProdRight (n := n) F).toLp (fun x : Fin n → ℝ => ∫ y, F (x, y) ∂γFin n)
  have hlhs_int :
      ∀ s, MeasurableSet s → γFin n s < ∞ →
        IntegrableOn (integralProdRightL2 (n := n) F) s (γFin n) := by
    intro s hs hμs
    exact integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne
  have hrhs_int :
      ∀ s, MeasurableSet s → γFin n s < ∞ → IntegrableOn G s (γFin n) := by
    intro s hs hμs
    exact integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne
  have hsets :
      ∀ s : Set (Fin n → ℝ), MeasurableSet s → γFin n s < ∞ →
        ∫ x in s, (integralProdRightL2 (n := n) F : (Fin n → ℝ) → ℝ) x ∂γFin n =
          ∫ x in s, G x ∂γFin n := by
    intro s hs hμs
    have hF_int :
        Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z) ((γFin n).prod (γFin n)) :=
      memLp_one_iff_integrable.mp ((Lp.memLp F).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    have hs_prod : MeasurableSet (s ×ˢ (Set.univ : Set (Fin n → ℝ))) := hs.prod MeasurableSet.univ
    have hleft :
        ∫ x in s, (integralProdRightL2 (n := n) F : (Fin n → ℝ) → ℝ) x ∂γFin n =
          inner ℝ (indicatorConstLp 2 hs hμs.ne (1 : ℝ)) (integralProdRightL2 (n := n) F) := by
      symm
      exact MeasureTheory.L2.inner_indicatorConstLp_one hs hμs.ne _
    have hright :
        ∫ x in s, G x ∂γFin n =
          ∫ z in s ×ˢ (Set.univ : Set (Fin n → ℝ)), F z ∂((γFin n).prod (γFin n)) := by
      calc
        ∫ x in s, G x ∂γFin n
            = ∫ x in s, ∫ y, F (x, y) ∂γFin n ∂γFin n := by
                refine setIntegral_congr_ae hs ?_
                exact ((memLp_integralProdRight (n := n) F).coeFn_toLp).mono fun x hx _ => hx
        _ = ∫ z in s ×ˢ (Set.univ : Set (Fin n → ℝ)), F z ∂((γFin n).prod (γFin n)) := by
              symm
              simpa using
                setIntegral_prod (f := fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z)
                  (s := s) (t := (Set.univ : Set (Fin n → ℝ))) (hF_int.integrableOn)
    rw [hleft]
    change inner ℝ (indicatorConstLp 2 hs hμs.ne (1 : ℝ)) ((fstPullL2 (n := n)).adjoint F) =
      ∫ x in s, G x ∂γFin n
    rw [ContinuousLinearMap.adjoint_inner_right]
    have hfst_indicator :
        fstPullL2 (n := n) (indicatorConstLp 2 hs hμs.ne (1 : ℝ)) =
          indicatorConstLp 2 hs_prod
            (by
              rw [show ((γFin n).prod (γFin n)) (s ×ˢ (Set.univ : Set (Fin n → ℝ))) = γFin n s by
                simp]
              exact hμs.ne)
            (1 : ℝ) := by
      have hpre :
          Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set (Fin n → ℝ)) := by
        ext z
        simp
      simpa [fstPullL2, hs_prod, hpre, Lp.compMeasurePreservingₗᵢ, Lp.compMeasurePreservingₗ]
        using
          (MeasureTheory.Lp.indicatorConstLp_compMeasurePreserving
            (p := 2) (f := Prod.fst) (μ := (γFin n).prod (γFin n)) (μb := γFin n)
            (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ)) measurePreserving_fst)
    rw [hfst_indicator]
    have hinner_prod :
        inner ℝ
            (indicatorConstLp 2 hs_prod
              (by
                rw [show ((γFin n).prod (γFin n)) (s ×ˢ (Set.univ : Set (Fin n → ℝ))) = γFin n s by
                  simp]
                exact hμs.ne)
              (1 : ℝ))
            F =
          ∫ z in s ×ˢ (Set.univ : Set (Fin n → ℝ)), F z ∂((γFin n).prod (γFin n)) := by
      exact MeasureTheory.L2.inner_indicatorConstLp_one hs_prod
        (by
          rw [show ((γFin n).prod (γFin n)) (s ×ˢ (Set.univ : Set (Fin n → ℝ))) = γFin n s by
            simp]
          exact hμs.ne)
        F
    rw [hinner_prod]
    simpa using hright.symm
  have hae :
      (integralProdRightL2 (n := n) F : Lp ℝ 2 (γFin n)) =ᵐ[γFin n] G :=
    Lp.ae_eq_of_forall_setIntegral_eq
      (integralProdRightL2 (n := n) F) G two_ne_zero ENNReal.ofNat_ne_top hlhs_int hrhs_int hsets
  exact hae.trans ((memLp_integralProdRight (n := n) F).coeFn_toLp)

private def mixPullL2 (t : ℝ) (ht : 0 ≤ t) :
    Lp ℝ 2 (γFin n) →L[ℝ] Lp ℝ 2 ((γFin n).prod (γFin n)) :=
  let hmp :
      MeasurePreserving
        (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t))))
        ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t)))).continuous.measurable,
      by simpa using ou_kernel_map_fin (n := n) t ht⟩
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℝ) (p := 2)
    (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t)))) hmp).toContinuousLinearMap

private def ouSemigroupFinLpNonneg (t : ℝ) (ht : 0 ≤ t) :
    Lp ℝ 2 (γFin n) →L[ℝ] Lp ℝ 2 (γFin n) :=
  (integralProdRightL2 (n := n)).comp (mixPullL2 (n := n) t ht)

theorem ouSemigroupFinLpNonneg_coeFn_ae (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (γFin n)) :
    (ouSemigroupFinLpNonneg (n := n) t ht f : (Fin n → ℝ) → ℝ) =ᵐ[γFin n]
      ouSemigroupFin t ((⇑f) : (Fin n → ℝ) → ℝ) := by
  refine (integralProdRightL2_coeFn_ae (n := n) (mixPullL2 (n := n) t ht f)).trans ?_
  let hmp :
      MeasurePreserving
        (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t))))
        ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t)))).continuous.measurable,
      by simpa using ou_kernel_map_fin (n := n) t ht⟩
  have hprod :
      ((mixPullL2 (n := n) t ht f : Lp ℝ 2 ((γFin n).prod (γFin n))) :
          ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ) =ᵐ[((γFin n).prod (γFin n))]
        fun z => f (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t))) z) := by
    simpa [mixPullL2, hmp, Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := f) (hf := hmp))
  have hsec :
    ∀ᵐ x ∂γFin n,
      (fun y => ((mixPullL2 (n := n) t ht f :
        Lp ℝ 2 ((γFin n).prod (γFin n))) : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ) (x, y)) =ᵐ[γFin n]
        (fun y => f (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t))) (x, y))) := by
    convert (MeasureTheory.Measure.ae_ae_eq_curry_of_prod hprod) using 1
    rfl
  filter_upwards [hsec] with x hx
  rw [ouSemigroupFin]
  exact integral_congr_ae hx

/-- The multivariate OU semigroup on `L²(γFin n)`. For `t < 0` we clamp to `t = 0`;
all semigroup laws are only used on `t ≥ 0`, so this keeps the carrier total while
preserving the intended right-half-line dynamics. -/
noncomputable def ouSemigroupFinLp (t : ℝ) :
    Lp ℝ 2 (γFin n) →L[ℝ] Lp ℝ 2 (γFin n) :=
  ouSemigroupFinLpNonneg (n := n) (max t 0) (le_max_right t 0)

theorem ouSemigroupFinLp_coeFn_ae (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 (γFin n)) :
    (ouSemigroupFinLp (n := n) t f : (Fin n → ℝ) → ℝ) =ᵐ[γFin n]
      ouSemigroupFin t ((⇑f) : (Fin n → ℝ) → ℝ) := by
  have hmax : max t 0 = t := max_eq_left ht
  simpa [ouSemigroupFinLp, hmax] using ouSemigroupFinLpNonneg_coeFn_ae (n := n) t ht f

theorem ouSemigroupFinLp_zero :
    ouSemigroupFinLp (n := n) 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 (γFin n)) := by
  ext f
  simpa using
    (ouSemigroupFinLp_coeFn_ae (n := n) 0 (le_rfl) f).trans <|
      Filter.EventuallyEq.of_eq (ouSemigroupFin_zero (n := n) ((⇑f) : (Fin n → ℝ) → ℝ))

theorem ouSemigroupFinLp_contraction (t : ℝ) (ht : 0 ≤ t) :
    ‖ouSemigroupFinLp (n := n) t‖ ≤ 1 := by
  have hmax : max t 0 = t := max_eq_left ht
  have hEq : ouSemigroupFinLp (n := n) t = ouSemigroupFinLpNonneg (n := n) t ht := by
    simp [ouSemigroupFinLp, hmax]
  let hmp :
      MeasurePreserving
        (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t))))
        ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t)))).continuous.measurable,
      by simpa using ou_kernel_map_fin (n := n) t ht⟩
  let fstIso :
      Lp ℝ 2 (γFin n) →ₗᵢ[ℝ] Lp ℝ 2 ((γFin n).prod (γFin n)) :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst
  let mixIso :
      Lp ℝ 2 (γFin n) →ₗᵢ[ℝ] Lp ℝ 2 ((γFin n).prod (γFin n)) :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t)))) hmp
  have hfst_norm :
      ‖fstPullL2 (n := n)‖ ≤ 1 := by
    simpa [fstPullL2, fstIso] using LinearIsometry.norm_toContinuousLinearMap_le fstIso
  have hmix_norm :
      ‖mixPullL2 (n := n) t ht‖ ≤ 1 := by
    simpa [mixPullL2, mixIso] using LinearIsometry.norm_toContinuousLinearMap_le mixIso
  rw [hEq]
  calc
    ‖(integralProdRightL2 (n := n)).comp (mixPullL2 (n := n) t ht)‖
      ≤ ‖integralProdRightL2 (n := n)‖ * ‖mixPullL2 (n := n) t ht‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fstPullL2 (n := n)‖ * ‖mixPullL2 (n := n) t ht‖ := by
          rw [integralProdRightL2, ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * 1 := by
          gcongr
    _ ≤ 1 := by norm_num

theorem ouSemigroupFinLp_conservation (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (γFin n)) (hf : ∀ᵐ x ∂γFin n, (⇑f : (Fin n → ℝ) → ℝ) x = 1) :
    ouSemigroupFinLp (n := n) t f = f := by
  have hconstae :
      ((⇑f) : (Fin n → ℝ) → ℝ) =ᵐ[γFin n]
        (Lp.const 2 (γFin n) (1 : ℝ) : (Fin n → ℝ) → ℝ) := by
    calc
      ((⇑f) : (Fin n → ℝ) → ℝ) =ᵐ[γFin n] fun _ => (1 : ℝ) := hf
      _ =ᵐ[γFin n] (Lp.const 2 (γFin n) (1 : ℝ) : (Fin n → ℝ) → ℝ) :=
        (Lp.coeFn_const (p := 2) (μ := γFin n) (c := (1 : ℝ))).symm
  have hconst : f = Lp.const 2 (γFin n) (1 : ℝ) := by
    rw [Lp.ext_iff]
    exact hconstae
  rw [hconst]
  rw [Lp.ext_iff]
  refine (ouSemigroupFinLp_coeFn_ae (n := n) t ht (Lp.const 2 (γFin n) (1 : ℝ))).trans ?_
  filter_upwards with x
  rw [ouSemigroupFin]
  simp

theorem ouSemigroupFinLp_positivity (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (γFin n)) (hf : 0 ≤ f) :
    0 ≤ ouSemigroupFinLp (n := n) t f := by
  have hEq : ouSemigroupFinLp (n := n) t = ouSemigroupFinLpNonneg (n := n) t ht := by
    simp [ouSemigroupFinLp, max_eq_left ht]
  rw [hEq, ← Lp.coeFn_nonneg]
  have hmix_nonneg : 0 ≤ mixPullL2 (n := n) t ht f := by
    rw [← Lp.coeFn_nonneg]
    let hmp :
        MeasurePreserving
          (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t))))
          ((γFin n).prod (γFin n)) (γFin n) :=
      ⟨(mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t)))).continuous.measurable,
        by simpa using ou_kernel_map_fin (n := n) t ht⟩
    have hf_ae : 0 ≤ᵐ[γFin n] ((⇑f) : (Fin n → ℝ) → ℝ) := (Lp.coeFn_nonneg f).mpr hf
    have hf_comp :
        ∀ᵐ z ∂((γFin n).prod (γFin n)),
          0 ≤ ((⇑f) : (Fin n → ℝ) → ℝ)
            (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t))) z) :=
      hmp.quasiMeasurePreserving.ae hf_ae
    filter_upwards [MeasureTheory.Lp.coeFn_compMeasurePreserving (g := f) (hf := hmp), hf_comp]
      with z hz hz_nonneg
    change 0 ≤
      (((MeasureTheory.Lp.compMeasurePreserving
          (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t)))) hmp) f :
        Lp ℝ 2 ((γFin n).prod (γFin n))) : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ) z
    rw [hz]
    exact hz_nonneg
  have hsec_all :
      ∀ᵐ x ∂γFin n, ∀ᵐ y ∂γFin n,
        0 ≤ ((mixPullL2 (n := n) t ht f :
          Lp ℝ 2 ((γFin n).prod (γFin n))) : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ) (x, y) := by
    exact MeasureTheory.Measure.ae_ae_of_ae_prod ((Lp.coeFn_nonneg _).mpr hmix_nonneg)
  filter_upwards [integralProdRightL2_coeFn_ae (n := n) (mixPullL2 (n := n) t ht f), hsec_all]
    with x hx hsec_nonneg
  simpa [Pi.zero_apply, ouSemigroupFinLpNonneg, hx] using integral_nonneg_of_ae hsec_nonneg

private theorem ouSemigroupFin_compose_of_bound
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf_meas : Measurable f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    ouSemigroupFin (n := n) (s + t) f = ouSemigroupFin s (ouSemigroupFin t f) := by
  ext x
  have hf_int : Integrable f (γFin n) := integrable_of_bound (n := n) hf_meas hM
  set ast := exp (-(s + t))
  set bst := sqrt (1 - exp (-2 * (s + t)))
  set as := exp (-s)
  set bs := sqrt (1 - exp (-2 * s))
  set at_ := exp (-t)
  set bt := sqrt (1 - exp (-2 * t))
  have hbst_nn : 0 ≤ 1 - exp (-2 * (s + t)) :=
    Gaussian1D.one_sub_exp_nonneg (s + t) (by linarith)
  have hbs_nn : 0 ≤ 1 - exp (-2 * s) := Gaussian1D.one_sub_exp_nonneg s hs
  have hbt_nn : 0 ≤ 1 - exp (-2 * t) := Gaussian1D.one_sub_exp_nonneg t ht
  have h_ast : ast = as * at_ := by
    show exp (-(s + t)) = exp (-s) * exp (-t)
    rw [show -(s + t) = -s + -t by ring, exp_add]
  set Ψ : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) :=
    mixCLM (n := n) (at_ * bs) bt
  have h_var_eq : (at_ * bs) ^ 2 + bt ^ 2 = bst ^ 2 := by
    show (exp (-t) * sqrt (1 - exp (-2 * s))) ^ 2 + sqrt (1 - exp (-2 * t)) ^ 2 =
        sqrt (1 - exp (-2 * (s + t))) ^ 2
    rw [mul_pow, sq_sqrt hbs_nn, sq_sqrt hbt_nn, sq_sqrt hbst_nn]
    rw [show exp (-t) ^ 2 = exp (-2 * t) by
      rw [show (-2 * t : ℝ) = -t + -t by ring, exp_add]
      ring]
    have h2 : exp (-2 * t) * exp (-2 * s) = exp (-2 * (s + t)) := by
      rw [← exp_add]
      congr 1
      ring
    linarith [h2]
  have hΨ_law :
      ((γFin n).prod (γFin n)).map Ψ = (γFin n).map (smulFinCLM (n := n) bst) := by
    simpa [Ψ] using
      (ou_kernel_map_coeff_scaled (n := n) (a := at_ * bs) (b := bt) (c := bst)
        h_var_eq (sqrt_nonneg _))
  have hΨ_int : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (ast • x + Ψ p))
      ((γFin n).prod (γFin n)) := by
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · exact (hf_meas.comp ((measurable_const.add Ψ.continuous.measurable))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => hM _)
  have hRHS :
      ouSemigroupFin s (ouSemigroupFin t f) x =
        ∫ p, f (ast • x + Ψ p) ∂((γFin n).prod (γFin n)) := by
    unfold ouSemigroupFin
    have h_eq_pt : ∀ y' y : Fin n → ℝ,
        ouShiftFin t (ouShiftFin s x y') y = ast • x + Ψ (y', y) := by
      intro y' y
      ext i
      rw [h_ast]
      simp [ouShiftFin, Ψ, mixCLM_apply, Pi.smul_apply, smul_eq_mul, as, bs, at_, bt]
      ring
    simp_rw [h_eq_pt]
    simpa using
      (integral_prod (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (ast • x + Ψ p)) hΨ_int).symm
  have hcompose :
      ∫ p, f (ast • x + Ψ p) ∂((γFin n).prod (γFin n)) =
        ∫ z, f (ast • x + bst • z) ∂γFin n := by
    have h_lhs_via_law :
        ∫ p, f (ast • x + Ψ p) ∂((γFin n).prod (γFin n)) =
          ∫ w, f (ast • x + w) ∂(((γFin n).prod (γFin n)).map Ψ) := by
      have hsm : AEStronglyMeasurable (fun w : Fin n → ℝ => f (ast • x + w))
          (((γFin n).prod (γFin n)).map Ψ) := by
        exact (hf_meas.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      rw [integral_map Ψ.continuous.measurable.aemeasurable hsm]
    have h_rhs_via_law :
        ∫ z, f (ast • x + bst • z) ∂γFin n =
          ∫ w, f (ast • x + w) ∂((γFin n).map (smulFinCLM (n := n) bst)) := by
      have hsm : AEStronglyMeasurable (fun w : Fin n → ℝ => f (ast • x + w))
          ((γFin n).map (smulFinCLM (n := n) bst)) := by
        exact (hf_meas.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      have htmp :
          ∫ w, f (ast • x + w) ∂((γFin n).map (smulFinCLM (n := n) bst)) =
            ∫ z, f (ast • x + smulFinCLM (n := n) bst z) ∂γFin n := by
        rw [integral_map (smulFinCLM (n := n) bst).continuous.measurable.aemeasurable hsm]
      calc
        ∫ z, f (ast • x + bst • z) ∂γFin n
            = ∫ z, f (ast • x + smulFinCLM (n := n) bst z) ∂γFin n := by
                simp [smulFinCLM]
        _ = ∫ w, f (ast • x + w) ∂((γFin n).map (smulFinCLM (n := n) bst)) := htmp.symm
    rw [h_lhs_via_law, h_rhs_via_law, hΨ_law]
  show ouSemigroupFin (s + t) f x = ouSemigroupFin s (ouSemigroupFin t f) x
  rw [hRHS, hcompose]
  unfold ouSemigroupFin
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have harg : ouShiftFin (s + t) x y = ast • x + bst • y := by
    ext i
    simp [ouShiftFin, Pi.smul_apply, smul_eq_mul, ast, bst]
  exact congrArg f harg

private theorem ouSemigroupFin_selfAdjoint_of_bound
    (t : ℝ) (ht : 0 ≤ t)
    {f g : (Fin n → ℝ) → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    {Mf Mg : ℝ} (hMf : ∀ x, ‖f x‖ ≤ Mf) (hMg : ∀ x, ‖g x‖ ≤ Mg) :
    ∫ x, ouSemigroupFin t f x * g x ∂γFin n =
      ∫ x, f x * ouSemigroupFin t g x ∂γFin n := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have hnonneg : 0 ≤ 1 - exp (-2 * t) := Gaussian1D.one_sub_exp_nonneg t ht
    rw [show a = exp (-t) by rfl, show b = sqrt (1 - exp (-2 * t)) by rfl]
    rw [sq_sqrt hnonneg, sq, ← exp_add]
    ring_nf
  have hmap : ((γFin n).prod (γFin n)).map (rotCLM (n := n) a b) =
      (γFin n).prod (γFin n) := rotCLM_map_coeff (n := n) a b hab
  have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
  have hMg_nn : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  have hF_sm : AEStronglyMeasurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (mixCLM (n := n) a b p) * g p.1)
      ((γFin n).prod (γFin n)) := by
    exact
      (((hf_meas.comp (mixCLM (n := n) a b).continuous.measurable)).mul
        (hg_meas.comp measurable_fst)).aemeasurable.aestronglyMeasurable
  have hG_sm : AEStronglyMeasurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1 * g (mixCLM (n := n) a b p))
      ((γFin n).prod (γFin n)) := by
    exact
      (((hf_meas.comp measurable_fst)).mul
        (hg_meas.comp (mixCLM (n := n) a b).continuous.measurable)).aemeasurable.aestronglyMeasurable
  have hF_int : Integrable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (mixCLM (n := n) a b p) * g p.1)
      ((γFin n).prod (γFin n)) := by
    refine Integrable.mono' (integrable_const (Mf * Mg)) hF_sm ?_
    refine Filter.Eventually.of_forall ?_
    intro p
    rw [norm_mul]
    exact mul_le_mul (hMf _) (hMg _) (norm_nonneg _) hMf_nn
  have hG_int : Integrable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1 * g (mixCLM (n := n) a b p))
      ((γFin n).prod (γFin n)) := by
    refine Integrable.mono' (integrable_const (Mf * Mg)) hG_sm ?_
    refine Filter.Eventually.of_forall ?_
    intro p
    rw [norm_mul]
    exact mul_le_mul (hMf _) (hMg _) (norm_nonneg _) hMf_nn
  have hlaw :
      HasLaw (rotCLM (n := n) a b) ((γFin n).prod (γFin n)) ((γFin n).prod (γFin n)) :=
    ⟨(Measurable.aemeasurable (by fun_prop)), hmap⟩
  have hswap :
      ∫ p, f (mixCLM (n := n) a b p) * g p.1 ∂((γFin n).prod (γFin n)) =
        ∫ p, f p.1 * g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
    calc
      ∫ p, f (mixCLM (n := n) a b p) * g p.1 ∂((γFin n).prod (γFin n))
          = ∫ p,
              (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
                f q.1 * g (mixCLM (n := n) a b q)) (rotCLM (n := n) a b p)
              ∂((γFin n).prod (γFin n)) := by
                refine integral_congr_ae ?_
                refine Filter.Eventually.of_forall ?_
                intro p
                change f (mixCLM (n := n) a b p) * g p.1 =
                  f ((rotCLM (n := n) a b p).1) *
                    g (mixCLM (n := n) a b (rotCLM (n := n) a b p))
                rw [mixCLM_rotCLM (n := n) a b hab p]
                simp [rotCLM]
      _ = ∫ p, f p.1 * g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
            exact hlaw.integral_comp hG_sm
  have hleft_prod :
      ∫ x, ouSemigroupFin t f x * g x ∂γFin n =
        ∫ p, f (mixCLM (n := n) a b p) * g p.1 ∂((γFin n).prod (γFin n)) := by
    have hiter :
        ∫ x, ouSemigroupFin t f x * g x ∂γFin n =
          ∫ x, ∫ y, f (mixCLM (n := n) a b (x, y)) * g x ∂γFin n ∂γFin n := by
      unfold ouSemigroupFin
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have hxy :
          (fun y : Fin n → ℝ => f (ouShiftFin t x y)) =
            fun y : Fin n → ℝ => f (mixCLM (n := n) a b (x, y)) := by
        funext y
        have harg : ouShiftFin t x y = mixCLM (n := n) a b (x, y) := by
          ext i
          simp [ouShiftFin, mixCLM_apply, a, b]
        exact congrArg f harg
      calc
        (∫ y, f (ouShiftFin t x y) ∂γFin n) * g x
            = (∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n) * g x := by
                simp [hxy]
        _ = ∫ y, f (mixCLM (n := n) a b (x, y)) * g x ∂γFin n := by
              symm
              simpa [mul_comm] using
                (integral_const_mul (r := g x)
                  (f := fun y : Fin n → ℝ => f (mixCLM (n := n) a b (x, y))))
    rw [hiter]
    simpa using
      (integral_prod
        (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          f (mixCLM (n := n) a b p) * g p.1) hF_int).symm
  have hright_prod :
      ∫ x, f x * ouSemigroupFin t g x ∂γFin n =
        ∫ p, f p.1 * g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
    have hiter :
        ∫ x, f x * ouSemigroupFin t g x ∂γFin n =
          ∫ x, ∫ y, f x * g (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n := by
      unfold ouSemigroupFin
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have hxy :
          (fun y : Fin n → ℝ => g (ouShiftFin t x y)) =
            fun y : Fin n → ℝ => g (mixCLM (n := n) a b (x, y)) := by
        funext y
        have harg : ouShiftFin t x y = mixCLM (n := n) a b (x, y) := by
          ext i
          simp [ouShiftFin, mixCLM_apply, a, b]
        exact congrArg g harg
      calc
        f x * ∫ y, g (ouShiftFin t x y) ∂γFin n
            = f x * ∫ y, g (mixCLM (n := n) a b (x, y)) ∂γFin n := by
                simp [hxy]
        _ = ∫ y, f x * g (mixCLM (n := n) a b (x, y)) ∂γFin n := by
              symm
              simpa using
                (integral_const_mul (r := f x)
                  (f := fun y : Fin n → ℝ => g (mixCLM (n := n) a b (x, y))))
    rw [hiter]
    simpa using
      (integral_prod
        (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          f p.1 * g (mixCLM (n := n) a b p)) hG_int).symm
  rw [hleft_prod, hright_prod]
  exact hswap

private theorem memLp_two_of_bound {f : (Fin n → ℝ) → ℝ}
    (hf_meas : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    MemLp f 2 (γFin n) :=
  MemLp.of_bound hf_meas.aestronglyMeasurable M (Filter.Eventually.of_forall hM)

theorem ouSemigroupFin_memLp_of_bound (t : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf_meas : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    MemLp (ouSemigroupFin t f) 2 (γFin n) :=
  MemLp.of_bound (stronglyMeasurable_ouSemigroupFin (n := n) t hf_meas).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x =>
      norm_ouSemigroupFin_le_of_bound (n := n) t hf_meas hM x)

private theorem integral_mul_toLp_eq_integral_mul {f g : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 (γFin n)) (hg : MemLp g 2 (γFin n)) :
    ∫ x, (hf.toLp f) x * (hg.toLp g) x ∂γFin n = ∫ x, f x * g x ∂γFin n := by
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp [hfx, hgx]

theorem norm_sq_toLp_eq_integral_sq {f : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 (γFin n)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂γFin n := by
  have hmulpow :
      ∫ x, (hf.toLp f) x * (hf.toLp f) x ∂γFin n =
        ∫ x, ((hf.toLp f) x) ^ 2 ∂γFin n := by
    simp [pow_two]
  have hinner :
      ∫ x, (hf.toLp f) x * (hf.toLp f) x ∂γFin n = ‖hf.toLp f‖ ^ 2 := by
    have h1 : ∫ x, (hf.toLp f) x * (hf.toLp f) x ∂γFin n = ⟪hf.toLp f, hf.toLp f⟫_ℝ := by
      rw [MeasureTheory.L2.inner_def]
      simp [pow_two]
    have h2 : ⟪hf.toLp f, hf.toLp f⟫_ℝ = ‖hf.toLp f‖ ^ 2 := by
      exact inner_self_eq_norm_sq_to_K (hf.toLp f)
    exact h1.trans h2
  calc
    ‖hf.toLp f‖ ^ 2 = ∫ x, (hf.toLp f) x * (hf.toLp f) x ∂γFin n := hinner.symm
    _ = ∫ x, (f x) ^ 2 ∂γFin n := by
      calc
        ∫ x, (hf.toLp f) x * (hf.toLp f) x ∂γFin n
            = ∫ x, f x * f x ∂γFin n := integral_mul_toLp_eq_integral_mul (n := n) hf hf
        _ = ∫ x, (f x) ^ 2 ∂γFin n := by simp [pow_two]

private theorem partialDeriv_hasCompactSupport {f : (Fin n → ℝ) → ℝ}
    (hf : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (partialDeriv i f) := by
  unfold partialDeriv
  simpa using hf.fderiv_apply ℝ (Pi.single i (1 : ℝ))

private theorem secondPartial_hasCompactSupport {f : (Fin n → ℝ) → ℝ}
    (hf : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (secondPartial i f) := by
  unfold secondPartial
  simpa [partialDeriv] using (partialDeriv_hasCompactSupport (n := n) hf i).fderiv_apply ℝ
    (Pi.single i (1 : ℝ))

private theorem isCoreFin_of_hasCompactSupport_contDiff {f : (Fin n → ℝ) → ℝ}
    (hf_supp : HasCompactSupport f) (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsCoreFin f := by
  obtain ⟨Mf, hMf⟩ := hf_supp.exists_bound_of_continuous hf_smooth.continuous
  choose M1 hM1 using fun i : Fin n =>
    (partialDeriv_hasCompactSupport (n := n) hf_supp i).exists_bound_of_continuous
      ((hf_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).continuous
  choose M2 hM2 using fun i : Fin n =>
    (secondPartial_hasCompactSupport (n := n) hf_supp i).exists_bound_of_continuous
      ((((hf_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).fderiv_right
        (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).continuous
  refine ⟨hf_smooth, |Mf| + ∑ i, |M1 i| + ∑ i, |M2 i|, ?_⟩
  intro x
  have hsum1_nonneg : 0 ≤ ∑ i, |M1 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsum2_nonneg : 0 ≤ ∑ i, |M2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨le_trans (hMf x) ?_, ?_, ?_⟩
  · calc
      Mf ≤ |Mf| := le_abs_self Mf
      _ ≤ |Mf| + ∑ i, |M1 i| + ∑ i, |M2 i| := by linarith
  · intro i
    have hsum : |M1 i| ≤ ∑ j, |M1 j| := by
      simpa using
        (Finset.single_le_sum (f := fun j : Fin n => |M1 j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    calc
      ‖partialDeriv i f x‖ ≤ M1 i := hM1 i x
      _ ≤ |M1 i| := le_abs_self (M1 i)
      _ ≤ ∑ j, |M1 j| := hsum
      _ ≤ ∑ j, |M1 j| + ∑ j, |M2 j| := by exact le_add_of_nonneg_right hsum2_nonneg
      _ ≤ |Mf| + (∑ j, |M1 j| + ∑ j, |M2 j|) := by
        exact le_add_of_nonneg_left (abs_nonneg Mf)
      _ = |Mf| + ∑ j, |M1 j| + ∑ j, |M2 j| := by ring
  · intro i
    have hsum : |M2 i| ≤ ∑ j, |M2 j| := by
      simpa using
        (Finset.single_le_sum (f := fun j : Fin n => |M2 j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    calc
      ‖secondPartial i f x‖ ≤ M2 i := hM2 i x
      _ ≤ |M2 i| := le_abs_self (M2 i)
      _ ≤ ∑ j, |M2 j| := hsum
      _ ≤ ∑ j, |M1 j| + ∑ j, |M2 j| := by exact le_add_of_nonneg_left hsum1_nonneg
      _ ≤ |Mf| + (∑ j, |M1 j| + ∑ j, |M2 j|) := by
        exact le_add_of_nonneg_left (abs_nonneg Mf)
      _ = |Mf| + ∑ j, |M1 j| + ∑ j, |M2 j| := by ring

theorem isCoreFin_memLp (f : (Fin n → ℝ) → ℝ) (hf : IsCoreFin f) :
    MemLp f 2 (γFin n) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  exact memLp_two_of_bound (n := n) hf.measurable hM

private theorem ouSemigroupFin_ae_eq_of_aeEq (t : ℝ) (ht : 0 ≤ t)
    {f g : (Fin n → ℝ) → ℝ} (hfg : f =ᵐ[γFin n] g) :
    ouSemigroupFin t f =ᵐ[γFin n] ouSemigroupFin t g := by
  let hmp :
      MeasurePreserving
        (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t))))
        ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t)))).continuous.measurable,
      by simpa using ou_kernel_map_fin (n := n) t ht⟩
  have hprod :
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => f (mixCLM (n := n) (exp (-t))
          (sqrt (1 - exp (-2 * t))) z)) =ᵐ[((γFin n).prod (γFin n))]
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => g (mixCLM (n := n) (exp (-t))
          (sqrt (1 - exp (-2 * t))) z)) := hmp.quasiMeasurePreserving.ae hfg
  have hsec :
      ∀ᵐ x ∂γFin n,
        (fun y => f (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t))) (x, y))) =ᵐ[γFin n]
        (fun y => g (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t))) (x, y))) := by
    convert (MeasureTheory.Measure.ae_ae_eq_curry_of_prod hprod) using 1
    rfl
  filter_upwards [hsec] with x hx
  rw [ouSemigroupFin, ouSemigroupFin]
  exact integral_congr_ae hx

theorem ouSemigroupFinLp_eq_toLp_of_bound (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf_meas : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    ouSemigroupFinLp (n := n) t ((memLp_two_of_bound (n := n) hf_meas hM).toLp f) =
      (ouSemigroupFin_memLp_of_bound (n := n) t hf_meas hM).toLp (ouSemigroupFin t f) := by
  rw [Lp.ext_iff]
  calc
    ((⇑(ouSemigroupFinLp (n := n) t ((memLp_two_of_bound (n := n) hf_meas hM).toLp f))) :
        (Fin n → ℝ) → ℝ) =ᵐ[γFin n]
        ouSemigroupFin t
          (((memLp_two_of_bound (n := n) hf_meas hM).toLp f : (Fin n → ℝ) → ℝ)) :=
      ouSemigroupFinLp_coeFn_ae (n := n) t ht _
    _ =ᵐ[γFin n] ouSemigroupFin t f :=
      ouSemigroupFin_ae_eq_of_aeEq (n := n) t ht
        (memLp_two_of_bound (n := n) hf_meas hM).coeFn_toLp
    _ =ᵐ[γFin n]
        ((ouSemigroupFin_memLp_of_bound (n := n) t hf_meas hM).toLp (ouSemigroupFin t f) :
          (Fin n → ℝ) → ℝ) :=
      (ouSemigroupFin_memLp_of_bound (n := n) t hf_meas hM).coeFn_toLp.symm

private def smoothCoreSet : Set (Lp ℝ 2 (γFin n)) :=
  {u | ∃ g : (Fin n → ℝ) → ℝ,
      ((⇑u) : (Fin n → ℝ) → ℝ) =ᵐ[γFin n] g ∧
      HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g}

private theorem smoothCoreSet_dense : Dense (smoothCoreSet (n := n)) := by
  simpa [smoothCoreSet] using
    (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (E := Fin n → ℝ) (F := ℝ) (μ := γFin n) (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top)

private theorem smoothCoreSet_eq_toLp {u : Lp ℝ 2 (γFin n)}
    (hu : u ∈ smoothCoreSet (n := n)) :
    ∃ g : (Fin n → ℝ) → ℝ, HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∃ hg_mem : MemLp g 2 (γFin n), u = hg_mem.toLp g := by
  rcases hu with ⟨g, hug, hg_supp, hg_smooth⟩
  have hg_mem : MemLp g 2 (γFin n) := hg_smooth.continuous.memLp_of_hasCompactSupport hg_supp
  refine ⟨g, hg_supp, hg_smooth, hg_mem, ?_⟩
  rw [Lp.ext_iff]
  exact hug.trans hg_mem.coeFn_toLp.symm

private theorem ouSemigroupFinLp_symmetric_of_bound (t : ℝ) (ht : 0 ≤ t)
    {f g : (Fin n → ℝ) → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    {Mf Mg : ℝ} (hMf : ∀ x, ‖f x‖ ≤ Mf) (hMg : ∀ x, ‖g x‖ ≤ Mg) :
    ⟪(memLp_two_of_bound (n := n) hf_meas hMf).toLp f,
      ouSemigroupFinLp (n := n) t ((memLp_two_of_bound (n := n) hg_meas hMg).toLp g)⟫_ℝ =
    ⟪ouSemigroupFinLp (n := n) t ((memLp_two_of_bound (n := n) hf_meas hMf).toLp f),
      (memLp_two_of_bound (n := n) hg_meas hMg).toLp g⟫_ℝ := by
  rw [ouSemigroupFinLp_eq_toLp_of_bound (n := n) t ht hg_meas hMg]
  rw [ouSemigroupFinLp_eq_toLp_of_bound (n := n) t ht hf_meas hMf]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hleft :
      ∫ a, ⟪((memLp_two_of_bound (n := n) hf_meas hMf).toLp f) a,
          ((ouSemigroupFin_memLp_of_bound (n := n) t hg_meas hMg).toLp (ouSemigroupFin t g)) a⟫_ℝ
        ∂γFin n
        = ∫ x, f x * ouSemigroupFin t g x ∂γFin n := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_two_of_bound (n := n) hf_meas hMf).coeFn_toLp,
      (ouSemigroupFin_memLp_of_bound (n := n) t hg_meas hMg).coeFn_toLp] with x hfx hgx
    rw [hfx, hgx]
    change RCLike.re (ouSemigroupFin t g x * star (f x)) = f x * ouSemigroupFin t g x
    simp [mul_comm]
  have hright :
      ∫ a, ⟪((ouSemigroupFin_memLp_of_bound (n := n) t hf_meas hMf).toLp (ouSemigroupFin t f)) a,
          ((memLp_two_of_bound (n := n) hg_meas hMg).toLp g) a⟫_ℝ
        ∂γFin n
        = ∫ x, ouSemigroupFin t f x * g x ∂γFin n := by
    refine integral_congr_ae ?_
    filter_upwards [(ouSemigroupFin_memLp_of_bound (n := n) t hf_meas hMf).coeFn_toLp,
      (memLp_two_of_bound (n := n) hg_meas hMg).coeFn_toLp] with x hfx hgx
    rw [hfx, hgx]
    change RCLike.re (g x * star (ouSemigroupFin t f x)) = ouSemigroupFin t f x * g x
    simp [mul_comm]
  rw [hleft, hright]
  exact (ouSemigroupFin_selfAdjoint_of_bound (n := n) t ht hf_meas hg_meas hMf hMg).symm

theorem ouSemigroupFinLp_semigroup (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ouSemigroupFinLp (n := n) (s + t) =
      (ouSemigroupFinLp (n := n) s).comp (ouSemigroupFinLp (n := n) t) := by
  let S : Set (Lp ℝ 2 (γFin n)) :=
    {u | ouSemigroupFinLp (n := n) (s + t) u =
        ((ouSemigroupFinLp (n := n) s).comp (ouSemigroupFinLp (n := n) t)) u}
  have hClosed : IsClosed S := by
    refine isClosed_eq (ouSemigroupFinLp (n := n) (s + t)).continuous ?_
    exact ((ouSemigroupFinLp (n := n) s).comp (ouSemigroupFinLp (n := n) t)).continuous
  have hSubset : smoothCoreSet (n := n) ⊆ S := by
    intro u hu
    rcases smoothCoreSet_eq_toLp (n := n) hu with ⟨g, hg_supp, hg_smooth, hg_mem, rfl⟩
    have hg_core : IsCoreFin g := isCoreFin_of_hasCompactSupport_contDiff (n := n) hg_supp hg_smooth
    obtain ⟨M, hM⟩ := hg_core.bound_exists
    have hPt_mem : MemLp (ouSemigroupFin t g) 2 (γFin n) :=
      ouSemigroupFin_memLp_of_bound (n := n) t hg_core.measurable hM
    calc
      ouSemigroupFinLp (n := n) (s + t) (hg_mem.toLp g)
          = (ouSemigroupFin_memLp_of_bound (n := n) (s + t) hg_core.measurable hM).toLp
              (ouSemigroupFin (s + t) g) :=
            ouSemigroupFinLp_eq_toLp_of_bound (n := n) (s + t) (add_nonneg hs ht)
              hg_core.measurable hM
      _ = (ouSemigroupFin_memLp_of_bound (n := n) s
            (stronglyMeasurable_ouSemigroupFin (n := n) t hg_core.measurable).measurable
            (fun x => norm_ouSemigroupFin_le_of_bound (n := n) t hg_core.measurable hM x)).toLp
            (ouSemigroupFin s (ouSemigroupFin t g)) := by
              rw [Lp.ext_iff]
              calc
                (((ouSemigroupFin_memLp_of_bound (n := n) (s + t) hg_core.measurable hM).toLp
                    (ouSemigroupFin (s + t) g)) : (Fin n → ℝ) → ℝ) =ᵐ[γFin n]
                    ouSemigroupFin (s + t) g :=
                  (ouSemigroupFin_memLp_of_bound (n := n) (s + t) hg_core.measurable hM).coeFn_toLp
                _ =ᵐ[γFin n] ouSemigroupFin s (ouSemigroupFin t g) :=
                  Filter.EventuallyEq.of_eq <| by
                    ext x
                    exact congrFun
                      (ouSemigroupFin_compose_of_bound (n := n) s t hs ht hg_core.measurable hM) x
                _ =ᵐ[γFin n]
                    (((ouSemigroupFin_memLp_of_bound (n := n) s
                        (stronglyMeasurable_ouSemigroupFin (n := n) t hg_core.measurable).measurable
                        (fun x => norm_ouSemigroupFin_le_of_bound (n := n) t hg_core.measurable hM x)).toLp
                      (ouSemigroupFin s (ouSemigroupFin t g))) : (Fin n → ℝ) → ℝ) :=
                  (ouSemigroupFin_memLp_of_bound (n := n) s
                    (stronglyMeasurable_ouSemigroupFin (n := n) t hg_core.measurable).measurable
                    (fun x => norm_ouSemigroupFin_le_of_bound (n := n) t hg_core.measurable hM x)).coeFn_toLp.symm
      _ = ouSemigroupFinLp (n := n) s (hPt_mem.toLp (ouSemigroupFin t g)) := by
            symm
            exact ouSemigroupFinLp_eq_toLp_of_bound (n := n) s hs
              (stronglyMeasurable_ouSemigroupFin (n := n) t hg_core.measurable).measurable
              (fun x => norm_ouSemigroupFin_le_of_bound (n := n) t hg_core.measurable hM x)
      _ = ouSemigroupFinLp (n := n) s (ouSemigroupFinLp (n := n) t (hg_mem.toLp g)) := by
            rw [ouSemigroupFinLp_eq_toLp_of_bound (n := n) t ht hg_core.measurable hM]
  apply ContinuousLinearMap.ext
  intro u
  have huClosure : u ∈ closure (smoothCoreSet (n := n)) := by
    simp [smoothCoreSet_dense (n := n).closure_eq]
  simpa [S] using hClosed.closure_subset_iff.mpr hSubset huClosure

theorem ouSemigroupFinLp_symmetric (t : ℝ) (ht : 0 ≤ t)
    (f g : Lp ℝ 2 (γFin n)) :
    ⟪f, ouSemigroupFinLp (n := n) t g⟫_ℝ = ⟪ouSemigroupFinLp (n := n) t f, g⟫_ℝ := by
  have hSmoothRight :
      ∀ v ∈ smoothCoreSet (n := n),
        ∀ u : Lp ℝ 2 (γFin n),
          ⟪u, ouSemigroupFinLp (n := n) t v⟫_ℝ =
            ⟪ouSemigroupFinLp (n := n) t u, v⟫_ℝ := by
    intro v hv u
    let Su : Set (Lp ℝ 2 (γFin n)) :=
      {w | ⟪w, ouSemigroupFinLp (n := n) t v⟫_ℝ =
          ⟪ouSemigroupFinLp (n := n) t w, v⟫_ℝ}
    have hSu_closed : IsClosed Su := by
      refine isClosed_eq ?_ ?_
      · exact Continuous.inner continuous_id continuous_const
      · exact Continuous.inner ((ouSemigroupFinLp (n := n) t).continuous) continuous_const
    have hSu_subset : smoothCoreSet (n := n) ⊆ Su := by
      intro w hw
      rcases smoothCoreSet_eq_toLp (n := n) hw with ⟨fw, hfw_supp, hfw_smooth, hfw_mem, rfl⟩
      rcases smoothCoreSet_eq_toLp (n := n) hv with ⟨fv, hfv_supp, hfv_smooth, hfv_mem, rfl⟩
      have hfw_core : IsCoreFin fw := isCoreFin_of_hasCompactSupport_contDiff (n := n) hfw_supp hfw_smooth
      have hfv_core : IsCoreFin fv := isCoreFin_of_hasCompactSupport_contDiff (n := n) hfv_supp hfv_smooth
      obtain ⟨Mw, hMw⟩ := hfw_core.bound_exists
      obtain ⟨Mv, hMv⟩ := hfv_core.bound_exists
      exact ouSemigroupFinLp_symmetric_of_bound (n := n) t ht hfw_core.measurable hfv_core.measurable
        hMw hMv
    have huClosure : u ∈ closure (smoothCoreSet (n := n)) := by
      simp [smoothCoreSet_dense (n := n).closure_eq]
    simpa [Su] using hSu_closed.closure_subset_iff.mpr hSu_subset huClosure
  let T : Set (Lp ℝ 2 (γFin n)) :=
    {v | ⟪f, ouSemigroupFinLp (n := n) t v⟫_ℝ =
        ⟪ouSemigroupFinLp (n := n) t f, v⟫_ℝ}
  have hT_closed : IsClosed T := by
    refine isClosed_eq ?_ ?_
    · exact Continuous.inner continuous_const ((ouSemigroupFinLp (n := n) t).continuous)
    · exact Continuous.inner continuous_const continuous_id
  have hT_subset : smoothCoreSet (n := n) ⊆ T := by
    intro v hv
    simpa [T] using hSmoothRight v hv f
  have hgClosure : g ∈ closure (smoothCoreSet (n := n)) := by
    simp [smoothCoreSet_dense (n := n).closure_eq]
  simpa [T] using hT_closed.closure_subset_iff.mpr hT_subset hgClosure

private theorem ouShiftFin_tendsto_zero (x y : Fin n → ℝ) :
    Tendsto (fun t : ℝ => ouShiftFin t x y) (nhdsWithin 0 (Set.Ici 0)) (nhds x) := by
  have hcont : Continuous (fun t : ℝ => ouShiftFin t x y) := by
    continuity
  have h0 :
      Tendsto (fun t : ℝ => ouShiftFin t x y) (nhdsWithin 0 (Set.Ici 0))
        (nhds (ouShiftFin 0 x y)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (hcont.continuousAt.tendsto)
  have hzero : ouShiftFin 0 x y = x := by
    ext i
    simp [ouShiftFin]
  simpa [hzero] using h0

private theorem ouSemigroupFin_tendsto_zero_of_bound
    {f : (Fin n → ℝ) → ℝ} (hf_cont : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (x : Fin n → ℝ) :
    Tendsto (fun t : ℝ => ouSemigroupFin t f x) (nhdsWithin 0 (Set.Ici 0)) (nhds (f x)) := by
  have hconst :
      Integrable (fun _ : Fin n → ℝ => M) (γFin n) := integrable_const M
  have hlim :
      Tendsto (fun t : ℝ => ∫ y, f (ouShiftFin t x y) ∂γFin n)
        (nhdsWithin 0 (Set.Ici 0)) (nhds (∫ _ : Fin n → ℝ, f x ∂γFin n)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M) ?_ ?_ hconst ?_
    · filter_upwards with t
      have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      exact (hf_cont.comp hcont_shift).aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with y
      exact hM (ouShiftFin t x y)
    · filter_upwards with y
      exact (hf_cont.tendsto _).comp (ouShiftFin_tendsto_zero (n := n) x y)
  simpa [ouSemigroupFin, integral_const] using hlim

private theorem ouSemigroupFin_integral_sq_sub_tendsto_zero
    {f : (Fin n → ℝ) → ℝ} (hf_cont : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    Tendsto (fun t : ℝ => ∫ x, (ouSemigroupFin t f x - f x) ^ 2 ∂γFin n)
      (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
  have hM_nonneg : 0 ≤ M := by
    simpa using (le_trans (norm_nonneg (f 0)) (hM 0))
  have hconst :
      Integrable (fun _ : Fin n → ℝ => (2 * M) ^ 2) (γFin n) := integrable_const ((2 * M) ^ 2)
  have hlim :
      Tendsto (fun t : ℝ => ∫ x, (ouSemigroupFin t f x - f x) ^ 2 ∂γFin n)
        (nhdsWithin 0 (Set.Ici 0)) (nhds (∫ x, (0 : ℝ) ∂γFin n)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2 * M) ^ 2) ?_ ?_ hconst ?_
    · filter_upwards with t
      exact ((stronglyMeasurable_ouSemigroupFin (n := n) t hf_cont.measurable).sub
        hf_cont.stronglyMeasurable).pow 2 |>.aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with x
      have hdiff :
          ‖ouSemigroupFin t f x - f x‖ ≤ 2 * M := by
        calc
          ‖ouSemigroupFin t f x - f x‖ ≤ ‖ouSemigroupFin t f x‖ + ‖f x‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add
              (norm_ouSemigroupFin_le_of_bound (n := n) t hf_cont.measurable hM x)
              (hM x)
          _ = 2 * M := by ring
      have habs : |ouSemigroupFin t f x - f x| ≤ 2 * M := by
        simpa [Real.norm_eq_abs] using hdiff
      have hsq : |(ouSemigroupFin t f x - f x) ^ 2| ≤ (2 * M) ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq.mpr <| by
          simpa [abs_of_nonneg (by positivity : 0 ≤ 2 * M)] using habs
      simpa [Real.norm_eq_abs] using hsq
    · filter_upwards with x
      have hdiff :
          Tendsto (fun t : ℝ => ouSemigroupFin t f x - f x)
            (nhdsWithin 0 (Set.Ici 0)) (nhds 0) :=
        by
          have hconst : Tendsto (fun _ : ℝ => f x) (nhdsWithin 0 (Set.Ici 0)) (nhds (f x)) :=
            tendsto_const_nhds
          simpa using (ouSemigroupFin_tendsto_zero_of_bound (n := n) hf_cont hM x).sub hconst
      simpa using hdiff.pow 2
  simpa using hlim

private theorem ouSemigroupFinLp_strong_cont_of_hasCompactSupport_contDiff
    {f : (Fin n → ℝ) → ℝ} (hf_supp : HasCompactSupport f) (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) :
    Tendsto (fun t : ℝ => ouSemigroupFinLp (n := n) t ((isCoreFin_memLp (n := n) f
      (isCoreFin_of_hasCompactSupport_contDiff (n := n) hf_supp hf_smooth)).toLp f))
      (nhdsWithin 0 (Set.Ici 0))
      (nhds ((isCoreFin_memLp (n := n) f
        (isCoreFin_of_hasCompactSupport_contDiff (n := n) hf_supp hf_smooth)).toLp f)) := by
  let hf_core : IsCoreFin f := isCoreFin_of_hasCompactSupport_contDiff (n := n) hf_supp hf_smooth
  let hf_mem : MemLp f 2 (γFin n) := isCoreFin_memLp (n := n) f hf_core
  let hPf_mem : ∀ t : ℝ, MemLp (ouSemigroupFin t f) 2 (γFin n) :=
    fun t => ouSemigroupFin_memLp_of_bound (n := n) t hf_core.measurable hf_core.bound_exists.choose_spec
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq :
      Tendsto (fun t : ℝ =>
        ‖ouSemigroupFinLp (n := n) t (hf_mem.toLp f) - hf_mem.toLp f‖ ^ 2)
        (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
    have hEq :
        (fun t : ℝ => ∫ x, (ouSemigroupFin t f x - f x) ^ 2 ∂γFin n) =ᶠ[nhdsWithin 0 (Set.Ici 0)]
          fun t : ℝ => ‖ouSemigroupFinLp (n := n) t (hf_mem.toLp f) - hf_mem.toLp f‖ ^ 2 := by
      have hIci : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ici 0), t ∈ Set.Ici 0 :=
        eventually_mem_of_tendsto_nhdsWithin tendsto_id
      filter_upwards [hIci] with t ht
      have htoLp :
          ouSemigroupFinLp (n := n) t (hf_mem.toLp f) - hf_mem.toLp f =
            ((hPf_mem t).sub hf_mem).toLp (ouSemigroupFin t f - f) := by
        rw [ouSemigroupFinLp_eq_toLp_of_bound (n := n) t ht hf_core.measurable
          hf_core.bound_exists.choose_spec]
        symm
        exact MemLp.toLp_sub (hPf_mem t) hf_mem
      rw [htoLp]
      symm
      exact norm_sq_toLp_eq_integral_sq (n := n) ((hPf_mem t).sub hf_mem)
    exact (ouSemigroupFin_integral_sq_sub_tendsto_zero (n := n) hf_smooth.continuous
      hf_core.bound_exists.choose_spec).congr' hEq
  have hnorm :
      Tendsto (fun t : ℝ => ‖ouSemigroupFinLp (n := n) t (hf_mem.toLp f) - hf_mem.toLp f‖)
        (nhdsWithin 0 (Set.Ici 0)) (nhds (Real.sqrt 0)) := by
    refine ((Continuous.tendsto Real.continuous_sqrt 0).comp hsq).congr' ?_
    filter_upwards with t
    simp [Function.comp]
  simpa using hnorm

theorem ouSemigroupFinLp_strong_cont (f : Lp ℝ 2 (γFin n)) :
    Tendsto (fun t : ℝ => ouSemigroupFinLp (n := n) t f)
      (nhdsWithin 0 (Set.Ici 0)) (nhds f) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rcases (smoothCoreSet_dense (n := n)).exists_dist_lt f (by positivity : 0 < ε / 4) with
    ⟨u, huSmooth, huApprox⟩
  rcases smoothCoreSet_eq_toLp (n := n) huSmooth with ⟨g, hg_supp, hg_smooth, hg_mem, rfl⟩
  have huCont := ouSemigroupFinLp_strong_cont_of_hasCompactSupport_contDiff (n := n) hg_supp hg_smooth
  rw [Metric.tendsto_nhdsWithin_nhds] at huCont
  obtain ⟨δ, hδ_pos, hδ⟩ := huCont (ε / 2) (by positivity)
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht0 htδ
  calc
    dist (ouSemigroupFinLp (n := n) t f) f
      ≤ dist (ouSemigroupFinLp (n := n) t f) (ouSemigroupFinLp (n := n) t (hg_mem.toLp g))
        + dist (ouSemigroupFinLp (n := n) t (hg_mem.toLp g)) (hg_mem.toLp g)
        + dist (hg_mem.toLp g) f := by
          simpa [dist_comm, dist_eq_norm, norm_sub_rev, add_assoc] using
            dist_triangle4 (ouSemigroupFinLp (n := n) t f) (ouSemigroupFinLp (n := n) t (hg_mem.toLp g))
              (hg_mem.toLp g) f
    _ ≤ ‖ouSemigroupFinLp (n := n) t‖ * dist f (hg_mem.toLp g)
        + dist (ouSemigroupFinLp (n := n) t (hg_mem.toLp g)) (hg_mem.toLp g)
        + dist (hg_mem.toLp g) f := by
          gcongr
          simpa [dist_eq_norm, norm_sub_rev] using
            (ouSemigroupFinLp (n := n) t).lipschitzWith.norm_sub_le f (hg_mem.toLp g)
    _ ≤ dist f (hg_mem.toLp g)
        + dist (ouSemigroupFinLp (n := n) t (hg_mem.toLp g)) (hg_mem.toLp g)
        + dist (hg_mem.toLp g) f := by
          have hmul :
              ‖ouSemigroupFinLp (n := n) t‖ * dist f (hg_mem.toLp g) ≤ dist f (hg_mem.toLp g) :=
            mul_le_of_le_one_left (dist_nonneg) (ouSemigroupFinLp_contraction (n := n) t ht0)
          linarith
    _ < ε / 4 + ε / 2 + ε / 4 := by
          have hmid :
              dist (ouSemigroupFinLp (n := n) t (hg_mem.toLp g)) (hg_mem.toLp g) < ε / 2 :=
            hδ ht0 htδ
          have huApprox' : dist (hg_mem.toLp g) f < ε / 4 := by
            simpa [dist_comm] using huApprox
          nlinarith [huApprox, huApprox', hmid]
    _ = ε := by ring

noncomputable def markovSemigroup (n : ℕ) :
    MarkovSemigroup (Fin n → ℝ) where
  μ := γFin n
  hμ := inferInstance
  P := ouSemigroupFinLp (n := n)
  P_zero := ouSemigroupFinLp_zero (n := n)
  P_semigroup := ouSemigroupFinLp_semigroup (n := n)
  P_strong_cont := ouSemigroupFinLp_strong_cont (n := n)
  P_contraction := ouSemigroupFinLp_contraction (n := n)
  P_conservation := ouSemigroupFinLp_conservation (n := n)
  P_positivity := ouSemigroupFinLp_positivity (n := n)
  P_symmetric := ouSemigroupFinLp_symmetric (n := n)

end GaussianFin
