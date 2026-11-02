/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strong-`L²` difference-quotient limit for the Gaussian OU semigroup

G2 (a) of the Gross-discharge plan (`plans/gross-discharge.md`) — the
analytic core. For core `f`, the right difference quotient of the
`Lp`-carrier OU semigroup converges in `L²(γFin n)`-norm to the named
generator `ouGeneratorFin f = Δf − x·∇f`.

**This file is the Codex work item.** It now contains the full
theorem-level strong-`L²` difference-quotient discharge for the
finite-dimensional Gaussian OU semigroup, isolating the analytic
`GeneratorCompat` spine used by `EuclideanHypercontractive`.
-/

/- Port history note: inherited comments describing placeholders or legacy
postulates refer to earlier upstream development stages. Local proof status
is determined by the compiled axiom audit and the accompanying port note. -/

import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanGeneratorLp

open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace ContDiff

-- Port elaboration compatibility only; kernel checking and linters remain enabled.
set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local simp] Function.comp_def Pi.add_def Pi.sub_def Pi.neg_def Pi.smul_def

namespace GaussianFin

variable {n : ℕ}

/-- **`Fin n`-generic Stein/Gaussian-IBP wrapper** (Codex, 2026-05-16).
`EuclideanFin.stein_partialDeriv_ouShiftFin` is stated only for
`Fin (n+1)`; this lifts it to generic `Fin n` by case-splitting
(`n = 0`: `i : Fin 0` is vacuous via `Fin.elim0`; `n = m+1`: the
existing lemma). Unblocks the `Fin n` endpoint theorem below. -/
private theorem stein_partialDeriv_ouShiftFin_all {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin n =
      Real.sqrt (1 - Real.exp (-2 * t)) *
        ouSemigroupFin t (secondPartial i f) x := by
  cases n with
  | zero => exact (Fin.elim0 i)
  | succ m =>
      simpa using
        (stein_partialDeriv_ouShiftFin (n := m) (f := f) hf t i x)

private theorem tendsto_ouSemigroupFin_pointwise_atZero
    {g : (Fin n → ℝ) → ℝ} (hg_cont : Continuous g) {M : ℝ}
    (hg_bd : ∀ z, ‖g z‖ ≤ M) (x : Fin n → ℝ) :
    Tendsto (fun t : ℝ => ouSemigroupFin t g x) (𝓝[Set.Ici 0] 0) (𝓝 (g x)) := by
  show Tendsto (fun t : ℝ => ∫ y, g (ouShiftFin t x y) ∂γFin n) (𝓝[Set.Ici 0] 0) (𝓝 (g x))
  have h_target :
      Tendsto (fun t : ℝ => ∫ y, g (ouShiftFin t x y) ∂γFin n)
        (𝓝[Set.Ici 0] 0) (𝓝 (∫ _y : Fin n → ℝ, g x ∂γFin n)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M) ?_ ?_ (integrable_const M) ?_
    · filter_upwards with t
      have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      exact (hg_cont.comp hshift).aestronglyMeasurable
    · filter_upwards with t
      exact Filter.Eventually.of_forall (fun y => hg_bd (ouShiftFin t x y))
    · filter_upwards with y
      have harg : Tendsto (fun t : ℝ => ouShiftFin t x y) (𝓝[Set.Ici 0] 0) (𝓝 x) := by
        have hcont : Continuous (fun t : ℝ => ouShiftFin t x y) := by
          continuity
        have hzero : ouShiftFin 0 x y = x := by
          funext i
          simp [ouShiftFin]
        have h : Tendsto (fun t : ℝ => ouShiftFin t x y) (𝓝[Set.Ici 0] 0)
            (𝓝 (ouShiftFin 0 x y)) :=
          hcont.continuousAt.continuousWithinAt
        simpa [hzero] using h
      exact (hg_cont.tendsto x).comp harg
  simpa using h_target

private theorem continuousAt_t_ouSemigroupFin_of_bound
    {g : (Fin n → ℝ) → ℝ} (hg_cont : Continuous g) {M : ℝ}
    (hg_bd : ∀ z, ‖g z‖ ≤ M) (x : Fin n → ℝ) (t₀ : ℝ) :
    ContinuousAt (fun t : ℝ => ouSemigroupFin t g x) t₀ := by
  show Tendsto (fun t : ℝ => ∫ y, g (ouShiftFin t x y) ∂γFin n) (𝓝 t₀)
    (𝓝 (∫ y, g (ouShiftFin t₀ x y) ∂γFin n))
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ => M) ?_ ?_ (integrable_const M) ?_
  · filter_upwards with t
    have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
      continuity
    exact (hg_cont.comp hshift).aestronglyMeasurable
  · filter_upwards with t
    exact Filter.Eventually.of_forall (fun y => hg_bd (ouShiftFin t x y))
  · filter_upwards with y
    have harg : Tendsto (fun t : ℝ => ouShiftFin t x y) (𝓝 t₀) (𝓝 (ouShiftFin t₀ x y)) := by
      have hcont : Continuous (fun t : ℝ => ouShiftFin t x y) := by
        continuity
      exact hcont.tendsto t₀
    exact (hg_cont.tendsto _).comp harg

private theorem ouSemigroupFin_ae_eq_of_aeEq_local (t : ℝ) (ht : 0 ≤ t)
    {f g : (Fin n → ℝ) → ℝ} (hfg : f =ᵐ[γFin n] g) :
    ouSemigroupFin t f =ᵐ[γFin n] ouSemigroupFin t g := by
  let hmp :
      MeasurePreserving
        (mixCLM (n := n) (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))))
        ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n := n) (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))).continuous.measurable,
      by simpa using ou_kernel_map_fin (n := n) t ht⟩
  have hprod :
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        f (mixCLM (n := n) (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) z)) =ᵐ[((γFin n).prod (γFin n))]
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        g (mixCLM (n := n) (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) z)) :=
    hmp.quasiMeasurePreserving.ae hfg
  have hsec :
      ∀ᵐ x ∂γFin n,
        (fun y => f (mixCLM (n := n) (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) (x, y)))
          =ᵐ[γFin n]
        (fun y => g (mixCLM (n := n) (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) (x, y))) := by
    convert (MeasureTheory.Measure.ae_ae_eq_curry_of_prod hprod) using 1
    rfl
  filter_upwards [hsec] with x hx
  rw [ouSemigroupFin, ouSemigroupFin]
  exact integral_congr_ae hx

set_option maxHeartbeats 800000 in
private theorem hasDerivAt_t_ouSemigroupFin_pos_aux {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (x : Fin n → ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t : ℝ => ouSemigroupFin t f x)
      (∑ i : Fin n,
        (Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x
          - x i * (Real.exp (-t₀) * ouSemigroupFin t₀ (partialDeriv i f) x))) t₀ := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) ((hM (fun _ => 0)).1)
  let ε : ℝ := t₀ / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_lt : ε < t₀ := by
    dsimp [ε]
    linarith
  have h_nbhd : Set.Ioo ε (t₀ + 1) ∈ 𝓝 t₀ := by
    exact Ioo_mem_nhds hε_lt (by linarith)
  let F : ℝ → (Fin n → ℝ) → ℝ := fun t y => f (ouShiftFin t x y)
  let F' : ℝ → (Fin n → ℝ) → ℝ := fun t y =>
    ∑ i : Fin n,
      (-Real.exp (-t) * x i
        + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) *
        partialDeriv i f (ouShiftFin t x y)
  let B : ℝ := Real.sqrt (1 - Real.exp (-2 * ε))
  have hB_pos : 0 < B := by
    have hlt : Real.exp (-2 * ε) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      linarith
    have hinner : 0 < 1 - Real.exp (-2 * ε) := by
      linarith
    simpa [B] using Real.sqrt_pos.mpr hinner
  have hF_meas :
      ∀ t ∈ Set.Ioo ε (t₀ + 1), AEStronglyMeasurable (F t) (γFin n) := by
    intro t ht
    have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
      continuity
    exact (hf_core.measurable.comp hshift.measurable).aestronglyMeasurable
  have hF_int : Integrable (F t₀) (γFin n) := by
    refine Integrable.mono' (integrable_const M) (hF_meas t₀ ⟨hε_lt, by linarith⟩) ?_
    exact Filter.Eventually.of_forall (fun y => (hM (ouShiftFin t₀ x y)).1)
  have hF'_meas : AEStronglyMeasurable (F' t₀) (γFin n) := by
    change AEStronglyMeasurable
      (fun y : Fin n → ℝ =>
        ∑ i : Fin n,
          (-Real.exp (-t₀) * x i
            + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
            partialDeriv i f (ouShiftFin t₀ x y))
      (γFin n)
    have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t₀ x y) := by
      continuity
    exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) (by
      intro i hi
      have hcoeff_meas :
          Measurable (fun y : Fin n → ℝ =>
            (-Real.exp (-t₀) * x i : ℝ)
              + ((Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) : ℝ) * y i) := by
        have hconst : Measurable (fun _y : Fin n → ℝ => (-Real.exp (-t₀) * x i : ℝ)) :=
          measurable_const
        have hlin : Measurable (fun y : Fin n → ℝ =>
            ((Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) : ℝ) * y i) :=
          measurable_const.mul (measurable_pi_apply i)
        exact hconst.add hlin
      exact hcoeff_meas.mul ((hf_core.partial_measurable i).comp hshift.measurable))).aestronglyMeasurable
  have h_bound :
      ∀ᵐ y ∂γFin n, ∀ t ∈ Set.Ioo ε (t₀ + 1), ‖F' t y‖ ≤
        ∑ i : Fin n, M * (|x i| + (1 / B) * |y i|) := by
    filter_upwards with y t ht
    have hcoeff :
        ∀ i : Fin n,
          |(-Real.exp (-t) * x i
              + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i)|
            ≤ |x i| + (1 / B) * |y i| := by
      intro i
      have ht_pos : 0 < t := lt_trans hε_pos ht.1
      have h_exp_le : Real.exp (-t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      have h_exp2_le : Real.exp (-2 * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      have h_exp_nn : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
      have h_exp2_nn : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
      have h_sqrt_ge : B ≤ Real.sqrt (1 - Real.exp (-2 * t)) := by
        have hmono : Real.exp (-2 * t) ≤ Real.exp (-2 * ε) := by
          apply Real.exp_le_exp.mpr
          nlinarith [ht.1]
        have hinner_le : 1 - Real.exp (-2 * ε) ≤ 1 - Real.exp (-2 * t) := by
          linarith
        dsimp [B]
        exact Real.sqrt_le_sqrt hinner_le
      have h_ratio_le : Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t)) ≤ 1 / B := by
        calc
          Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))
              ≤ 1 / Real.sqrt (1 - Real.exp (-2 * t)) := by
                  gcongr
          _ ≤ 1 / B := by
                  exact one_div_le_one_div_of_le hB_pos h_sqrt_ge
      calc
        |(-Real.exp (-t) * x i
            + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i)|
            ≤ |(-Real.exp (-t) * x i)| +
                |(Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i| :=
              abs_add_le _ _
        _ = Real.exp (-t) * |x i| +
              (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * |y i| := by
              rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg h_exp_nn,
                abs_of_nonneg (div_nonneg h_exp2_nn (Real.sqrt_nonneg _))]
        _ ≤ 1 * |x i| + (1 / B) * |y i| := by
              gcongr
        _ = |x i| + (1 / B) * |y i| := by ring
    change
      ‖∑ i : Fin n,
          (-Real.exp (-t) * x i
            + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) *
            partialDeriv i f (ouShiftFin t x y)‖
        ≤ ∑ i : Fin n, M * (|x i| + (1 / B) * |y i|)
    calc
      ‖F' t y‖
          ≤ ∑ i : Fin n,
              ‖(-Real.exp (-t) * x i
                + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) *
                partialDeriv i f (ouShiftFin t x y)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n,
            (|x i| + (1 / B) * |y i|) * M := by
              refine Finset.sum_le_sum ?_
              intro i hi
              calc
                ‖(-Real.exp (-t) * x i
                    + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) *
                    partialDeriv i f (ouShiftFin t x y)‖
                    = |(-Real.exp (-t) * x i
                        + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i)| *
                        ‖partialDeriv i f (ouShiftFin t x y)‖ := by
                          rw [norm_mul, Real.norm_eq_abs]
                _ ≤ (|x i| + (1 / B) * |y i|) * M := by
                    exact mul_le_mul (hcoeff i) ((hM (ouShiftFin t x y)).2.1 i)
                      (norm_nonneg _) (by positivity)
      _ = ∑ i : Fin n, M * (|x i| + (1 / B) * |y i|) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  have h_bound_int : Integrable (fun y : Fin n → ℝ =>
      ∑ i : Fin n, M * (|x i| + (1 / B) * |y i|)) (γFin n) := by
    have hterm :
        ∀ i : Fin n, Integrable (fun y : Fin n → ℝ => M * (|x i| + (1 / B) * |y i|)) (γFin n) := by
      intro i
      have h_eval : Integrable (fun y : Fin n → ℝ => |y i|) (γFin n) := integrable_abs_eval_γFin i
      simpa [mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using (integrable_const (M * |x i|)).add (h_eval.const_mul (M * (1 / B)))
    refine integrable_finsetSum (s := Finset.univ)
      (f := fun i (y : Fin n → ℝ) => M * (|x i| + (1 / B) * |y i|)) ?_
    intro i hi
    exact hterm i
  have h_diff :
      ∀ᵐ y ∂γFin n, ∀ t ∈ Set.Ioo ε (t₀ + 1), HasDerivAt (fun s => F s y) (F' t y) t := by
    filter_upwards with y t ht
    have h_shift :
        HasDerivAt (fun s : ℝ => ouShiftFin s x y)
          (fun i => -Real.exp (-t) * x i
            + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) t := by
      rw [hasDerivAt_pi]
      intro i
      have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s) * x i) (-Real.exp (-t) * x i) t := by
        have hneg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := by
          simpa using (hasDerivAt_id t).neg
        have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * (-1)) t := hneg.exp
        convert hexp.mul_const (x i) using 1; ring
      have h2 :
          HasDerivAt (fun s : ℝ => Real.sqrt (1 - Real.exp (-2 * s)) * y i)
            ((Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) t := by
        exact (Gaussian1D.hasDerivAt_b t (lt_trans hε_pos ht.1)).mul_const (y i)
      simpa [ouShiftFin] using h1.add h2
    have h_f :
        HasFDerivAt f (fderiv ℝ f (ouShiftFin t x y)) (ouShiftFin t x y) :=
      ((hf_smooth.differentiable (by simp)).differentiableAt).hasFDerivAt
    have h_comp := h_f.comp_hasDerivAt t h_shift
    have hsum := fderiv_apply_eq_sum_partial hf_smooth (ouShiftFin t x y)
      (fun i => -Real.exp (-t) * x i
        + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i)
    rw [hsum] at h_comp
    simpa [F, F'] using h_comp
  have hF_meas_ev : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) (γFin n) :=
    Filter.eventually_of_mem h_nbhd hF_meas
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le h_nbhd
      hF_meas_ev hF_int hF'_meas h_bound h_bound_int h_diff
  have h_term_int :
      ∀ i : Fin n,
        Integrable
          (fun y : Fin n → ℝ =>
            (-Real.exp (-t₀) * x i
              + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
              partialDeriv i f (ouShiftFin t₀ x y)) (γFin n) := by
    intro i
    refine Integrable.mono'
      ((integrable_const (M * |x i|)).add
        ((integrable_abs_eval_γFin i).const_mul (M * (Real.exp (-2 * t₀) /
          Real.sqrt (1 - Real.exp (-2 * t₀)))))) ?_ ?_
    · have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t₀ x y) := by
        continuity
      exact ((((measurable_const.mul measurable_const).add
        ((measurable_const.mul (measurable_pi_apply i)))).mul
        ((hf_core.partial_measurable i).comp hshift.measurable)).aestronglyMeasurable)
    · filter_upwards with y
      have hcoef :
          |(-Real.exp (-t₀) * x i
              + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i)|
            ≤ Real.exp (-t₀) * |x i| +
              (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * |y i| := by
        calc
          |(-Real.exp (-t₀) * x i
              + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i)|
              ≤ |(-Real.exp (-t₀) * x i)| +
                  |(Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i| :=
                abs_add_le _ _
          _ = Real.exp (-t₀) * |x i| +
              (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * |y i| := by
                rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (Real.exp_pos _).le,
                  abs_of_nonneg (div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))]
      calc
        ‖(-Real.exp (-t₀) * x i
            + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
            partialDeriv i f (ouShiftFin t₀ x y)‖
            = |(-Real.exp (-t₀) * x i
                + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i)| *
                ‖partialDeriv i f (ouShiftFin t₀ x y)‖ := by
                    rw [norm_mul, Real.norm_eq_abs]
        _ ≤ (Real.exp (-t₀) * |x i| +
              (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * |y i|) * M := by
              exact mul_le_mul hcoef ((hM (ouShiftFin t₀ x y)).2.1 i) (norm_nonneg _) (by positivity)
        _ ≤ M * |x i| + (M * (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀)))) * |y i| := by
              have h_exp_le : Real.exp (-t₀) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
              have h1 : (Real.exp (-t₀) * |x i|) * M ≤ M * |x i| := by
                calc
                  (Real.exp (-t₀) * |x i|) * M ≤ (1 * |x i|) * M := by
                    gcongr
                  _ = M * |x i| := by ring
              ring_nf
              linarith [h1]
  have h_eval :
      ∫ y, F' t₀ y ∂γFin n
        = ∑ i : Fin n,
            (Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x
              - x i * (Real.exp (-t₀) * ouSemigroupFin t₀ (partialDeriv i f) x)) := by
    rw [show (∫ y, F' t₀ y ∂γFin n) =
        ∫ y, ∑ i : Fin n,
          ((-Real.exp (-t₀) * x i
            + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
            partialDeriv i f (ouShiftFin t₀ x y)) ∂γFin n from rfl]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t₀ x y) := by
        continuity
      have hpartial_meas :
          Measurable (fun y : Fin n → ℝ => partialDeriv i f (ouShiftFin t₀ x y)) :=
        (hf_core.partial_measurable i).comp hshift.measurable
      have hpartial_int :
          Integrable (fun y : Fin n → ℝ => partialDeriv i f (ouShiftFin t₀ x y)) (γFin n) := by
        refine integrable_of_bound (M := M) hpartial_meas ?_
        intro y
        exact (hM (ouShiftFin t₀ x y)).2.1 i
      have h1 :
          Integrable (fun y : Fin n → ℝ =>
            (-Real.exp (-t₀) * x i) * partialDeriv i f (ouShiftFin t₀ x y)) (γFin n) := by
        exact hpartial_int.const_mul (-Real.exp (-t₀) * x i)
      have h2 :
          Integrable (fun y : Fin n → ℝ =>
            ((Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
              partialDeriv i f (ouShiftFin t₀ x y)) (γFin n) := by
        have hy_partial :
            Integrable (fun y : Fin n → ℝ => y i * partialDeriv i f (ouShiftFin t₀ x y)) (γFin n) := by
          refine Integrable.mono' ((integrable_abs_eval_γFin i).const_mul M)
            ((measurable_pi_apply i).mul hpartial_meas).aestronglyMeasurable ?_
          filter_upwards with y
          calc
            ‖y i * partialDeriv i f (ouShiftFin t₀ x y)‖
                = |y i| * ‖partialDeriv i f (ouShiftFin t₀ x y)‖ := by
                    rw [norm_mul, Real.norm_eq_abs]
            _ ≤ |y i| * M := by
                  exact mul_le_mul_of_nonneg_left ((hM (ouShiftFin t₀ x y)).2.1 i) (abs_nonneg _)
            _ = M * |y i| := by ring
        simpa [mul_assoc] using
          hy_partial.const_mul (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀)))
      calc
        ∫ y,
            ((-Real.exp (-t₀) * x i
              + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
              partialDeriv i f (ouShiftFin t₀ x y)) ∂γFin n
            = ∫ y,
                (-Real.exp (-t₀) * x i) * partialDeriv i f (ouShiftFin t₀ x y)
                  + ((Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
                    partialDeriv i f (ouShiftFin t₀ x y) ∂γFin n := by
                      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                      intro y
                      ring
        _ = (-Real.exp (-t₀) * x i) * ouSemigroupFin t₀ (partialDeriv i f) x
              + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) *
                ∫ y, y i * partialDeriv i f (ouShiftFin t₀ x y) ∂γFin n := by
                  rw [integral_add h1 h2, integral_const_mul]
                  have hcongr :
                      (∫ y,
                        ((Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
                          partialDeriv i f (ouShiftFin t₀ x y) ∂γFin n)
                        =
                      ∫ y,
                        (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) *
                          (y i * partialDeriv i f (ouShiftFin t₀ x y)) ∂γFin n := by
                    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                    intro y
                    ring
                  rw [hcongr, integral_const_mul]
                  simp [ouSemigroupFin]
        _ = (-Real.exp (-t₀) * x i) * ouSemigroupFin t₀ (partialDeriv i f) x
              + Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x := by
                  rw [stein_partialDeriv_ouShiftFin_all hf_core t₀ i x]
                  have hsqrt_pos : 0 < Real.sqrt (1 - Real.exp (-2 * t₀)) := by
                    apply Real.sqrt_pos.mpr
                    have hlt : Real.exp (-2 * t₀) < 1 := by
                      apply Real.exp_lt_one_iff.mpr
                      linarith
                    linarith
                  have hsqrt_ne : Real.sqrt (1 - Real.exp (-2 * t₀)) ≠ 0 := hsqrt_pos.ne'
                  rw [div_eq_mul_inv]
                  calc
                    (-Real.exp (-t₀) * x i) * ouSemigroupFin t₀ (partialDeriv i f) x +
                        Real.exp (-2 * t₀) * (Real.sqrt (1 - Real.exp (-2 * t₀)))⁻¹ *
                          (Real.sqrt (1 - Real.exp (-2 * t₀)) *
                            ouSemigroupFin t₀ (secondPartial i f) x)
                        =
                      (-Real.exp (-t₀) * x i) * ouSemigroupFin t₀ (partialDeriv i f) x +
                        Real.exp (-2 * t₀) *
                          ((Real.sqrt (1 - Real.exp (-2 * t₀)))⁻¹ *
                            Real.sqrt (1 - Real.exp (-2 * t₀))) *
                          ouSemigroupFin t₀ (secondPartial i f) x
                        := by ring
                    _ =
                      (-Real.exp (-t₀) * x i) * ouSemigroupFin t₀ (partialDeriv i f) x +
                        Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x := by
                          rw [inv_mul_cancel₀ hsqrt_ne]
                          ring_nf
        _ = Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x
              - x i * (Real.exp (-t₀) * ouSemigroupFin t₀ (partialDeriv i f) x) := by
                  ring
    · intro i hi
      exact h_term_int i
  have h_lhs : (fun t : ℝ => ∫ y, F t y ∂γFin n) = fun t => ouSemigroupFin t f x := rfl
  rw [h_lhs] at h_deriv
  rw [h_eval] at h_deriv
  exact h_deriv

private theorem hasDerivAt_t_ouSemigroupFin_pos {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (x : Fin n → ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t : ℝ => ouSemigroupFin t f x)
      (ouGeneratorFin (ouSemigroupFin t₀ f) x) t₀ := by
  have haux := hasDerivAt_t_ouSemigroupFin_pos_aux hf x ht₀
  have hcore_t : IsCoreFin (ouSemigroupFin t₀ f) :=
    ouSemigroupFin_preserves_IsCore t₀ ht₀.le hf
  have hrewrite :
      (∑ i : Fin n,
        (Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x
          - x i * (Real.exp (-t₀) * ouSemigroupFin t₀ (partialDeriv i f) x)))
        = ouGeneratorFin (ouSemigroupFin t₀ f) x := by
    rw [ouGeneratorFin_apply]
    have hsum_second :
        (∑ i : Fin n, Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x) =
          ∑ i : Fin n, secondPartial i (ouSemigroupFin t₀ f) x := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [secondPartial_eq_section_deriv_of_contDiff hcore_t.contDiff i x,
        section_secondDeriv_ouSemigroupFin_eq hf t₀ i x]
      simp
    have hsum_first :
        (∑ i : Fin n, x i * (Real.exp (-t₀) * ouSemigroupFin t₀ (partialDeriv i f) x)) =
          ∑ i : Fin n, x i * partialDeriv i (ouSemigroupFin t₀ f) x := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [partialDeriv_ouSemigroupFin_eq (n := n) t₀ ht₀.le hf i]
    rw [Finset.sum_sub_distrib, hsum_second, hsum_first]
  convert haux using 1
  exact hrewrite.symm

private theorem hasDerivWithinAt_t_ouSemigroupFin_zero_core {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (x : Fin n → ℝ) :
    HasDerivWithinAt (fun t : ℝ => ouSemigroupFin t f x)
      (ouGeneratorFin f x) (Set.Ici 0) 0 := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    (f := fun t : ℝ => ouSemigroupFin t f x) (e := ouGeneratorFin f x) (a := 0) ?_ ?_
    self_mem_nhdsWithin ?_
  · intro t ht
    exact (hasDerivAt_t_ouSemigroupFin_pos hf_core x ht).differentiableAt.differentiableWithinAt
  · have hcont := tendsto_ouSemigroupFin_pointwise_atZero hf_smooth.continuous (fun z => (hM z).1) x
    show ContinuousWithinAt (fun t : ℝ => ouSemigroupFin t f x) (Set.Ioi 0) 0
    rw [ContinuousWithinAt, ouSemigroupFin_zero]
    exact hcont.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  · have hderiv_eq :
      ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
        deriv (fun t : ℝ => ouSemigroupFin t f x) t
          = ∑ i : Fin n,
              (Real.exp (-2 * t) * ouSemigroupFin t (secondPartial i f) x
                - x i * (Real.exp (-t) * ouSemigroupFin t (partialDeriv i f) x)) := by
      have hmem : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, t ∈ Set.Ioi (0 : ℝ) := self_mem_nhdsWithin
      filter_upwards [hmem] with t ht
      exact (hasDerivAt_t_ouSemigroupFin_pos_aux hf_core x ht).deriv
    have h_second :
        Tendsto (fun t : ℝ =>
          ∑ i : Fin n, Real.exp (-2 * t) * ouSemigroupFin t (secondPartial i f) x)
          (𝓝[Set.Ioi 0] 0) (𝓝 (∑ i : Fin n, secondPartial i f x)) := by
      refine tendsto_finsetSum Finset.univ (fun i _ => ?_)
      have h_exp : Tendsto (fun t : ℝ => Real.exp (-2 * t)) (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
        have hcont : Continuous (fun t : ℝ => Real.exp (-2 * t)) := by
          continuity
        have h : Tendsto (fun t : ℝ => Real.exp (-2 * t)) (𝓝[Set.Ioi 0] 0)
            (𝓝 (Real.exp (-2 * 0))) :=
          hcont.continuousAt.continuousWithinAt
        simpa using h
      have h_pt :
          Tendsto (fun t : ℝ => ouSemigroupFin t (secondPartial i f) x)
            (𝓝[Set.Ioi 0] 0) (𝓝 (secondPartial i f x)) := by
        have := tendsto_ouSemigroupFin_pointwise_atZero
          (hf_core.secondPartial_continuous i) (fun z => (hM z).2.2 i) x
        exact this.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      simpa using h_exp.mul h_pt
    have h_first :
        Tendsto (fun t : ℝ =>
          ∑ i : Fin n, x i * (Real.exp (-t) * ouSemigroupFin t (partialDeriv i f) x))
          (𝓝[Set.Ioi 0] 0) (𝓝 (∑ i : Fin n, x i * partialDeriv i f x)) := by
      refine tendsto_finsetSum Finset.univ (fun i _ => ?_)
      have h_exp : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
        have hcont : Continuous (fun t : ℝ => Real.exp (-t)) := by
          continuity
        have h : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[Set.Ioi 0] 0)
            (𝓝 (Real.exp (-0))) :=
          hcont.continuousAt.continuousWithinAt
        simpa using h
      have h_pt :
          Tendsto (fun t : ℝ => ouSemigroupFin t (partialDeriv i f) x)
            (𝓝[Set.Ioi 0] 0) (𝓝 (partialDeriv i f x)) := by
        have := tendsto_ouSemigroupFin_pointwise_atZero
          (hf_core.partial_continuous i) (fun z => (hM z).2.1 i) x
        exact this.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      simpa [mul_assoc] using (h_exp.mul h_pt).const_mul (x i)
    have h_lim :
        Tendsto
          (fun t : ℝ =>
            ∑ i : Fin n,
              (Real.exp (-2 * t) * ouSemigroupFin t (secondPartial i f) x
                - x i * (Real.exp (-t) * ouSemigroupFin t (partialDeriv i f) x)))
          (𝓝[Set.Ioi 0] 0)
          (𝓝 (ouGeneratorFin f x)) := by
      simpa [ouGeneratorFin_apply] using h_second.sub h_first
    have hderiv_eq' :
        (fun t : ℝ => deriv (fun t : ℝ => ouSemigroupFin t f x) t) =ᶠ[𝓝[Set.Ioi 0] 0]
          (fun t : ℝ =>
            ∑ i : Fin n,
              (Real.exp (-2 * t) * ouSemigroupFin t (secondPartial i f) x
                - x i * (Real.exp (-t) * ouSemigroupFin t (partialDeriv i f) x))) := hderiv_eq
    exact Tendsto.congr' hderiv_eq'.symm h_lim

/-- **Ornstein–Uhlenbeck pointwise heat equation at `t = 0⁺`** (the
right-endpoint of the Mehler-semigroup time derivative).

For `f : (Fin n → ℝ) → ℝ` that is `C^∞` with uniformly bounded value,
first and second coordinate derivatives, the explicit Mehler integral
`t ↦ ∫ f(e^{-t}x + √(1-e^{-2t})·y) d(⊗ⁿ N(0,1))(y)` has right
derivative at `0` equal to the OU generator `Lf(x) = Δf(x) − x·∇f(x)`.

**General (no project definitions).** Stated purely in Mathlib terms
— `fderiv`, `Pi.single`, `Real.exp`/`Real.sqrt`,
`MeasureTheory.Measure.pi`, `ProbabilityTheory.gaussianReal`,
`HasDerivWithinAt`, `Set.Ici` — so it is a reusable, vetting-amenable
textbook statement rather than a project-specific stopgap. The
project-specific `hasDerivWithinAt_t_ouSemigroupFin_zero` is derived
from it by unfolding the (thin) project definitions.

Reference: Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
Diffusion Operators* (2014), §2.7 (the Ornstein–Uhlenbeck/heat
semigroup and its generator); Mehler's formula. **Vetted Standard /
Likely correct** (Gemini `gemini-3-pro-preview`, 2026-05-16; recorded
in `AXIOM_AUDIT.md`): well-formed; matches BGL §2.7 with
self-consistent variance-1 Mehler constants (no rescaling); non-vacuous;
**pure-second-partial bounds sufficient** — via Itô/Dynkin
`Pₜf − f = ∫₀ᵗ Pₛ(Lf) ds` the martingale term vanishes in
expectation, so only `|∇f|`,`|Δf|` boundedness is needed (no mixed-
partial, third-derivative, or growth hypotheses); right-derivative
endpoint form correct. Discharge route: parametric differentiation
under the integral with the Pi-valued chain rule through the Mehler
shift + the scaling identity `∂ᵢ²(Pₜf) = e^{-2t} Pₜ(∂ᵢ²f)` (see the
two-interface obstacle note on the project lemma below). -/
theorem gaussianOU_heatEquation_within_zero {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf_smooth : ContDiff ℝ ∞ f) (M : ℝ)
    (hf_bd : ∀ x : Fin n → ℝ,
      ‖f x‖ ≤ M ∧
      (∀ i : Fin n, ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ M) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
            (Pi.single i 1)‖ ≤ M))
    (x : Fin n → ℝ) :
    HasDerivWithinAt
      (fun t : ℝ =>
        ∫ y,
          f (fun i => Real.exp (-t) * x i
              + Real.sqrt (1 - Real.exp (-2 * t)) * y i)
          ∂(MeasureTheory.Measure.pi
              (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
      ((∑ i : Fin n,
          fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
            (Pi.single i 1))
        - ∑ i : Fin n, x i * fderiv ℝ f x (Pi.single i 1))
      (Set.Ici 0) 0 := by
  have hf : IsCoreFin f := by
    refine ⟨hf_smooth, M, ?_⟩
    convert hf_bd using 1
    rfl
  convert hasDerivWithinAt_t_ouSemigroupFin_zero_core hf x using 1 <;> rfl

/-- **The precise blocker (Codex 2026-05-16): the nD pointwise OU
heat equation at `t = 0⁺`.** The branch controls *spatial*
derivatives of `ouSemigroupFin t f` and has the scalar/L²-continuity
endgame, but exposes **no reusable multivariate pointwise
time-derivative** for `τ ↦ ouSemigroupFin τ f x`. This lemma is
exactly that missing prerequisite (right-derivative-at-0 form, which
Codex confirmed suffices): `P_0 f = f`, so the right `t`-derivative of
`τ ↦ (P_τ f) x` at `0` is `(L f) x = ouGeneratorFin f x`.

Proof route: tensor/Fubini lift of the proved 1D
`Gaussian1D.hasDerivAt_t_ouSemigroup'` (G1) through
`ouSemigroupFin_section_eq_ouSemigroup` / `ouSemigroupFin_insertNth_eq`
+ per-coordinate product rule + the `t→0⁺` endpoint
(`hasDerivWithinAt_Ici_of_tendsto_deriv`, as used for the 1D /
quadratic discharges). This is the genuine analytic crux; isolated as
its own target so it can be filled (Codex) independently of the DCT
upgrade below.

**Remaining obstacle (Codex, 2026-05-16; the `Fin n` Stein wrapper
above is done).** Two specific Lean interfaces fight the parametric
heat-equation proof: (1) the `HasDerivAt`-under-the-integral for
`τ ↦ ouSemigroupFin τ f x` needs a *Pi-valued chain rule through
`ouShiftFin`*, with the derivative integrand `F'` presented to
simultaneously satisfy `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
finite-sum measurability, and the later integral algebra; (2) then the
Mehler-scaling identity
`secondPartial i (ouSemigroupFin t f) x
  = exp (-2*t) * ouSemigroupFin t (secondPartial i f) x`
must be bridged through `section_secondDeriv` /
`section_secondDeriv_ouSemigroupFin_eq`. -/
theorem hasDerivWithinAt_t_ouSemigroupFin_zero {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (x : Fin n → ℝ) :
    HasDerivWithinAt (fun t : ℝ => ouSemigroupFin t f x)
      (ouGeneratorFin f x) (Set.Ici 0) 0 := by
  exact hasDerivWithinAt_t_ouSemigroupFin_zero_core hf x

private theorem tendsto_diffQuot_ouSemigroupFin_zero {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (x : Fin n → ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ * (ouSemigroupFin t f x - f x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ouGeneratorFin f x)) := by
  have hderiv :
      HasDerivWithinAt (fun t : ℝ => ouSemigroupFin t f x)
        (ouGeneratorFin f x) (Set.Ioi 0) 0 :=
    (hasDerivWithinAt_t_ouSemigroupFin_zero hf x).Ioi_of_Ici
  rw [hasDerivWithinAt_iff_tendsto_slope'] at hderiv
  · refine hderiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    rw [slope_def_field, ouSemigroupFin_zero, sub_zero]
    field_simp [ht0]
  · simp

private theorem norm_ouGeneratorFin_le_of_coreBound {f : (Fin n → ℝ) → ℝ}
    (M : ℝ)
    (hM : ∀ x : Fin n → ℝ,
      ‖f x‖ ≤ M ∧
      (∀ i : Fin n, ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ M) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x (Pi.single i 1)‖ ≤ M))
    (x : Fin n → ℝ) :
    ‖ouGeneratorFin f x‖ ≤ (n : ℝ) * M + M * ∑ i : Fin n, |x i| := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) ((hM (fun _ => 0)).1)
  rw [ouGeneratorFin_apply, Real.norm_eq_abs]
  calc
    |∑ i : Fin n, secondPartial i f x - ∑ i : Fin n, x i * partialDeriv i f x|
      ≤ |∑ i : Fin n, secondPartial i f x| + |∑ i : Fin n, x i * partialDeriv i f x| := by
        simpa [sub_eq_add_neg] using
          (abs_add_le (∑ i : Fin n, secondPartial i f x)
            (-∑ i : Fin n, x i * partialDeriv i f x))
    _ ≤ ∑ i : Fin n, |secondPartial i f x| + ∑ i : Fin n, |x i * partialDeriv i f x| := by
      gcongr
      · exact Finset.abs_sum_le_sum_abs _ _
      · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, M + ∑ i : Fin n, |x i| * M := by
      refine add_le_add ?_ ?_
      · refine Finset.sum_le_sum ?_
        intro i hi
        convert (hM x).2.2 i using 1
        rfl
      · refine Finset.sum_le_sum ?_
        intro i hi
        have hpi : |partialDeriv i f x| ≤ M := by
          simpa [partialDeriv, Real.norm_eq_abs] using (hM x).2.1 i
        calc
          |x i * partialDeriv i f x| = |x i| * |partialDeriv i f x| := abs_mul _ _
          _ ≤ |x i| * M := mul_le_mul_of_nonneg_left hpi (abs_nonneg _)
    _ = (n : ℝ) * M + M * ∑ i : Fin n, |x i| := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hsum : (∑ i : Fin n, |x i| * M) = M * ∑ i : Fin n, |x i| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      rw [hsum]
      simp [Finset.card_univ]

private theorem norm_diffQuot_ouSemigroupFin_le_of_coreBound {f : (Fin n → ℝ) → ℝ}
    (hf_smooth : ContDiff ℝ ∞ f) (M : ℝ)
    (hM : ∀ x : Fin n → ℝ,
      ‖f x‖ ≤ M ∧
      (∀ i : Fin n, ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ M) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x (Pi.single i 1)‖ ≤ M))
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    ‖t⁻¹ * (ouSemigroupFin t f x - f x)‖ ≤ (n : ℝ) * M + M * ∑ i : Fin n, |x i| := by
  let hf : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  let H : ℝ := (n : ℝ) * M + M * ∑ i : Fin n, |x i|
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) ((hM (fun _ => 0)).1)
  have hH0 : (0 : ℝ) ≤ H := by
    dsimp [H]
    positivity
  let φ : ℝ → ℝ := fun s =>
    ∑ i : Fin n,
      (Real.exp (-2 * s) * ouSemigroupFin s (secondPartial i f) x
        - x i * (Real.exp (-s) * ouSemigroupFin s (partialDeriv i f) x))
  have hcont : ContinuousOn (fun s : ℝ => ouSemigroupFin s f x) (Set.Icc 0 t) := by
    intro s hs
    exact (continuousAt_t_ouSemigroupFin_of_bound hf_smooth.continuous
      (fun z => (hM z).1) x s).continuousWithinAt
  have hderiv :
      ∀ s ∈ Set.Ioo 0 t, HasDerivAt (fun r : ℝ => ouSemigroupFin r f x) (φ s) s := by
    intro s hs
    simpa [φ] using hasDerivAt_t_ouSemigroupFin_pos_aux hf x hs.1
  have hφ_cont : Continuous φ := by
    refine continuous_finsetSum _ ?_
    intro i hi
    have hsec :
        Continuous (fun s : ℝ => Real.exp (-2 * s) * ouSemigroupFin s (secondPartial i f) x) := by
      have hexp : Continuous (fun s : ℝ => Real.exp (-2 * s)) := by
        continuity
      have hou : Continuous (fun s : ℝ => ouSemigroupFin s (secondPartial i f) x) := by
        refine continuous_iff_continuousAt.mpr ?_
        intro s
        exact continuousAt_t_ouSemigroupFin_of_bound (hf.secondPartial_continuous i)
          (fun z => (hM z).2.2 i) x s
      exact hexp.mul hou
    have hfir :
        Continuous (fun s : ℝ => x i * (Real.exp (-s) * ouSemigroupFin s (partialDeriv i f) x)) := by
      have hexp : Continuous (fun s : ℝ => Real.exp (-s)) := by
        continuity
      have hou : Continuous (fun s : ℝ => ouSemigroupFin s (partialDeriv i f) x) := by
        refine continuous_iff_continuousAt.mpr ?_
        intro s
        exact continuousAt_t_ouSemigroupFin_of_bound (hf.partial_continuous i)
          (fun z => (hM z).2.1 i) x s
      exact continuous_const.mul (hexp.mul hou)
    exact hsec.sub hfir
  have hφ_bd : ∀ s ∈ Set.Icc 0 t, ‖φ s‖ ≤ H := by
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1
    calc
      ‖φ s‖ = |∑ i : Fin n,
          (Real.exp (-2 * s) * ouSemigroupFin s (secondPartial i f) x
            - x i * (Real.exp (-s) * ouSemigroupFin s (partialDeriv i f) x))| := by
          simp [φ, Real.norm_eq_abs]
      _ = |∑ i : Fin n, Real.exp (-2 * s) * ouSemigroupFin s (secondPartial i f) x
            - ∑ i : Fin n, x i * (Real.exp (-s) * ouSemigroupFin s (partialDeriv i f) x)| := by
          rw [Finset.sum_sub_distrib]
      _ ≤ |∑ i : Fin n, Real.exp (-2 * s) * ouSemigroupFin s (secondPartial i f) x|
          + |∑ i : Fin n, x i * (Real.exp (-s) * ouSemigroupFin s (partialDeriv i f) x)| := by
            simpa [sub_eq_add_neg] using
              (abs_add_le (∑ i : Fin n, Real.exp (-2 * s) * ouSemigroupFin s (secondPartial i f) x)
                (-∑ i : Fin n, x i * (Real.exp (-s) * ouSemigroupFin s (partialDeriv i f) x)))
      _ ≤ ∑ _i : Fin n, M + ∑ i : Fin n, |x i| * M := by
        gcongr
        · calc
            |∑ i : Fin n, Real.exp (-2 * s) * ouSemigroupFin s (secondPartial i f) x|
              ≤ ∑ i : Fin n, |Real.exp (-2 * s) * ouSemigroupFin s (secondPartial i f) x| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i : Fin n, M := by
              refine Finset.sum_le_sum ?_
              intro i hi
              calc
                |Real.exp (-2 * s) * ouSemigroupFin s (secondPartial i f) x|
                    = Real.exp (-2 * s) *
                        ‖ouSemigroupFin s (secondPartial i f) x‖ := by
                          rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs]
                _ ≤ Real.exp (-2 * s) * M := by
                    gcongr
                    exact norm_ouSemigroupFin_le_of_bound (n := n) s
                      (hf.secondPartial_measurable i) (fun z => (hM z).2.2 i) x
                _ ≤ M := by
                    have hexp_le : Real.exp (-2 * s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
                    nlinarith
        · calc
            |∑ i : Fin n, x i * (Real.exp (-s) * ouSemigroupFin s (partialDeriv i f) x)|
              ≤ ∑ i : Fin n, |x i * (Real.exp (-s) * ouSemigroupFin s (partialDeriv i f) x)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i : Fin n, |x i| * M := by
              refine Finset.sum_le_sum ?_
              intro i hi
              calc
                |x i * (Real.exp (-s) * ouSemigroupFin s (partialDeriv i f) x)|
                    = |x i| * (Real.exp (-s) * ‖ouSemigroupFin s (partialDeriv i f) x‖) := by
                        rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs]
                _ ≤ |x i| * (Real.exp (-s) * M) := by
                    gcongr
                    exact norm_ouSemigroupFin_le_of_bound (n := n) s
                      (hf.partial_measurable i) (fun z => (hM z).2.1 i) x
                _ ≤ |x i| * M := by
                    have hexp_le : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
                    calc
                      |x i| * (Real.exp (-s) * M) ≤ |x i| * (1 * M) := by
                        gcongr
                    _ = |x i| * M := by ring
      _ = H := by
        dsimp [H]
        rw [Finset.sum_const, nsmul_eq_mul]
        have hsum : (∑ i : Fin n, |x i| * M) = M * ∑ i : Fin n, |x i| := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        rw [hsum]
        simp [Finset.card_univ]
  have hφ_int : IntervalIntegrable φ volume 0 t := by
    exact hφ_cont.continuousOn.intervalIntegrable_of_Icc ht.le
  have hFTC :
      ∫ s in 0..t, φ s = ouSemigroupFin t f x - f x := by
    simpa [ouSemigroupFin_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun s : ℝ => ouSemigroupFin s f x)
        (f' := φ) ht.le hcont hderiv hφ_int
  calc
    ‖t⁻¹ * (ouSemigroupFin t f x - f x)‖ = |t⁻¹| * ‖∫ s in 0..t, φ s‖ := by
      rw [hFTC, norm_mul, Real.norm_eq_abs]
    _ ≤ |t⁻¹| * (H * |t - 0|) := by
      gcongr
      exact intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s hs => by
          have hs' : s ∈ Set.Icc 0 t := by
            rw [Set.uIoc_of_le ht.le] at hs
            exact ⟨le_of_lt hs.1, hs.2⟩
          exact hφ_bd s hs')
    _ = H := by
      rw [abs_of_pos (inv_pos.mpr ht), sub_zero, abs_of_pos ht]
      field_simp [ht.ne']

/-- **OU difference-quotient `→` generator, strong `L²`** (the DCT
upgrade of the pointwise heat equation — third Gross-discharge crux).

For `f : (Fin n → ℝ) → ℝ` that is `C^∞` with uniformly bounded value,
first and second coordinate derivatives, and *any* operator family
`P` acting on `Lp ℝ 2 (⊗ⁿ N(0,1))` whose a.e. representative is the
Mehler integral, the right difference quotient
`t⁻¹ • (P t [f] − [f])` converges in `L²`-norm as `t → 0⁺` to the
`Lp` class of the OU generator `Δf − x·∇f`.

**General (no project definitions).** Stated purely in Mathlib terms
— `fderiv`, `Pi.single`, `Real.exp`/`Real.sqrt`,
`MeasureTheory.Measure.pi`, `ProbabilityTheory.gaussianReal`,
`MemLp`/`MemLp.toLp`, `Lp`, `Filter.Tendsto`, `nhdsWithin` — with the
semigroup supplied as a parameter `P` characterized only by its
generic Mehler a.e. action `hP`, so it is a reusable,
vetting-amenable textbook statement rather than a project-specific
stopgap. The project lemma `ouSemigroupFinLp_diffQuot_tendsto` is
derived from it by instantiating `P := ouSemigroupFinLp` and
`hP := ouSemigroupFinLp_coeFn_ae` and unfolding the thin project
definitions.

Reference: Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
Diffusion Operators* (2014), §2.7 / §1.6 (the OU semigroup is
strongly continuous on `L²(γ)` with generator `L = Δ − x·∇` on the
smooth core; the difference quotient converges to `Lf` in `L²`).
Strategy: the pointwise right limit `(P_t f − f)/t → Lf` is the heat
equation `gaussianOU_heatEquation_within_zero`; the quotient is
dominated by a fixed `L²(γ)` function (mean-value bound from the
*segment-wide* positive-time derivative + core `IsCoreFin` bounds and
Mehler contraction), so dominated convergence upgrades the pointwise
limit to the strong `L²` limit. The segment uniform-`L²` dominator —
the precise Lean obstruction (Codex, 2026-05-16) — is the content
promoted here. **Upstream historical vetting record** (the declaration now
has a proof body and is checked by the local compiled audit):
**Vetted Standard / Likely correct** (Gemini
`gemini-3-pro-preview`, 2026-05-17; deep-think unavailable, GR-tier
as for the prior two Gross-discharge axioms; recorded in
`AXIOM_AUDIT.md`): well-formed; normalization exact for variance-1
(`∇log ρ = −x`, generator `Δ − x·∇`, Mehler constants self-consistent,
no factor-2/variance rescale); matches BGL §2.7 `L²` strong
convergence on the core; non-vacuous (`f = Σ sin xᵢ`; the genuine OU
`Lp` semigroup satisfies `hP`, so the `P`-characterization is
consistent, not contradictory); hypotheses **sufficient** — value +
first + unmixed-second bounds give `f, Lf ∈ L²(μ)` (Gaussian
integrates all polynomials, `Lf` has ≤ linear growth) and the strong
`L²` limit follows from `Pₜf − f = ∫₀ᵗ Pₛ(Lf) ds` (no mixed partials,
third derivatives, or growth hypotheses required); right-limit
`𝓝[>] 0` form appropriate. No revision. -/
theorem gaussianFin_diffQuot_tendsto_Lp {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf_smooth : ContDiff ℝ ∞ f) (M : ℝ)
    (hf_bd : ∀ x : Fin n → ℝ,
      ‖f x‖ ≤ M ∧
      (∀ i : Fin n, ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ M) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
            (Pi.single i 1)‖ ≤ M))
    (hf_mem : MemLp f 2
      (MeasureTheory.Measure.pi
        (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
    (hLf_mem : MemLp
      (fun x : Fin n → ℝ =>
        (∑ i : Fin n,
            fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
              (Pi.single i 1))
          - ∑ i : Fin n, x i * fderiv ℝ f x (Pi.single i 1)) 2
      (MeasureTheory.Measure.pi
        (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
    (P : ℝ →
      (Lp ℝ 2
          (MeasureTheory.Measure.pi
            (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) →L[ℝ]
        Lp ℝ 2
          (MeasureTheory.Measure.pi
            (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))))
    (hP : ∀ t : ℝ, 0 ≤ t →
      ∀ φ : Lp ℝ 2
          (MeasureTheory.Measure.pi
            (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)),
        (P t φ : (Fin n → ℝ) → ℝ)
            =ᵐ[MeasureTheory.Measure.pi
                (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)]
        (fun x => ∫ y,
            (φ : (Fin n → ℝ) → ℝ)
                (fun i => Real.exp (-t) * x i
                  + Real.sqrt (1 - Real.exp (-2 * t)) * y i)
            ∂(MeasureTheory.Measure.pi
                (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (P t (hf_mem.toLp f) - hf_mem.toLp f))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (hLf_mem.toLp _)) := by
  let μ : MeasureTheory.Measure (Fin n → ℝ) :=
    MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
  let Lf : (Fin n → ℝ) → ℝ := fun x =>
    (∑ i : Fin n,
        fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
          (Pi.single i 1))
      - ∑ i : Fin n, x i * fderiv ℝ f x (Pi.single i 1)
  let hcore : IsCoreFin f := ⟨hf_smooth, M, hf_bd⟩
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) ((hf_bd (fun _ => 0)).1)
  let H : (Fin n → ℝ) → ℝ := fun x => (n : ℝ) * M + M * ∑ i : Fin n, |x i|
  have hcoord : ∀ i : Fin n, MemLp (fun x : Fin n → ℝ => |x i|) 2 μ := by
    intro i
    have heval : MeasurePreserving (Function.eval i) μ Gaussian1D.γ := by
      simpa [μ, γFin, Gaussian1D.γ] using
        (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => Gaussian1D.γ) i)
    have hid : MemLp (id : ℝ → ℝ) 2 Gaussian1D.γ := by
      have hid0 : MemLp (id : ℝ → ℝ) 2 (ProbabilityTheory.gaussianReal (0 : ℝ) 1) :=
        ProbabilityTheory.memLp_id_gaussianReal 2
      simpa [Gaussian1D.γ] using
        hid0
    have hcomp := hid.comp_measurePreserving heval
    simpa [Function.comp, Real.norm_eq_abs] using hcomp.norm
  have hsumabs_mem : MemLp (fun x : Fin n → ℝ => ∑ i : Fin n, |x i|) 2 μ := by
    convert
      (memLp_finsetSum' (s := Finset.univ)
        (f := fun i (x : Fin n → ℝ) => |x i|)
        (fun i _ => hcoord i)) using 1
    ext x
    simp
  have hH_mem : MemLp H 2 μ := by
    have hconst : MemLp (fun _ : Fin n → ℝ => (n : ℝ) * M) 2 μ := memLp_const ((n : ℝ) * M)
    have hsum : MemLp (fun x : Fin n → ℝ => M * ∑ i : Fin n, |x i|) 2 μ := hsumabs_mem.const_mul M
    simpa [H] using hconst.add hsum
  have h2H_mem : MemLp (fun x : Fin n → ℝ => 2 * H x) 2 μ := hH_mem.const_mul 2
  have hLf_bd : ∀ x : Fin n → ℝ, ‖Lf x‖ ≤ H x := by
    intro x
    convert (norm_ouGeneratorFin_le_of_coreBound (n := n) M hf_bd x) using 1
    rfl
  have hquot_bd : ∀ x : Fin n → ℝ, ∀ ⦃t : ℝ⦄, 0 < t →
      ‖t⁻¹ * (ouSemigroupFin t f x - f x)‖ ≤ H x := by
    intro x t ht
    simpa [H] using
      (norm_diffQuot_ouSemigroupFin_le_of_coreBound (n := n) hf_smooth M hf_bd x ht)
  let D : ℝ → (Fin n → ℝ) → ℝ := fun t x => t⁻¹ * (ouSemigroupFin t f x - f x) - Lf x
  have hD_mem : ∀ ⦃t : ℝ⦄, 0 < t → MemLp (D t) 2 μ := by
    intro t ht
    have hmeas : AEStronglyMeasurable (D t) μ := by
      have hou : StronglyMeasurable (ouSemigroupFin t f) :=
        stronglyMeasurable_ouSemigroupFin (n := n) t hf_smooth.continuous.measurable
      exact (((hou.aestronglyMeasurable.sub
        hf_smooth.continuous.stronglyMeasurable.aestronglyMeasurable).const_mul t⁻¹).sub
        hLf_mem.aestronglyMeasurable)
    refine h2H_mem.mono hmeas ?_
    exact Filter.Eventually.of_forall (fun x => by
      have hHx : (0 : ℝ) ≤ H x := by
        dsimp [H]
        positivity
      have h2Hx : (0 : ℝ) ≤ 2 * H x := by
        positivity
      calc
        ‖D t x‖ ≤ ‖t⁻¹ * (ouSemigroupFin t f x - f x)‖ + ‖Lf x‖ := norm_sub_le _ _
        _ ≤ H x + H x := add_le_add (hquot_bd x ht) (hLf_bd x)
        _ = 2 * H x := by ring
        _ = ‖2 * H x‖ := by rw [Real.norm_eq_abs, abs_of_nonneg h2Hx])
  have hIntLim :
      Tendsto (fun t : ℝ => ∫ x, (D t x) ^ 2 ∂μ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hbound_int : Integrable (fun x : Fin n → ℝ => (2 * H x) ^ 2) μ := by
      simpa [pow_two] using h2H_mem.integrable_sq
    have hlim :
        Tendsto (fun t : ℝ => ∫ x, (D t x) ^ 2 ∂μ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ x, (0 : ℝ) ∂μ)) := by
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun x : Fin n → ℝ => (2 * H x) ^ 2) ?_ ?_ hbound_int ?_
      · filter_upwards with t
        exact ((((stronglyMeasurable_ouSemigroupFin (n := n) t
          hf_smooth.continuous.measurable).aestronglyMeasurable.sub
          hf_smooth.continuous.stronglyMeasurable.aestronglyMeasurable).const_mul t⁻¹).sub
          hLf_mem.aestronglyMeasurable).pow 2
      · filter_upwards [self_mem_nhdsWithin] with t ht
        filter_upwards with x
        have hHx : (0 : ℝ) ≤ H x := by
          dsimp [H]
          positivity
        have h2Hx : (0 : ℝ) ≤ 2 * H x := by
          positivity
        have hdiff : ‖D t x‖ ≤ 2 * H x := by
          calc
            ‖D t x‖ ≤ ‖t⁻¹ * (ouSemigroupFin t f x - f x)‖ + ‖Lf x‖ := norm_sub_le _ _
            _ ≤ H x + H x := add_le_add (hquot_bd x ht) (hLf_bd x)
            _ = 2 * H x := by ring
        have habs : |D t x| ≤ 2 * H x := by
          simpa [D, Real.norm_eq_abs] using hdiff
        have hsq' : (D t x) ^ 2 ≤ (2 * H x) ^ 2 := by
          exact sq_le_sq.mpr <| by simpa [abs_of_nonneg h2Hx] using habs
        have hsq : |(D t x) ^ 2| ≤ (2 * H x) ^ 2 := by
          simpa using hsq'
        simpa [D, Real.norm_eq_abs] using hsq
      · filter_upwards with x
        have hq :
            Tendsto (fun t : ℝ => t⁻¹ * (ouSemigroupFin t f x - f x))
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Lf x)) := by
          convert (tendsto_diffQuot_ouSemigroupFin_zero (n := n) hcore x) using 1
          rfl
        have hconst : Tendsto (fun _ : ℝ => Lf x)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Lf x)) := tendsto_const_nhds
        have hsub :
            Tendsto (fun t : ℝ => D t x)
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
          simpa [D] using hq.sub hconst
        simpa using hsub.pow 2
    simpa using hlim
  have hPow :
      Tendsto (fun t : ℝ => (∫ x, (D t x) ^ 2 ∂μ) ^ (1 / (2 : ℝ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using
      (Real.continuous_rpow_const (by positivity : 0 ≤ (1 / (2 : ℝ)))).continuousAt.tendsto.comp
        hIntLim
  have hRhs :
      Tendsto
        (fun t : ℝ => ENNReal.ofReal ((∫ x, (D t x) ^ 2 ∂μ) ^ (1 / (2 : ℝ))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hPow
  have hConcrete :
      Tendsto
        (fun t : ℝ => eLpNorm
          (⇑(t⁻¹ • (P t (hf_mem.toLp f) - hf_mem.toLp f)) - Lf) 2 μ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    refine Tendsto.congr' ?_ hRhs
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hPt_f :
        ((((P t) (hf_mem.toLp f)) : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ) =ᵐ[μ]
          ouSemigroupFin t f := by
      have hPrep :
          ((((P t) (hf_mem.toLp f)) : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ) =ᵐ[μ]
            ouSemigroupFin t ((((hf_mem.toLp f) : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ)) := by
        refine (hP t ht.le (hf_mem.toLp f)).trans ?_
        filter_upwards with x
        change
          (∫ y,
              ((((hf_mem.toLp f) : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ)
                (fun i =>
                  Real.exp (-t) * x i + Real.sqrt (1 - Real.exp (-2 * t)) * y i)) ∂μ)
            = ouSemigroupFin t ((((hf_mem.toLp f) : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ)) x
        rw [ouSemigroupFin]
        simp only [μ, γFin, Gaussian1D.γ]
        refine integral_congr_ae ?_
        filter_upwards with y
        have harg :
            (fun i : Fin n =>
              Real.exp (-t) * x i + Real.sqrt (1 - Real.exp (-2 * t)) * y i) = ouShiftFin t x y := by
          ext i
          simp [ouShiftFin]
        exact congrArg ((((hf_mem.toLp f) : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ)) harg
      calc
        ((((P t) (hf_mem.toLp f)) : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ) =ᵐ[μ]
            ouSemigroupFin t ((((hf_mem.toLp f) : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ)) := hPrep
        _ =ᵐ[μ] ouSemigroupFin t f :=
          by simpa [μ, γFin, Gaussian1D.γ] using
            (ouSemigroupFin_ae_eq_of_aeEq_local (n := n) t ht.le hf_mem.coeFn_toLp)
    have hEq1 :
        eLpNorm (⇑(t⁻¹ • (P t (hf_mem.toLp f) - hf_mem.toLp f)) - Lf) 2 μ
          = eLpNorm (D t) 2 μ := by
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_smul t⁻¹ (P t (hf_mem.toLp f) - hf_mem.toLp f),
        Lp.coeFn_sub (P t (hf_mem.toLp f)) (hf_mem.toLp f), hPt_f, hf_mem.coeFn_toLp] with
        x hsmul hsub hPt hfx
      have hinner :
          ((((P t) (hf_mem.toLp f) - hf_mem.toLp f : Lp ℝ 2 μ) :
            (Fin n → ℝ) → ℝ) x) = ouSemigroupFin t f x - f x := by
        calc
          ((((P t) (hf_mem.toLp f) - hf_mem.toLp f : Lp ℝ 2 μ) :
              (Fin n → ℝ) → ℝ) x)
              = ((((P t) (hf_mem.toLp f) : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ) -
                  (((hf_mem.toLp f) : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ)) x := hsub
          _ = ouSemigroupFin t f x - f x := by
              simpa [Pi.sub_apply] using congrArg₂ (fun a b : ℝ => a - b) hPt hfx
      simp only [Pi.sub_apply]
      rw [hsmul]
      simp only [Pi.smul_apply]
      simpa [D] using congrArg (fun z : ℝ => t⁻¹ * z - Lf x) hinner
    have hEq2 :
        eLpNorm (D t) 2 μ
          = ENNReal.ofReal ((∫ x, (D t x) ^ 2 ∂μ) ^ (1 / (2 : ℝ))) := by
      simpa [D, Real.norm_eq_abs] using
        ((hD_mem ht).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top)
    calc
      ENNReal.ofReal ((∫ x, (D t x) ^ 2 ∂μ) ^ (1 / (2 : ℝ))) = eLpNorm (D t) 2 μ := hEq2.symm
      _ = eLpNorm (⇑(t⁻¹ • (P t (hf_mem.toLp f) - hf_mem.toLp f)) - Lf) 2 μ := hEq1.symm
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun t : ℝ => t⁻¹ • (P t (hf_mem.toLp f) - hf_mem.toLp f)) Lf hLf_mem).mpr hConcrete

/-- **G2 (a) — strong-`L²` difference-quotient limit.** For core `f`,
`t⁻¹ • (P_t [f] − [f]) → [ouGeneratorFin f]` in `Lp ℝ 2 (γFin n)` as
`t → 0⁺` (right limit, matching `GeneratorCompat`'s `𝓝[>] 0`).

Discharged from the proved general, Mathlib-native theorem
`gaussianFin_diffQuot_tendsto_Lp` by instantiating the operator
parameter with `ouSemigroupFinLp` and its generic Mehler a.e.
characterization `ouSemigroupFinLp_coeFn_ae`, then unfolding the thin
project definitions. The upstream comment previously called this theorem
an axiom; that historical claim is superseded by its proof body and the
local all-declaration axiom audit. -/
theorem ouSemigroupFinLp_diffQuot_tendsto {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) :
    Tendsto
      (fun t : ℝ => t⁻¹ •
        (ouSemigroupFinLp (n := n) t ((isCoreFin_memLp f hf).toLp f)
          - (isCoreFin_memLp f hf).toLp f))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ouGeneratorFinLp hf)) := by
  obtain ⟨hsm, M, hM⟩ := hf
  have hfc : IsCoreFin f := ⟨hsm, M, hM⟩
  convert gaussianFin_diffQuot_tendsto_Lp (n := n) f hsm M hM
      (isCoreFin_memLp f hfc) (memLp_ouGeneratorFin hfc)
      (ouSemigroupFinLp (n := n))
      (fun t ht φ => by
        refine (ouSemigroupFinLp_coeFn_ae (n := n) t ht φ).trans ?_
        simp only [γFin, Gaussian1D.γ]
        exact Filter.EventuallyEq.rfl) using 1 <;> rfl

end GaussianFin

end
