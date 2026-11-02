/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port attribution: this upstream file had no per-file header. Its repository
license and authorship are retained explicitly here; see UPSTREAM.md.
-/

import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanGeneratorLimit

open MeasureTheory Filter Set
open scoped BigOperators InnerProductSpace

noncomputable section

namespace GaussianFin

variable {n : ℕ}

/-- The OU semigroup respects a.e. equality of inputs (its Mehler kernel pushforward
is absolutely continuous w.r.t. `γFin n`). Needed by the `CoreSemigroupInvariant`
discharge in `EuclideanHypercontractive`. -/
theorem ouSemigroupFin_ae_eq_of_aeEq (t : ℝ) (ht : 0 ≤ t)
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

private theorem core_toLp_eq_semigroupLp (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ouSemigroupFinLp (n := n) t ((isCoreFin_memLp (n := n) f hf).toLp f) =
      ((isCoreFin_memLp (n := n) (ouSemigroupFin t f)
        (ouSemigroupFin_preserves_IsCore (n := n) t ht hf)).toLp (ouSemigroupFin t f)) := by
  rw [Lp.ext_iff]
  calc
    (((ouSemigroupFinLp (n := n) t ((isCoreFin_memLp (n := n) f hf).toLp f)) :
        Lp ℝ 2 (γFin n)) : (Fin n → ℝ) → ℝ) =ᵐ[γFin n]
        ouSemigroupFin t (((isCoreFin_memLp (n := n) f hf).toLp f : Lp ℝ 2 (γFin n)) : (Fin n → ℝ) → ℝ) :=
      ouSemigroupFinLp_coeFn_ae (n := n) t ht _
    _ =ᵐ[γFin n] ouSemigroupFin t f :=
      ouSemigroupFin_ae_eq_of_aeEq (n := n) t ht (isCoreFin_memLp (n := n) f hf).coeFn_toLp
    _ =ᵐ[γFin n]
        (((isCoreFin_memLp (n := n) (ouSemigroupFin t f)
            (ouSemigroupFin_preserves_IsCore (n := n) t ht hf)).toLp (ouSemigroupFin t f)) :
          (Fin n → ℝ) → ℝ) :=
      (isCoreFin_memLp (n := n) (ouSemigroupFin t f)
        (ouSemigroupFin_preserves_IsCore (n := n) t ht hf)).coeFn_toLp.symm

private theorem pairing_eq_integral_mul {f g : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    ⟪(isCoreFin_memLp (n := n) f hf).toLp f, (isCoreFin_memLp (n := n) g hg).toLp g⟫_ℝ =
      ∫ x, f x * g x ∂γFin n := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(isCoreFin_memLp (n := n) f hf).coeFn_toLp,
    (isCoreFin_memLp (n := n) g hg).coeFn_toLp] with x hfx hgx
  simp only [hfx, hgx]
  change RCLike.re (g x * star (f x)) = f x * g x
  simp [mul_comm]

private theorem tendsto_sub_right_at (t : ℝ) :
    Tendsto (fun s : ℝ => s - t) (nhdsWithin t (Ioi t)) (nhdsWithin 0 (Ioi 0)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have : Tendsto (fun s : ℝ => s - t) (nhds t) (nhds 0) := by
      have h := Filter.Tendsto.sub_const (Filter.tendsto_id (α := ℝ).mono_left (le_refl (nhds t))) t
      simpa using h
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs ⊢
    linarith

private theorem tendsto_sub_left_at (t : ℝ) :
    Tendsto (fun s : ℝ => t - s) (nhdsWithin t (Iio t)) (nhdsWithin 0 (Ioi 0)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have : Tendsto (fun s : ℝ => t - s) (nhds t) (nhds 0) := by
      have h := Filter.Tendsto.const_sub t (Filter.tendsto_id (α := ℝ).mono_left (le_refl (nhds t)))
      simpa using h
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Iio] at hs ⊢
    exact sub_pos.mpr hs

private theorem tendsto_ouSemigroupFinLp_right (t : ℝ) (ht : 0 ≤ t)
    (v : Lp ℝ 2 (γFin n)) :
    Tendsto (fun s : ℝ => ouSemigroupFinLp (n := n) (t + s) v)
      (nhdsWithin 0 (Ici 0)) (nhds (ouSemigroupFinLp (n := n) t v)) := by
  have hcont0 := ouSemigroupFinLp_strong_cont (n := n) v
  rw [Metric.tendsto_nhdsWithin_nhds] at hcont0 ⊢
  intro ε hε
  rcases hcont0 ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro s hs0 hsδ
  have hsem :
      ouSemigroupFinLp (n := n) (t + s) v =
        ouSemigroupFinLp (n := n) t (ouSemigroupFinLp (n := n) s v) := by
    simpa using congrArg (fun P => P v) (ouSemigroupFinLp_semigroup (n := n) t s ht hs0)
  rw [hsem]
  calc
    dist (ouSemigroupFinLp (n := n) t (ouSemigroupFinLp (n := n) s v))
        (ouSemigroupFinLp (n := n) t v)
      ≤ ‖ouSemigroupFinLp (n := n) t‖ * dist (ouSemigroupFinLp (n := n) s v) v := by
          simpa [dist_eq_norm, norm_sub_rev] using
            (ouSemigroupFinLp (n := n) t).lipschitzWith.norm_sub_le
              (ouSemigroupFinLp (n := n) s v) v
    _ ≤ dist (ouSemigroupFinLp (n := n) s v) v := by
          exact mul_le_of_le_one_left (dist_nonneg)
            (ouSemigroupFinLp_contraction (n := n) t ht)
    _ < ε := hδ hs0 hsδ

private theorem tendsto_ouSemigroupFinLp_left {t : ℝ} (ht : 0 < t)
    (v : Lp ℝ 2 (γFin n)) :
    Tendsto (fun s : ℝ => ouSemigroupFinLp (n := n) s v)
      (nhdsWithin t (Iio t)) (nhds (ouSemigroupFinLp (n := n) t v)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hcont0 := ouSemigroupFinLp_strong_cont (n := n) v
  rw [Metric.tendsto_nhdsWithin_nhds] at hcont0
  rcases hcont0 ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨min δ t, by positivity, ?_⟩
  intro s hst hsδ
  have hts : 0 < t - s := sub_pos.mpr hst
  have hs_pos : 0 < s := by
    have hdist : |t - s| < t := lt_of_lt_of_le (by simpa [Real.dist_eq, abs_sub_comm] using hsδ)
      (min_le_right _ _)
    have habs : |t - s| = t - s := abs_of_pos hts
    linarith
  have hts_le : t - s < δ := by
    have h1 : t - s < min δ t := by
      simpa [Real.dist_eq, abs_sub_comm, abs_of_pos hts] using hsδ
    exact lt_of_lt_of_le h1 (min_le_left _ _)
  have hsem :
      ouSemigroupFinLp (n := n) t v =
        ouSemigroupFinLp (n := n) s (ouSemigroupFinLp (n := n) (t - s) v) := by
    simpa [show s + (t - s) = t by ring] using
      congrArg (fun P => P v) (ouSemigroupFinLp_semigroup (n := n) s (t - s) hs_pos.le hts.le)
  rw [hsem]
  calc
    dist (ouSemigroupFinLp (n := n) s v)
        (ouSemigroupFinLp (n := n) s (ouSemigroupFinLp (n := n) (t - s) v))
      ≤ ‖ouSemigroupFinLp (n := n) s‖ * dist v (ouSemigroupFinLp (n := n) (t - s) v) := by
          simpa [dist_eq_norm] using
            (ouSemigroupFinLp (n := n) s).lipschitzWith.norm_sub_le v
              (ouSemigroupFinLp (n := n) (t - s) v)
    _ ≤ dist v (ouSemigroupFinLp (n := n) (t - s) v) := by
          exact mul_le_of_le_one_left (dist_nonneg)
            (ouSemigroupFinLp_contraction (n := n) s hs_pos.le)
    _ = dist (ouSemigroupFinLp (n := n) (t - s) v) v := by rw [dist_comm]
    _ < ε := by
          have hdist : dist (t - s) 0 < δ := by
            simpa [Real.dist_eq, abs_of_pos hts] using hts_le
          exact hδ hts.le hdist

private theorem ouGeneratorFinLp_commutes (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ouSemigroupFinLp (n := n) t (ouGeneratorFinLp (n := n) hf) =
      ouGeneratorFinLp (n := n)
        (ouSemigroupFin_preserves_IsCore (n := n) t ht hf) := by
  let fLp : Lp ℝ 2 (γFin n) := (isCoreFin_memLp (n := n) f hf).toLp f
  let hf' : IsCoreFin (ouSemigroupFin t f) := ouSemigroupFin_preserves_IsCore (n := n) t ht hf
  let hLp : Lp ℝ 2 (γFin n) := (isCoreFin_memLp (n := n) (ouSemigroupFin t f) hf').toLp (ouSemigroupFin t f)
  have hhEq : ouSemigroupFinLp (n := n) t fLp = hLp :=
    core_toLp_eq_semigroupLp (n := n) t ht hf
  have hA := ouSemigroupFinLp_diffQuot_tendsto (n := n) hf
  have hA' := ouSemigroupFinLp_diffQuot_tendsto (n := n) hf'
  have hmap :
      Tendsto
        (fun s : ℝ =>
          s⁻¹ • (ouSemigroupFinLp (n := n) s hLp - hLp))
        (nhdsWithin 0 (Ioi 0))
        (nhds (ouSemigroupFinLp (n := n) t (ouGeneratorFinLp (n := n) hf))) := by
    have hbase :
        Tendsto
          (fun s : ℝ =>
            ouSemigroupFinLp (n := n) t
              (s⁻¹ • (ouSemigroupFinLp (n := n) s fLp - fLp)))
          (nhdsWithin 0 (Ioi 0))
          (nhds (ouSemigroupFinLp (n := n) t (ouGeneratorFinLp (n := n) hf))) :=
      (ouSemigroupFinLp (n := n) t).continuous.tendsto _
        |>.comp hA
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : 0 ≤ s := hs.le
    have hst :
        ouSemigroupFinLp (n := n) (s + t) fLp =
          ouSemigroupFinLp (n := n) s (ouSemigroupFinLp (n := n) t fLp) := by
      simpa using congrArg (fun P => P fLp) (ouSemigroupFinLp_semigroup (n := n) s t hs0 ht)
    have hts :
        ouSemigroupFinLp (n := n) (t + s) fLp =
          ouSemigroupFinLp (n := n) t (ouSemigroupFinLp (n := n) s fLp) := by
      simpa using congrArg (fun P => P fLp) (ouSemigroupFinLp_semigroup (n := n) t s ht hs0)
    have hswap :
        ouSemigroupFinLp (n := n) t (ouSemigroupFinLp (n := n) s fLp) =
          ouSemigroupFinLp (n := n) s (ouSemigroupFinLp (n := n) t fLp) := by
      rw [← hts, show t + s = s + t by ring, hst]
    calc
      ouSemigroupFinLp (n := n) t
          (s⁻¹ • (ouSemigroupFinLp (n := n) s fLp - fLp))
          = s⁻¹ • (ouSemigroupFinLp (n := n) t (ouSemigroupFinLp (n := n) s fLp) -
              ouSemigroupFinLp (n := n) t fLp) := by
              simp [ContinuousLinearMap.map_sub]
      _ = s⁻¹ • (ouSemigroupFinLp (n := n) s (ouSemigroupFinLp (n := n) t fLp) -
              ouSemigroupFinLp (n := n) t fLp) := by rw [hswap]
      _ = s⁻¹ • (ouSemigroupFinLp (n := n) s hLp - hLp) := by rw [hhEq]
  exact tendsto_nhds_unique hmap hA'

private theorem pairing_time_deriv_zero {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    HasDerivWithinAt
      (fun s : ℝ =>
        ⟪(isCoreFin_memLp (n := n) f hf).toLp f,
          ouSemigroupFinLp (n := n) s ((isCoreFin_memLp (n := n) f hf).toLp f)⟫_ℝ)
      (⟪(isCoreFin_memLp (n := n) f hf).toLp f, ouGeneratorFinLp (n := n) hf⟫_ℝ)
      (Ici 0) 0 := by
  let fLp : Lp ℝ 2 (γFin n) := (isCoreFin_memLp (n := n) f hf).toLp f
  let Af : Lp ℝ 2 (γFin n) := ouGeneratorFinLp (n := n) hf
  have hq :
      Tendsto
        (fun s : ℝ =>
          ⟪fLp, s⁻¹ • (ouSemigroupFinLp (n := n) s fLp - fLp)⟫_ℝ)
        (nhdsWithin 0 (Ioi 0)) (nhds ⟪fLp, Af⟫_ℝ) :=
    ((Continuous.inner continuous_const continuous_id).continuousAt.tendsto).comp
      (ouSemigroupFinLp_diffQuot_tendsto (n := n) hf)
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope']
  · refine hq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    rw [slope_def_field, sub_zero, ouSemigroupFinLp_zero]
    simp only [div_eq_mul_inv, inner_smul_right, inner_sub_right, ContinuousLinearMap.id_apply]
    ring
  · simp

private theorem pairing_slope_right_eq
    (fLp : Lp ℝ 2 (γFin n)) (t s : ℝ) (ht : 0 ≤ t) (hst : t < s) :
    slope (fun u : ℝ => ⟪fLp, ouSemigroupFinLp (n := n) u fLp⟫_ℝ) t s =
      ⟪ouSemigroupFinLp (n := n) t fLp,
        (s - t)⁻¹ • (ouSemigroupFinLp (n := n) (s - t) fLp - fLp)⟫_ℝ := by
  have hst0 : s - t ≠ 0 := sub_ne_zero.mpr hst.ne'
  have hsem : ouSemigroupFinLp (n := n) s fLp =
      ouSemigroupFinLp (n := n) t (ouSemigroupFinLp (n := n) (s - t) fLp) := by
    simpa [show t + (s - t) = s by ring] using
      congrArg (fun P => P fLp) (ouSemigroupFinLp_semigroup (n := n) t (s - t) ht (sub_nonneg.mpr hst.le))
  have hsym :
      ⟪fLp, ouSemigroupFinLp (n := n) t (ouSemigroupFinLp (n := n) (s - t) fLp)⟫_ℝ =
        ⟪ouSemigroupFinLp (n := n) t fLp, ouSemigroupFinLp (n := n) (s - t) fLp⟫_ℝ := by
    simpa [real_inner_comm] using
      (ouSemigroupFinLp_symmetric (n := n) t ht fLp
        (ouSemigroupFinLp (n := n) (s - t) fLp))
  have hsym0 :
      ⟪fLp, ouSemigroupFinLp (n := n) t fLp⟫_ℝ =
        ⟪ouSemigroupFinLp (n := n) t fLp, fLp⟫_ℝ := by
    simp [real_inner_comm]
  rw [slope_def_field, hsem, hsym, hsym0]
  simp [div_eq_mul_inv, inner_sub_right, inner_smul_right, mul_comm]

private theorem pairing_slope_left_eq
    (fLp : Lp ℝ 2 (γFin n)) (t s : ℝ) (hs : 0 < s) (hst : s < t) :
    slope (fun u : ℝ => ⟪fLp, ouSemigroupFinLp (n := n) u fLp⟫_ℝ) t s =
      ⟪ouSemigroupFinLp (n := n) s fLp,
        (t - s)⁻¹ • (ouSemigroupFinLp (n := n) (t - s) fLp - fLp)⟫_ℝ := by
  have hts : 0 ≤ t - s := (sub_pos.mpr hst).le
  have hst0 : s - t ≠ 0 := sub_ne_zero.mpr hst.ne
  have hts0 : t - s ≠ 0 := sub_ne_zero.mpr hst.ne.symm
  have hsem : ouSemigroupFinLp (n := n) t fLp =
      ouSemigroupFinLp (n := n) s (ouSemigroupFinLp (n := n) (t - s) fLp) := by
    simpa [show s + (t - s) = t by ring] using
      congrArg (fun P => P fLp) (ouSemigroupFinLp_semigroup (n := n) s (t - s) hs.le hts)
  have hsym :
      ⟪fLp, ouSemigroupFinLp (n := n) s (ouSemigroupFinLp (n := n) (t - s) fLp)⟫_ℝ =
        ⟪ouSemigroupFinLp (n := n) s fLp, ouSemigroupFinLp (n := n) (t - s) fLp⟫_ℝ := by
    simpa [real_inner_comm] using
      (ouSemigroupFinLp_symmetric (n := n) s hs.le fLp
        (ouSemigroupFinLp (n := n) (t - s) fLp))
  have hsym0 :
      ⟪fLp, ouSemigroupFinLp (n := n) s fLp⟫_ℝ =
        ⟪ouSemigroupFinLp (n := n) s fLp, fLp⟫_ℝ := by
    simp [real_inner_comm]
  rw [slope_def_field, hsem, hsym, hsym0]
  have hsubl :
      (⟪ouSemigroupFinLp (n := n) s fLp, fLp⟫_ℝ -
          ⟪ouSemigroupFinLp (n := n) s fLp, ouSemigroupFinLp (n := n) (t - s) fLp⟫_ℝ) *
        (s - t)⁻¹ =
      (t - s)⁻¹ *
        (⟪ouSemigroupFinLp (n := n) s fLp, ouSemigroupFinLp (n := n) (t - s) fLp⟫_ℝ -
          ⟪ouSemigroupFinLp (n := n) s fLp, fLp⟫_ℝ) := by
    field_simp [hst0, hts0]
    ring
  rw [div_eq_mul_inv, hsubl]
  simp [inner_sub_right, inner_smul_right]

set_option maxHeartbeats 800000 in
private theorem pairing_time_deriv_pos {f : (Fin n → ℝ) → ℝ}
    (t : ℝ) (ht : 0 < t) (hf : IsCoreFin f) :
    HasDerivAt
      (fun s : ℝ =>
        ⟪(isCoreFin_memLp (n := n) f hf).toLp f,
          ouSemigroupFinLp (n := n) s ((isCoreFin_memLp (n := n) f hf).toLp f)⟫_ℝ)
      (⟪ouSemigroupFinLp (n := n) t ((isCoreFin_memLp (n := n) f hf).toLp f),
        ouGeneratorFinLp (n := n) hf⟫_ℝ)
      t := by
  let fLp : Lp ℝ 2 (γFin n) := (isCoreFin_memLp (n := n) f hf).toLp f
  let Af : Lp ℝ 2 (γFin n) := ouGeneratorFinLp (n := n) hf
  let ψ : ℝ → ℝ := fun s => ⟪fLp, ouSemigroupFinLp (n := n) s fLp⟫_ℝ
  have hright :
      HasDerivWithinAt ψ ⟪ouSemigroupFinLp (n := n) t fLp, Af⟫_ℝ (Ioi t) t := by
    rw [hasDerivWithinAt_iff_tendsto_slope']
    · have hq :
          Tendsto
            (fun s : ℝ =>
              (s - t)⁻¹ • (ouSemigroupFinLp (n := n) (s - t) fLp - fLp))
            (nhdsWithin t (Ioi t)) (nhds Af) :=
        (ouSemigroupFinLp_diffQuot_tendsto (n := n) hf).comp (tendsto_sub_right_at t)
      have hpair :
          Tendsto
            (fun s : ℝ => ⟪ouSemigroupFinLp (n := n) t fLp,
              (s - t)⁻¹ • (ouSemigroupFinLp (n := n) (s - t) fLp - fLp)⟫_ℝ)
            (nhdsWithin t (Ioi t)) (nhds ⟪ouSemigroupFinLp (n := n) t fLp, Af⟫_ℝ) :=
        Filter.Tendsto.inner tendsto_const_nhds hq
      refine hpair.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      simpa [ψ] using (pairing_slope_right_eq (n := n) fLp t s ht.le hs).symm
    · simp
  have hleft :
      HasDerivWithinAt ψ ⟪ouSemigroupFinLp (n := n) t fLp, Af⟫_ℝ (Iio t) t := by
    rw [hasDerivWithinAt_iff_tendsto_slope']
    · have hcont :
          Tendsto (fun s : ℝ => ouSemigroupFinLp (n := n) s fLp)
            (nhdsWithin t (Iio t)) (nhds (ouSemigroupFinLp (n := n) t fLp)) :=
        tendsto_ouSemigroupFinLp_left (n := n) ht fLp
      have hq :
          Tendsto
            (fun s : ℝ =>
              (t - s)⁻¹ • (ouSemigroupFinLp (n := n) (t - s) fLp - fLp))
            (nhdsWithin t (Iio t)) (nhds Af) :=
        (ouSemigroupFinLp_diffQuot_tendsto (n := n) hf).comp (tendsto_sub_left_at t)
      have hpair :
          Tendsto
            (fun s : ℝ =>
              ⟪ouSemigroupFinLp (n := n) s fLp,
                (t - s)⁻¹ • (ouSemigroupFinLp (n := n) (t - s) fLp - fLp)⟫_ℝ)
            (nhdsWithin t (Iio t)) (nhds ⟪ouSemigroupFinLp (n := n) t fLp, Af⟫_ℝ) := by
        exact Filter.Tendsto.inner hcont hq
      have hpos : ∀ᶠ s : ℝ in nhdsWithin t (Iio t), s ∈ Ioi 0 :=
        eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds ht)
      refine hpair.congr' ?_
      filter_upwards [self_mem_nhdsWithin, hpos] with s hs hspos
      have hs0 : 0 < s := hspos
      simpa [ψ] using (pairing_slope_left_eq (n := n) fLp t s hs0 hs).symm
    · simp
  have hpunct : HasDerivWithinAt ψ ⟪ouSemigroupFinLp (n := n) t fLp, Af⟫_ℝ (Iic t ∪ Ioi t) t :=
    hleft.Iic_of_Iio.union hright
  have huniv : HasDerivWithinAt ψ ⟪ouSemigroupFinLp (n := n) t fLp, Af⟫_ℝ (univ : Set ℝ) t := by
    simpa [Set.Iic_union_Ioi] using hpunct
  exact (hasDerivWithinAt_univ.mp huniv)

private theorem pairing_time_deriv_eq_energy (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ⟪ouSemigroupFinLp (n := n) (2 * t) ((isCoreFin_memLp (n := n) f hf).toLp f),
      ouGeneratorFinLp (n := n) hf⟫_ℝ =
      - ouEnergyFin (ouSemigroupFin t f) (ouSemigroupFin t f) := by
  let hh : IsCoreFin (ouSemigroupFin t f) := ouSemigroupFin_preserves_IsCore (n := n) t ht hf
  have hcore : ouSemigroupFinLp (n := n) t ((isCoreFin_memLp (n := n) f hf).toLp f) =
      (isCoreFin_memLp (n := n) (ouSemigroupFin t f) hh).toLp (ouSemigroupFin t f) :=
    core_toLp_eq_semigroupLp (n := n) t ht hf
  have hcomm := ouGeneratorFinLp_commutes (n := n) t ht hf
  calc
    ⟪ouSemigroupFinLp (n := n) (2 * t) ((isCoreFin_memLp (n := n) f hf).toLp f),
      ouGeneratorFinLp (n := n) hf⟫_ℝ
      = ⟪ouSemigroupFinLp (n := n) t
            (ouSemigroupFinLp (n := n) t ((isCoreFin_memLp (n := n) f hf).toLp f)),
          ouGeneratorFinLp (n := n) hf⟫_ℝ := by
            have hsem := congrArg (fun P => P ((isCoreFin_memLp (n := n) f hf).toLp f))
              (ouSemigroupFinLp_semigroup (n := n) t t ht ht)
            simpa [two_mul] using congrArg (fun u => ⟪u, ouGeneratorFinLp (n := n) hf⟫_ℝ) hsem
    _ = ⟪ouSemigroupFinLp (n := n) t ((isCoreFin_memLp (n := n) f hf).toLp f),
          ouSemigroupFinLp (n := n) t (ouGeneratorFinLp (n := n) hf)⟫_ℝ := by
            simpa using (ouSemigroupFinLp_symmetric (n := n) t ht
              (ouSemigroupFinLp (n := n) t ((isCoreFin_memLp (n := n) f hf).toLp f))
              (ouGeneratorFinLp (n := n) hf)).symm
    _ = ⟪(isCoreFin_memLp (n := n) (ouSemigroupFin t f) hh).toLp (ouSemigroupFin t f),
          ouGeneratorFinLp (n := n) hh⟫_ℝ := by rw [hcore, hcomm]
    _ = - ouEnergyFin (ouSemigroupFin t f) (ouSemigroupFin t f) :=
      ouGeneratorFin_ibp (n := n) hh hh

private theorem pairing_hasDerivWithinAt {f : (Fin n → ℝ) → ℝ}
    (t : ℝ) (ht : 0 ≤ t) (hf : IsCoreFin f) :
    HasDerivWithinAt
      (fun s : ℝ =>
        ⟪(isCoreFin_memLp (n := n) f hf).toLp f,
          ouSemigroupFinLp (n := n) s ((isCoreFin_memLp (n := n) f hf).toLp f)⟫_ℝ)
      (- ouEnergyFin (ouSemigroupFin (t / 2) f) (ouSemigroupFin (t / 2) f))
      (Ici 0) t := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  ·
    simpa [ouSemigroupFin_zero, (ouGeneratorFin_ibp (n := n) hf hf).symm] using
      pairing_time_deriv_zero (n := n) hf
  · have hpos := pairing_time_deriv_pos (n := n) t ht_pos hf
    have henergy : ⟪ouSemigroupFinLp (n := n) t ((isCoreFin_memLp (n := n) f hf).toLp f),
        ouGeneratorFinLp (n := n) hf⟫_ℝ =
        - ouEnergyFin (ouSemigroupFin (t / 2) f) (ouSemigroupFin (t / 2) f) := by
      have ht2 : 0 ≤ t / 2 := by positivity
      simpa [show 2 * (t / 2) = t by ring] using
        pairing_time_deriv_eq_energy (n := n) (t := t / 2) ht2 hf
    rw [henergy] at hpos
    exact hpos.hasDerivWithinAt

private theorem l2_sq_eq_pairing {f : (Fin n → ℝ) → ℝ}
    (s : ℝ) (hs : 0 ≤ s) (hf : IsCoreFin f) :
    ∫ x, (ouSemigroupFin s f x) ^ 2 ∂γFin n =
      ⟪(isCoreFin_memLp (n := n) f hf).toLp f,
        ouSemigroupFinLp (n := n) (2 * s) ((isCoreFin_memLp (n := n) f hf).toLp f)⟫_ℝ := by
  let hs_core : IsCoreFin (ouSemigroupFin s f) := ouSemigroupFin_preserves_IsCore (n := n) s hs hf
  have hLp :
      ouSemigroupFinLp (n := n) s ((isCoreFin_memLp (n := n) f hf).toLp f) =
        (isCoreFin_memLp (n := n) (ouSemigroupFin s f) hs_core).toLp (ouSemigroupFin s f) :=
    core_toLp_eq_semigroupLp (n := n) s hs hf
  calc
    ∫ x, (ouSemigroupFin s f x) ^ 2 ∂γFin n
      = ⟪(isCoreFin_memLp (n := n) (ouSemigroupFin s f) hs_core).toLp (ouSemigroupFin s f),
          (isCoreFin_memLp (n := n) (ouSemigroupFin s f) hs_core).toLp (ouSemigroupFin s f)⟫_ℝ := by
            symm
            simpa [pow_two] using pairing_eq_integral_mul (n := n) hs_core hs_core
    _ = ⟪ouSemigroupFinLp (n := n) s ((isCoreFin_memLp (n := n) f hf).toLp f),
          ouSemigroupFinLp (n := n) s ((isCoreFin_memLp (n := n) f hf).toLp f)⟫_ℝ := by
            rw [hLp]
    _ = ⟪(isCoreFin_memLp (n := n) f hf).toLp f,
          ouSemigroupFinLp (n := n) (2 * s) ((isCoreFin_memLp (n := n) f hf).toLp f)⟫_ℝ := by
            rw [show 2 * s = s + s by ring, ouSemigroupFinLp_semigroup (n := n) s s hs hs]
            simpa using (ouSemigroupFinLp_symmetric (n := n) s hs
              ((isCoreFin_memLp (n := n) f hf).toLp f)
              (ouSemigroupFinLp (n := n) s ((isCoreFin_memLp (n := n) f hf).toLp f))).symm

/-- **Multivariate de Bruijn-style L²-derivative identity (BGL Prop 4.7.1, n-dim Gaussian case).**

Discharged through the existing strong-`L²` generator-limit route:
`ouSemigroupFinLp_diffQuot_tendsto` plus the multivariate Gaussian
integration-by-parts theorem `ouGeneratorFin_ibp`. -/
theorem ouSemigroupFin_l2_sq_hasDerivWithinAt {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : IsCoreFin f) :
    HasDerivWithinAt
      (fun s => ∫ x, (ouSemigroupFin s f x) ^ 2 ∂γFin n)
      (-2 * ∫ x, ouGammaFin (ouSemigroupFin t f) (ouSemigroupFin t f) x ∂γFin n)
      (Set.Ici 0) t := by
  let ψ : ℝ → ℝ := fun s =>
    ⟪(isCoreFin_memLp (n := n) f hf).toLp f,
      ouSemigroupFinLp (n := n) s ((isCoreFin_memLp (n := n) f hf).toLp f)⟫_ℝ
  have hpair : HasDerivWithinAt ψ
      (- ouEnergyFin (ouSemigroupFin t f) (ouSemigroupFin t f)) (Ici 0) (2 * t) := by
    simpa [show (2 * t) / 2 = t by ring] using
      pairing_hasDerivWithinAt (n := n) (t := 2 * t) (by positivity) hf
  have hlin : HasDerivWithinAt (fun s : ℝ => 2 * s) 2 (Ici 0) t := by
    simpa [two_mul] using ((hasDerivAt_id t).const_mul (2 : ℝ)).hasDerivWithinAt
  have hcomp : HasDerivWithinAt (fun s : ℝ => ψ (2 * s))
      ((- ouEnergyFin (ouSemigroupFin t f) (ouSemigroupFin t f)) * 2) (Ici 0) t := by
    exact hpair.comp t hlin (fun s hs => show 0 ≤ 2 * s by exact mul_nonneg zero_le_two hs)
  have hmain :
      HasDerivWithinAt
        (fun s => ∫ x, (ouSemigroupFin s f x) ^ 2 ∂γFin n)
        ((- ouEnergyFin (ouSemigroupFin t f) (ouSemigroupFin t f)) * 2)
        (Ici 0) t := by
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · have hmem : ∀ᶠ s : ℝ in nhdsWithin t (Ici 0), s ∈ Ici 0 :=
        eventually_mem_of_tendsto_nhdsWithin tendsto_id
      filter_upwards [hmem] with s hs
      simp [ψ, l2_sq_eq_pairing (n := n) s hs hf]
    · simp [ψ, l2_sq_eq_pairing (n := n) t ht hf]
  convert hmain using 1
  simp [ouEnergyFin, mul_comm]

/-- **Integrated multivariate L² decay (BGL Prop. 4.7.1, n-dim Gaussian case).** -/
theorem ouSemigroupFin_l2_decay_bound {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : IsCoreFin f) :
    ∫ x, (f x) ^ 2 ∂γFin n - ∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n ≤
      (1 - Real.exp (-2 * t)) * ouEnergyFin f f := by
  set Ef : ℝ := ouEnergyFin f f with hEf_def
  set g : ℝ → ℝ := fun s => ∫ x, (ouSemigroupFin s f x) ^ 2 ∂γFin n with hg_def
  set φ : ℝ → ℝ := fun s => -2 * Real.exp (-2 * s) * Ef with hφ_def
  have hderiv : ∀ s, 0 ≤ s →
      HasDerivWithinAt g
        (-2 * ∫ x, ouGammaFin (ouSemigroupFin s f) (ouSemigroupFin s f) x ∂γFin n) (Ici 0) s := by
    intro s hs
    exact ouSemigroupFin_l2_sq_hasDerivWithinAt (n := n) f s hs hf
  have hg_cont : ContinuousOn g (Set.Icc 0 t) := by
    intro s hs
    have h := (hderiv s hs.1).continuousWithinAt
    exact h.mono (fun x hx => hx.1)
  have hderiv_open : ∀ s ∈ Set.Ioo 0 t,
      HasDerivWithinAt g
        (-2 * ∫ x, ouGammaFin (ouSemigroupFin s f) (ouSemigroupFin s f) x ∂γFin n) (Ioi s) s := by
    intro s hs
    exact (hderiv s hs.1.le).mono (fun x hx => hs.1.le.trans hx.le)
  have hφg' : ∀ s ∈ Set.Ioo 0 t,
      φ s ≤ -2 * ∫ x, ouGammaFin (ouSemigroupFin s f) (ouSemigroupFin s f) x ∂γFin n := by
    intro s hs
    have hgrad := ouSemigroupFin_gradient_decay f s hs.1.le hf
    have hgrad' : ∫ x, ouGammaFin (ouSemigroupFin s f) (ouSemigroupFin s f) x ∂γFin n ≤
        Real.exp (-2 * s) * Ef := by
      rw [hEf_def]
      exact hgrad
    have h := mul_le_mul_of_nonneg_left hgrad' (by norm_num : (0 : ℝ) ≤ 2)
    show -2 * Real.exp (-2 * s) * Ef ≤ -2 * _
    linarith
  have hφ_cont : Continuous φ := by
    show Continuous (fun s => -2 * Real.exp (-2 * s) * Ef)
    fun_prop
  have hφ_int : MeasureTheory.IntegrableOn φ (Set.Icc 0 t) :=
    hφ_cont.continuousOn.integrableOn_Icc
  have hFTC : ∫ s in (0)..t, φ s ≤ g t - g 0 :=
    intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le ht hg_cont
      hderiv_open hφ_int hφg'
  have hderiv_exp : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => Real.exp (-2 * u)) (-2 * Real.exp (-2 * s)) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => -2 * u) (-2 : ℝ) s := by
      simpa using (hasDerivAt_id s).const_mul (-2 : ℝ)
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-2 * u))
        (Real.exp (-2 * s) * (-2)) s :=
      (Real.hasDerivAt_exp (-2 * s)).comp s h1
    simpa [mul_comm] using h2
  have hintExp : ∫ s in (0)..t, -2 * Real.exp (-2 * s) =
      Real.exp (-2 * t) - Real.exp (-2 * 0) := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u => Real.exp (-2 * u))
      (f' := fun u => -2 * Real.exp (-2 * u))
      (a := 0) (b := t) (fun s _ => hderiv_exp s)
      ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
    exact this
  have hintφ : ∫ s in (0)..t, φ s = Ef * (Real.exp (-2 * t) - 1) := by
    show ∫ s in (0)..t, -2 * Real.exp (-2 * s) * Ef = Ef * (Real.exp (-2 * t) - 1)
    rw [show (fun s => -2 * Real.exp (-2 * s) * Ef) =
        (fun s => (-2 * Real.exp (-2 * s)) * Ef) from rfl]
    rw [intervalIntegral.integral_mul_const, hintExp]
    have : Real.exp (-2 * 0) = 1 := by simp
    rw [this, mul_comm]
  have hg0 : g 0 = ∫ x, (f x) ^ 2 ∂γFin n := by
    show ∫ x, (ouSemigroupFin 0 f x) ^ 2 ∂γFin n = ∫ x, (f x) ^ 2 ∂γFin n
    rw [ouSemigroupFin_zero]
  rw [show g t = ∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n from rfl] at hFTC
  rw [hg0, hintφ] at hFTC
  have hEf_rw : (1 - Real.exp (-2 * t)) * ouEnergyFin f f =
      -(Ef * (Real.exp (-2 * t) - 1)) := by
    rw [hEf_def]
    ring
  rw [hEf_rw]
  linarith


/-! ### Restored DirichletMarkovSemigroup bundle (re-homed from the
deleted `EuclideanFinLp.lean` tail; depends on the discharged theorem
`ouSemigroupFin_l2_sq_hasDerivWithinAt` above, not an axiom). -/


private theorem ouSemigroupFinLp_half_normSq_hasDerivWithinAt
    {h : (Fin n → ℝ) → ℝ} (hh : IsCoreFin h) :
    HasDerivWithinAt
      (fun t : ℝ =>
        ‖ouSemigroupFinLp (n := n) (t / 2) ((isCoreFin_memLp (n := n) h hh).toLp h)‖ ^ 2)
      (-ouEnergyFin h h) (Set.Ici 0) 0 := by
  obtain ⟨M, hM⟩ := hh.bound_exists
  let h_mem : MemLp h 2 (γFin n) := isCoreFin_memLp (n := n) h hh
  let ψ : ℝ → ℝ := fun s => ∫ x, (ouSemigroupFin s h x) ^ 2 ∂γFin n
  have hψ : HasDerivWithinAt ψ (-2 * ouEnergyFin h h) (Set.Ici 0) 0 := by
    simpa [ψ, ouEnergyFin, ouSemigroupFin_zero] using
      ouSemigroupFin_l2_sq_hasDerivWithinAt (n := n) h 0 le_rfl hh
  have hhalf : HasDerivWithinAt (fun t : ℝ => t / 2) (1 / 2) (Set.Ici 0) 0 := by
    simpa using ((hasDerivAt_id 0).div_const (2 : ℝ)).hasDerivWithinAt
  have hcomp :
      HasDerivWithinAt (fun t : ℝ => ψ (t / 2))
        ((-2 * ouEnergyFin h h) * (1 / 2)) (Set.Ici 0) 0 := by
    refine HasDerivWithinAt.comp_of_eq (x := 0) (s := Set.Ici 0) (s' := Set.Ici 0)
      (h := fun t : ℝ => t / 2) (h₂ := ψ) hψ hhalf ?_ ?_
    intro t ht
    show 0 ≤ t / 2
    have ht0 : 0 ≤ t := ht
    nlinarith
    ring
  have hEq := by
    have hIci : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ici 0), t ∈ Set.Ici 0 :=
      eventually_mem_of_tendsto_nhdsWithin tendsto_id
    filter_upwards [hIci] with t ht
    have ht2 : 0 ≤ t / 2 := div_nonneg ht zero_le_two
    calc
      ‖ouSemigroupFinLp (n := n) (t / 2) (h_mem.toLp h)‖ ^ 2
          = ‖(ouSemigroupFin_memLp_of_bound (n := n) (t / 2) hh.measurable hM).toLp
              (ouSemigroupFin (t / 2) h)‖ ^ 2 := by
                rw [ouSemigroupFinLp_eq_toLp_of_bound (n := n) (t / 2) ht2 hh.measurable hM]
      _ = ψ (t / 2) := by
            simpa [ψ] using
              (norm_sq_toLp_eq_integral_sq (n := n)
                (ouSemigroupFin_memLp_of_bound (n := n) (t / 2) hh.measurable hM))
  have hmain :
      HasDerivWithinAt
        (fun t : ℝ =>
          ‖ouSemigroupFinLp (n := n) (t / 2) ((isCoreFin_memLp (n := n) h hh).toLp h)‖ ^ 2)
        ((-2 * ouEnergyFin h h) * (1 / 2)) (Set.Ici 0) 0 :=
    hcomp.congr_of_eventuallyEq hEq (by
      simpa [ψ, ouSemigroupFin_zero, ouSemigroupFinLp_zero] using
        (norm_sq_toLp_eq_integral_sq (n := n) h_mem))
  convert hmain using 1
  ring

private theorem ouSemigroupFinLp_pairing_eq_polarization
    (t : ℝ) (ht : 0 ≤ t) (f g : Lp ℝ 2 (γFin n)) :
    4 * ⟪f, ouSemigroupFinLp (n := n) t g⟫_ℝ =
      ‖ouSemigroupFinLp (n := n) (t / 2) (f + g)‖ ^ 2 -
        ‖ouSemigroupFinLp (n := n) (t / 2) (f - g)‖ ^ 2 := by
  have ht2 : 0 ≤ t / 2 := div_nonneg ht zero_le_two
  let u := ouSemigroupFinLp (n := n) (t / 2) f
  let v := ouSemigroupFinLp (n := n) (t / 2) g
  have hpair :
      ⟪f, ouSemigroupFinLp (n := n) t g⟫_ℝ = ⟪u, v⟫_ℝ := by
    rw [show t = t / 2 + t / 2 by ring]
    rw [ouSemigroupFinLp_semigroup (n := n) (t / 2) (t / 2) ht2 ht2]
    simpa [u, v] using
      (ouSemigroupFinLp_symmetric (n := n) (t / 2) ht2 f
        (ouSemigroupFinLp (n := n) (t / 2) g))
  have hadd :
      ouSemigroupFinLp (n := n) (t / 2) (f + g) = u + v := by
    simp [u, v]
  have hsub :
      ouSemigroupFinLp (n := n) (t / 2) (f - g) = u - v := by
    simp [u, v]
  calc
    4 * ⟪f, ouSemigroupFinLp (n := n) t g⟫_ℝ = 4 * ⟪u, v⟫_ℝ := by rw [hpair]
    _ = ‖u + v‖ ^ 2 - ‖u - v‖ ^ 2 := by
          linarith [norm_add_sq_real u v, norm_sub_sq_real u v]
    _ = ‖ouSemigroupFinLp (n := n) (t / 2) (f + g)‖ ^ 2 -
          ‖ouSemigroupFinLp (n := n) (t / 2) (f - g)‖ ^ 2 := by
            rw [hadd, hsub]

private theorem ouEnergyFin_polarization
    {f g : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (hg : IsCoreFin g) :
    ouEnergyFin (f - g) (f - g) - ouEnergyFin (f + g) (f + g) = -4 * ouEnergyFin f g := by
  have hplus : IsCoreFin (f + g) := IsCoreFin_add hf hg
  have hneg : IsCoreFin ((-1 : ℝ) • g) := IsCoreFin_smul (-1 : ℝ) hg
  have hminus : IsCoreFin (f - g) := by
    simpa [sub_eq_add_neg] using IsCoreFin_add hf hneg
  have hΓ :
      (fun x => ouGammaFin (f - g) (f - g) x - ouGammaFin (f + g) (f + g) x) =
        fun x => -4 * ouGammaFin f g x := by
    ext x
    unfold ouGammaFin
    calc
      (∑ i : Fin n, partialDeriv i (f - g) x * partialDeriv i (f - g) x) -
          ∑ i : Fin n, partialDeriv i (f + g) x * partialDeriv i (f + g) x
          = ∑ i : Fin n,
              (partialDeriv i (f - g) x * partialDeriv i (f - g) x -
                partialDeriv i (f + g) x * partialDeriv i (f + g) x) := by
              rw [Finset.sum_sub_distrib]
        _ = ∑ i : Fin n,
              ((partialDeriv i f x - partialDeriv i g x) *
                  (partialDeriv i f x - partialDeriv i g x) -
                (partialDeriv i f x + partialDeriv i g x) *
                  (partialDeriv i f x + partialDeriv i g x)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [show partialDeriv i (f - g) x = partialDeriv i f x - partialDeriv i g x by
                    have hsub : partialDeriv i (f - g) = fun x => partialDeriv i f x - partialDeriv i g x := by
                      funext x
                      rw [sub_eq_add_neg]
                      have hnegfun : (-g : (Fin n → ℝ) → ℝ) = (-1 : ℝ) • g := by
                        funext y
                        simp
                      rw [hnegfun, partialDeriv_add i hf.contDiff hneg.contDiff, partialDeriv_smul]
                      ring
                    simpa using congrFun hsub x,
                  partialDeriv_add i hf.contDiff hg.contDiff]
        _ = ∑ i : Fin n, -4 * (partialDeriv i f x * partialDeriv i g x) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = -4 * ∑ i : Fin n, partialDeriv i f x * partialDeriv i g x := by
              rw [Finset.mul_sum]
  calc
    ouEnergyFin (f - g) (f - g) - ouEnergyFin (f + g) (f + g)
        = ∫ x, (ouGammaFin (f - g) (f - g) x - ouGammaFin (f + g) (f + g) x) ∂γFin n := by
            rw [ouEnergyFin, ouEnergyFin,
              integral_sub (hminus.integrable_gamma hminus) (hplus.integrable_gamma hplus)]
    _ = ∫ x, -4 * ouGammaFin f g x ∂γFin n := by rw [hΓ]
    _ = -4 * ouEnergyFin f g := by rw [ouEnergyFin, integral_const_mul]

theorem ouSemigroupFin_energy_eq_deriv (f g : (Fin n → ℝ) → ℝ)
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    HasDerivWithinAt
      (fun t : ℝ => ⟪(isCoreFin_memLp (n := n) f hf).toLp f,
                     ouSemigroupFinLp (n := n) t ((isCoreFin_memLp (n := n) g hg).toLp g)⟫_ℝ)
      (-(ouEnergyFin f g)) (Set.Ici 0) 0 := by
  let fLp : Lp ℝ 2 (γFin n) := (isCoreFin_memLp (n := n) f hf).toLp f
  let gLp : Lp ℝ 2 (γFin n) := (isCoreFin_memLp (n := n) g hg).toLp g
  let hf_mem : MemLp f 2 (γFin n) := isCoreFin_memLp (n := n) f hf
  let hg_mem : MemLp g 2 (γFin n) := isCoreFin_memLp (n := n) g hg
  have hplus : IsCoreFin (f + g) := IsCoreFin_add hf hg
  have hneg : IsCoreFin ((-1 : ℝ) • g) := IsCoreFin_smul (-1 : ℝ) hg
  have hminus : IsCoreFin (f - g) := by
    simpa [sub_eq_add_neg] using IsCoreFin_add hf hneg
  have hplusD :
      HasDerivWithinAt
        (fun t : ℝ =>
          ‖ouSemigroupFinLp (n := n) (t / 2) ((isCoreFin_memLp (n := n) (f + g) hplus).toLp
            (f + g))‖ ^ 2)
        (-ouEnergyFin (f + g) (f + g)) (Set.Ici 0) 0 :=
    ouSemigroupFinLp_half_normSq_hasDerivWithinAt (n := n) hplus
  have hminusD :
      HasDerivWithinAt
        (fun t : ℝ =>
          ‖ouSemigroupFinLp (n := n) (t / 2) ((isCoreFin_memLp (n := n) (f - g) hminus).toLp
            (f - g))‖ ^ 2)
        (-ouEnergyFin (f - g) (f - g)) (Set.Ici 0) 0 :=
    ouSemigroupFinLp_half_normSq_hasDerivWithinAt (n := n) hminus
  have hpol :
      HasDerivWithinAt
        (fun t : ℝ =>
          (1 / 4) *
            (‖ouSemigroupFinLp (n := n) (t / 2)
                ((isCoreFin_memLp (n := n) (f + g) hplus).toLp (f + g))‖ ^ 2 -
              ‖ouSemigroupFinLp (n := n) (t / 2)
                ((isCoreFin_memLp (n := n) (f - g) hminus).toLp (f - g))‖ ^ 2))
        ((1 / 4) * ((-ouEnergyFin (f + g) (f + g)) - (-ouEnergyFin (f - g) (f - g))))
        (Set.Ici 0) 0 := by
    exact (hplusD.sub hminusD).const_mul (1 / 4)
  have hEq :
      (fun t : ℝ => ⟪fLp, ouSemigroupFinLp (n := n) t gLp⟫_ℝ) =ᶠ[nhdsWithin 0 (Set.Ici 0)]
        (fun t : ℝ =>
          (1 / 4) *
            (‖ouSemigroupFinLp (n := n) (t / 2)
                ((isCoreFin_memLp (n := n) (f + g) hplus).toLp (f + g))‖ ^ 2 -
              ‖ouSemigroupFinLp (n := n) (t / 2)
                ((isCoreFin_memLp (n := n) (f - g) hminus).toLp (f - g))‖ ^ 2)) := by
    have hIci : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ici 0), t ∈ Set.Ici 0 :=
      eventually_mem_of_tendsto_nhdsWithin tendsto_id
    filter_upwards [hIci] with t ht
    have hpair := ouSemigroupFinLp_pairing_eq_polarization (n := n) t ht fLp gLp
    have hplusLp : ((hf_mem.add hg_mem).toLp (f + g)) = fLp + gLp :=
      MemLp.toLp_add hf_mem hg_mem
    have hminusLp : ((hf_mem.sub hg_mem).toLp (f - g)) = fLp - gLp :=
      MemLp.toLp_sub hf_mem hg_mem
    calc
      ⟪fLp, ouSemigroupFinLp (n := n) t gLp⟫_ℝ
          = (1 / 4) * (4 * ⟪fLp, ouSemigroupFinLp (n := n) t gLp⟫_ℝ) := by ring
      _ = (1 / 4) *
            (‖ouSemigroupFinLp (n := n) (t / 2)
                ((hf_mem.add hg_mem).toLp (f + g))‖ ^ 2 -
              ‖ouSemigroupFinLp (n := n) (t / 2)
                ((hf_mem.sub hg_mem).toLp (f - g))‖ ^ 2) := by
              rw [hpair, ← hplusLp, ← hminusLp]
  have h0eq :
      ⟪fLp, ouSemigroupFinLp (n := n) 0 gLp⟫_ℝ =
        (1 / 4) *
          (‖ouSemigroupFinLp (n := n) (0 / 2)
              ((isCoreFin_memLp (n := n) (f + g) hplus).toLp (f + g))‖ ^ 2 -
            ‖ouSemigroupFinLp (n := n) (0 / 2)
              ((isCoreFin_memLp (n := n) (f - g) hminus).toLp (f - g))‖ ^ 2) := by
    have hpair := ouSemigroupFinLp_pairing_eq_polarization (n := n) 0 le_rfl fLp gLp
    have hplusLp : ((hf_mem.add hg_mem).toLp (f + g)) = fLp + gLp :=
      MemLp.toLp_add hf_mem hg_mem
    have hminusLp : ((hf_mem.sub hg_mem).toLp (f - g)) = fLp - gLp :=
      MemLp.toLp_sub hf_mem hg_mem
    calc
      ⟪fLp, ouSemigroupFinLp (n := n) 0 gLp⟫_ℝ
          = (1 / 4) * (4 * ⟪fLp, ouSemigroupFinLp (n := n) 0 gLp⟫_ℝ) := by ring
      _ = (1 / 4) *
            (‖ouSemigroupFinLp (n := n) (0 / 2)
                ((hf_mem.add hg_mem).toLp (f + g))‖ ^ 2 -
              ‖ouSemigroupFinLp (n := n) (0 / 2)
                ((hf_mem.sub hg_mem).toLp (f - g))‖ ^ 2) := by
              rw [hpair, ← hplusLp, ← hminusLp]
  have hmain :
      HasDerivWithinAt
        (fun t : ℝ => ⟪fLp, ouSemigroupFinLp (n := n) t gLp⟫_ℝ)
        ((1 / 4) * ((-ouEnergyFin (f + g) (f + g)) - (-ouEnergyFin (f - g) (f - g))))
        (Set.Ici 0) 0 :=
    hpol.congr_of_eventuallyEq hEq h0eq
  convert hmain using 1
  have hE := ouEnergyFin_polarization (n := n) hf hg
  linarith

/-- The multivariate Gaussian OU semigroup on `L²(γFin n)`, bundled
with the canonical Dirichlet form data.

TODO: replace the current `energy_eq_deriv` proof by the direct
Fubini lift of the discharged 1D boundary derivative identity, so this
bundle no longer depends on
`ouSemigroupFin_l2_sq_hasDerivWithinAt`. -/
noncomputable def stdGaussianFin_dirichletMarkovSemigroup (n : ℕ) :
    DirichletMarkovSemigroup (Fin n → ℝ) where
  toMarkovSemigroup := markovSemigroup n
  energy := ouEnergyFin
  energy_symm := (dirichletSpaceFin n).energy_symm
  energy_nonneg := (dirichletSpaceFin n).energy_nonneg
  IsCore := IsCoreFin
  IsCore_const := IsCoreFin_const
  IsCore_add := fun hf hg => IsCoreFin_add hf hg
  IsCore_smul := fun c _ hf => IsCoreFin_smul c hf
  -- Path A, strictly-positive escape. For `f ∈ IsCoreFin` with `ε ≤ f` a.e.,
  -- the full-support property of `γFin n` upgrades the a.e. bound to a pointwise
  -- one (`le_of_ae_le_of_continuous`), and then `IsCoreFin_rpow_pos` gives `f^r`
  -- core via the chain rule plus bounded-derivative propagation on `[ε, M]`.
  IsCore_rpow_pos_strict := by
    intro f hf ε hε hae r
    exact IsCoreFin_rpow_pos hf hε (le_of_ae_le_of_continuous hf.continuous hae) r
  IsCore_memLp_top := fun {f} hf => by
    -- IsCoreFin includes `∃ M, ∀ x, ‖f x‖ ≤ M`. Extract directly.
    obtain ⟨M, hM⟩ := hf.bound_exists
    exact ⟨M, Filter.Eventually.of_forall fun x => by
      have := hM x
      rwa [Real.norm_eq_abs] at this⟩
  energy_add_left := (dirichletSpaceFin n).energy_add_left
  energy_smul_left := (dirichletSpaceFin n).energy_smul_left
  energy_const := (dirichletSpaceFin n).energy_const
  IsCore_memLp := fun {_f} hf => isCoreFin_memLp (n := n) _ hf
  energy_eq_deriv := fun f g hf hg => ouSemigroupFin_energy_eq_deriv (n := n) f g hf hg

end GaussianFin

namespace stdGaussianFin

open GaussianFin

/-- The finite-dimensional standard Gaussian Bakry-Emery structure on `Fin n → ℝ`. -/
@[reducible]
def bakryEmerySpace (n : ℕ) : BakryEmerySpace (Fin n → ℝ) where
  toDirichletSpace := GaussianFin.dirichletSpaceFin n
  Γ := GaussianFin.ouGammaFin
  Γ_symm := fun f g => GaussianFin.ouGammaFin_symm
  Γ_nonneg := fun f x => GaussianFin.ouGammaFin_nonneg x
  energy_eq_integral_Γ := fun f g => rfl
  IsCore_mul := fun hf hg => GaussianFin.IsCoreFin_mul hf hg
  Γ_leibniz := fun f g h hf hg hh x => GaussianFin.ouGammaFin_leibniz hf hg hh x
  Γ_const := fun c f => GaussianFin.ouGammaFin_const_left c f
  semigroup := GaussianFin.ouSemigroupFin
  IsCore_semigroup := fun t ht _ hf => GaussianFin.ouSemigroupFin_preserves_IsCore t ht hf
  ρ := 1
  hρ := one_pos
  gradient_decay := fun f t ht hf => by
    convert GaussianFin.ouSemigroupFin_gradient_decay (n := n) f t ht hf using 1
    simp only [mul_one]
    rfl
  semigroup_zero := fun f => GaussianFin.ouSemigroupFin_zero (n := n) f
  semigroup_add := fun s t f hs ht hf =>
    GaussianFin.ouSemigroupFin_compose (n := n) s t hs ht hf
  semigroup_contraction := fun f t ht hf =>
    GaussianFin.ouSemigroupFin_contraction (n := n) f t ht hf
  semigroup_mean := fun f t ht hf =>
    GaussianFin.ouSemigroupFin_mean (n := n) f t ht hf
  semigroup_selfAdjoint := fun f g t ht hf hg =>
    GaussianFin.ouSemigroupFin_selfAdjoint (n := n) f g t ht hf hg
  semigroup_l2_decay_bound := fun f t ht hf => by
    convert GaussianFin.ouSemigroupFin_l2_decay_bound (n := n) f t ht hf using 1
    simp only [mul_one, div_one]
    rfl
  semigroup_l2_sq_hasDerivWithinAt := fun f t ht hf =>
    GaussianFin.ouSemigroupFin_l2_sq_hasDerivWithinAt f t ht hf
  semigroup_ergodic := fun f hf =>
    GaussianFin.ouSemigroupFin_ergodic (n := n) f hf
  semigroup_entropy_sq_decay_bound := fun f t ht hf =>
    GaussianFin.ouSemigroupFin_entropy_sq_decay_bound f t ht hf
  semigroup_entropy_sq_ergodic := fun f hf =>
    GaussianFin.ouSemigroupFin_entropy_sq_ergodic (n := n) f hf

end stdGaussianFin
