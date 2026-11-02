/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The three smooth-core lemmas below are extracted from the attributed
EuclideanFinLp port (same proofs), exposing its private approximation adapter.
-/
import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanFinBE
import AcceleratedLogConcave.Analysis.Poisson.Centered

noncomputable section
open MeasureTheory InnerProductSpace Filter Set
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open GaussianFin Analysis.Poisson
variable {n : ℕ}

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

theorem smoothCompact_isCore {f : (Fin n → ℝ) → ℝ}
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


/-- The actual Gaussian Mehler operator preserves the mean on its smooth core. -/
theorem ou_mean_core (t : ℝ) (ht : 0 ≤ t) (f : (Fin n → ℝ) → ℝ) (hf : IsCoreFin f) :
    mean (γFin n) (ouSemigroupFinLp t ((isCoreFin_memLp f hf).toLp f)) =
      mean (γFin n) ((isCoreFin_memLp f hf).toLp f) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  rw [ouSemigroupFinLp_eq_toLp_of_bound t ht hf.measurable hM, mean_apply, mean_apply]
  rw [integral_congr_ae (ouSemigroupFin_memLp_of_bound t hf.measurable hM).coeFn_toLp,
    integral_congr_ae (isCoreFin_memLp f hf).coeFn_toLp]
  exact ouSemigroupFin_mean f t ht hf

/-- The constructed Mehler operator's sharp variance decay on smooth core data. -/
theorem ou_variance_core (t : ℝ) (ht : 0 ≤ t) (f : (Fin n → ℝ) → ℝ) (hf : IsCoreFin f) :
    ‖ouSemigroupFinLp t ((isCoreFin_memLp f hf).toLp f)‖ ^ 2 -
      (mean (γFin n) ((isCoreFin_memLp f hf).toLp f)) ^ 2 ≤
      Real.exp (-2 * t) * (‖(isCoreFin_memLp f hf).toLp f‖ ^ 2 -
        (mean (γFin n) ((isCoreFin_memLp f hf).toLp f)) ^ 2) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  rw [ouSemigroupFinLp_eq_toLp_of_bound t ht hf.measurable hM,
    norm_sq_toLp_eq_integral_sq, norm_sq_toLp_eq_integral_sq, mean_apply,
    integral_congr_ae (isCoreFin_memLp f hf).coeFn_toLp]
  have h := (stdGaussianFin.bakryEmerySpace n).variance_decay f t ht hf
  change (∫ x, (ouSemigroupFin t f x)^2 ∂γFin n) -
    (∫ x, ouSemigroupFin t f x ∂γFin n)^2 ≤
    Real.exp (-2 * 1 * t) * ((∫ x, (f x)^2 ∂γFin n) - (∫ x, f x ∂γFin n)^2) at h
  simpa only [ouSemigroupFin_mean f t ht hf, mul_one] using h

/-- Smooth compact Gaussian test functions are dense in the actual L2 quotient. -/
theorem gaussian_smooth_induction (S : Set (Lp ℝ 2 (γFin n))) (hS : IsClosed S)
    (hcore : ∀ f : (Fin n → ℝ) → ℝ, ∀ hf : IsCoreFin f,
      (isCoreFin_memLp f hf).toLp f ∈ S) (u : Lp ℝ 2 (γFin n)) : u ∈ S := by
  let T : Set (Lp ℝ 2 (γFin n)) := {u | ∃ f : (Fin n → ℝ) → ℝ,
    u =ᵐ[γFin n] f ∧ HasCompactSupport f ∧ ContDiff ℝ (⊤ : ℕ∞) f}
  have hd : Dense T := by
    simpa [T] using (Lp.dense_hasCompactSupport_contDiff
      (E := Fin n → ℝ) (F := ℝ) (μ := γFin n) (p := (2 : ENNReal)) ENNReal.ofNat_ne_top)
  have hs : T ⊆ S := by
    rintro u ⟨f, huf, hc, hf⟩
    have hk := smoothCompact_isCore hc hf
    have he : u = (isCoreFin_memLp f hk).toLp f :=
      Lp.ext (huf.trans (isCoreFin_memLp f hk).coeFn_toLp.symm)
    rw [he]
    exact hcore f hk
  exact hS.closure_subset_iff.mpr hs (by simp only [hd.closure_eq, mem_univ])

/-- The actual Mehler operator preserves means for every L2 input. -/
theorem ou_mean (t : ℝ) (ht : 0 ≤ t) (u : Lp ℝ 2 (γFin n)) :
    mean (γFin n) (ouSemigroupFinLp t u) = mean (γFin n) u := by
  apply gaussian_smooth_induction
    {u | mean (γFin n) (ouSemigroupFinLp t u) = mean (γFin n) u}
    (isClosed_eq ((mean (γFin n)).continuous.comp (ouSemigroupFinLp t).continuous)
      (mean (γFin n)).continuous)
  exact fun f hf => ou_mean_core t ht f hf

/-- Sharp Gaussian OU variance contraction for every actual L2 input. -/
theorem ou_variance (t : ℝ) (ht : 0 ≤ t) (u : Lp ℝ 2 (γFin n)) :
    ‖ouSemigroupFinLp t u‖ ^ 2 - (mean (γFin n) u)^2 ≤
      Real.exp (-2*t) * (‖u‖^2 - (mean (γFin n) u)^2) := by
  refine gaussian_smooth_induction
    {u | ‖ouSemigroupFinLp t u‖ ^ 2 - (mean (γFin n) u)^2 ≤
      Real.exp (-2*t) * (‖u‖^2 - (mean (γFin n) u)^2)}
    (isClosed_le (((ouSemigroupFinLp t).continuous.norm.pow 2).sub
      ((mean (γFin n)).continuous.pow 2))
      (continuous_const.mul ((continuous_norm.pow 2).sub ((mean (γFin n)).continuous.pow 2)))) ?_ u
  exact fun f hf => ou_variance_core t ht f hf

/-- Centered L2 data contract with the exact squared correlation exp(-2t). -/
theorem ou_centered_norm_sq (t : ℝ) (ht : 0 ≤ t) (u : Lp ℝ 2 (γFin n))
    (hu : mean (γFin n) u = 0) :
    ‖ouSemigroupFinLp t u‖^2 ≤ Real.exp (-2*t) * ‖u‖^2 := by
  simpa only [hu, zero_pow (by decide : 2 ≠ 0), sub_zero] using ou_variance t ht u

end AcceleratedLogConcave.Kinetic.Reheating
