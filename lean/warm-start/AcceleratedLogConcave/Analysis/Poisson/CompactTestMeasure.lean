import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! Finite laws are determined by compact C1 test functions. This is the
measure-extensionality step for the actual continuity-equation transport proof.
The approximation argument adapts openai/math's measure_eq_of_smooth_lipschitz
(Sampling/MeasureSmoothLipschitz.lean, revision
1581d4cbdd69a0faf34b2089614fe2a814316a6a, Apache-2.0), using a fixed compact
bump and a compact-test hypothesis instead of the upstream expanding cutoffs. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace AcceleratedLogConcave.Analysis.Poisson

/-- Compact C1 tests suffice to identify two finite Borel measures. -/
theorem measure_eq_of_compact_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ x, φ x ∂μ) = ∫ x, φ x ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  obtain ⟨R, hR, hsupport⟩ := f.hasCompactSupport.isBounded.subset_closedBall_lt 0 (0 : E)
  let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩
  have hχf (x : E) : χ x * f x = f x := by
    by_cases hx : f x = 0
    · simp [hx]
    · rw [χ.one_of_mem_closedBall (hsupport (subset_tsupport f hx)), one_mul]
  obtain ⟨B, hB⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hε (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose g hgc hgd using fun n : ℕ =>
    (f.hasCompactSupport.uniformContinuous_of_continuous f.continuous).exists_contDiff_dist_le (hε n)
  have hgb (n : ℕ) (x : E) : ‖g n x‖ ≤ B + 1 := by
    have he : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
    have hd := (hgd n x).le.trans he
    rw [dist_eq_norm] at hd
    exact (norm_le_norm_add_norm_sub' (g n x) (f x)).trans (add_le_add (hB x) hd)
  let u (n : ℕ) (x : E) := χ x * g n x
  have huc (n : ℕ) : ContDiff ℝ 1 (u n) := χ.contDiff.mul ((hgc n).of_le (by simp))
  have huk (n : ℕ) : HasCompactSupport (u n) := χ.hasCompactSupport.mul_right
  have hub (n : ℕ) (x : E) : ‖u n x‖ ≤ B + 1 := by
    change ‖χ x * g n x‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) χ.le_one).trans (hgb n x)
  have hut (x : E) : Tendsto (fun n => u n x) atTop (𝓝 (f x)) := by
    have hg : Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hgd n x).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [hχf] using (tendsto_const_nhds (x := χ x)).mul hg
  have hlim (η : Measure E) [IsFiniteMeasure η] :
      Tendsto (fun n => ∫ x, u n x ∂η) atTop (𝓝 (∫ x, f x ∂η)) :=
    tendsto_integral_of_dominated_convergence (fun _ => B + 1)
      (fun n => (huc n).continuous.aestronglyMeasurable) (integrable_const (B + 1))
      (fun n => Eventually.of_forall (hub n)) (Eventually.of_forall hut)
  have he : (fun n => ∫ x, u n x ∂μ) = (fun n => ∫ x, u n x ∂ν) :=
    funext fun n => h (u n) (huc n) (huk n)
  exact tendsto_nhds_unique (hlim μ) (he ▸ hlim ν)

end AcceleratedLogConcave.Analysis.Poisson
