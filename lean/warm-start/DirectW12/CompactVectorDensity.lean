import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space

/-!

-/
noncomputable section
open MeasureTheory Set Metric
open scoped Topology NNReal ENNReal
namespace AcceleratedLogConcave.Kinetic.DirectW12

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Smooth an actual compact continuous vector test uniformly, then multiply
by a smooth bump which is one on its support. The multiplication preserves the
uniform error even outside the support, because the original test is zero. -/
theorem exists_compact_contDiff_vector_approx {f : X → V}
    (hf : Continuous f) (hc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : X → V, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧
      ∀ x, dist (ψ x) (f x) < ε := by
  obtain ⟨r, hr, hsupport⟩ :=
    hc.isCompact.isBounded.subset_closedBall_lt 0 (0 : X)
  let χ : ContDiffBump (0 : X) := ⟨r, r + 1, hr, by linarith⟩
  obtain ⟨g, hg, hgf⟩ :=
    (hc.uniformContinuous_of_continuous hf).exists_contDiff_dist_le hε
  refine ⟨fun x => χ x • g x, χ.contDiff.smul (hg.of_le (by simp)), ?_, ?_⟩
  · change HasCompactSupport ((χ : X → ℝ) • g)
    exact χ.hasCompactSupport.smul_right
  · intro x
    have hfix : χ x • f x = f x := by
      by_cases hx : f x = 0
      · simp [hx]
      · rw [χ.one_of_mem_closedBall (hsupport
          (subset_tsupport f (Function.mem_support.mpr hx))), one_smul]
    calc
      dist (χ x • g x) (f x) = ‖χ x • (g x - f x)‖ := by
        rw [smul_sub, hfix, dist_eq_norm]
      _ = χ x * ‖g x - f x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
      _ ≤ ‖g x - f x‖ := mul_le_of_le_one_left (norm_nonneg _) χ.le_one
      _ < ε := by simpa only [dist_eq_norm] using hgf x

/-- Density is proved for the actual vector-valued L² classes, not merely for
scalar coordinate functions, and not supplied as a field or a hypothesis. -/
theorem compact_contDiff_vector_dense (μ : Measure X) [IsProbabilityMeasure μ] :
    Dense {v : Lp V 2 μ | ∃ (ψ : X → V) (hψ : ContDiff ℝ 1 ψ)
      (hc : HasCompactSupport ψ),
      v = (hψ.continuous.memLp_of_hasCompactSupport hc).toLp ψ} := by
  intro v
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hδ : 0 < ε / 3 := by positivity
  obtain ⟨f, hc, herr, hf, hfm⟩ :=
    (Lp.memLp v).exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (show ENNReal.ofReal (ε / 3) ≠ 0 by positivity)
  obtain ⟨ψ, hψ, hcψ, hclose⟩ := exists_compact_contDiff_vector_approx hf hc hδ
  let w : Lp V 2 μ := hfm.toLp f
  let q : Lp V 2 μ := (hψ.continuous.memLp_of_hasCompactSupport hcψ).toLp ψ
  have hfirst : dist v w ≤ ε / 3 := by
    apply (edist_le_ofReal hδ.le).mp
    calc
      edist v w = edist ((Lp.memLp v).toLp (v : X → V)) (hfm.toLp f) := by
        rw [Lp.toLp_coeFn]
      _ = eLpNorm ((v : X → V) - f) 2 μ := Lp.edist_toLp_toLp _ _ _ _
      _ ≤ ENNReal.ofReal (ε / 3) := herr
  have hsecond : dist w q ≤ ε / 3 := by
    rw [dist_eq_norm]
    have hb : ∀ᵐ x ∂μ, ‖(w - q) x‖ ≤ ε / 3 := by
      filter_upwards [Lp.coeFn_sub w q, hfm.coeFn_toLp,
        (hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with x hx hw hq
      rw [hx, Pi.sub_apply, hw, hq, ← dist_eq_norm, dist_comm]
      exact (hclose x).le
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hδ.le hb
  refine ⟨q, ⟨ψ, hψ, hcψ, rfl⟩, ?_⟩
  exact ((dist_triangle v w q).trans (add_le_add hfirst hsecond)).trans_lt (by linarith)

end AcceleratedLogConcave.Kinetic.DirectW12
