import AcceleratedLogConcave.Numerics.MeanSmoothCollocationLp

/-!
# Quantitative error for the unchanged smooth mean collocation

The hypotheses are the actual mesh conditions, a strict contraction for the
actual graph, and full regularity of `curvesWithSmoothBranches`. The geometric
estimate separates the finite-iteration error, the row quadrature residual,
and the full centering defect. The epsilon consumer merely allocates these
three explicit terms; it does not infer regularity or a returned-law bound.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.AffineGraph
open Numerics.AffineGraph.MeanGeometry Numerics.MeanCollocationLp
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.SmoothQuantitativeError
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

variable (d : Data ι m) (h₀ : ℝ) (h : MeshConditions d h₀)
  (l v : ℝ) (hl : l < 0) (hv : backwardEnd d.G.R < v)
  (D : AffineResidual.Mean.DerivativeBudget d.G)
  (hreg : AffineResidual.Mean.Regularity d.G (curvesWithSmoothBranches d)
    (operator d) 0 d.r l v D)
include h hl hv hreg

/-- The geometric-series estimate for the original final L² output. The
quadrature term is the maximum of the actual row-error budget, and the
centering term retains its full factor `2`. -/
theorem geometric_final_bound (N : ℕ) (hq : contraction d h₀ < 1) :
    ‖output d N - terminalTarget d‖ ≤
      d.ell * (contraction d h₀ ^ N * initialError d) +
      d.ell * (residualBudget d h₀ D / (1 - contraction d h₀)) +
      2 * D.center / (m.factorial : ℝ) := by
  have hfinite := MeanSmoothCollocationLp.final_bound d h₀ h l v hl hv D hreg N
  calc
    ‖output d N - terminalTarget d‖ ≤
        d.ell * finiteError d h₀ D N + 2 * D.center / (m.factorial : ℝ) := hfinite
    _ ≤ d.ell * (contraction d h₀ ^ N * initialError d +
          residualBudget d h₀ D / (1 - contraction d h₀)) +
          2 * D.center / (m.factorial : ℝ) := by
      have hsum : finiteError d h₀ D N ≤
          contraction d h₀ ^ N * initialError d +
            residualBudget d h₀ D / (1 - contraction d h₀) := by
        unfold finiteError
        have hs : (∑ j ∈ Finset.range N, contraction d h₀ ^ j) ≤
            1 / (1 - contraction d h₀) := by
          simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := N)
            (contraction_nonneg d h₀ h) hq
        simpa only [div_eq_mul_inv, one_mul, residualBudget] using
          add_le_add (le_refl (contraction d h₀ ^ N * initialError d))
            (mul_le_mul_of_nonneg_left hs
              (norm_nonneg (D.rowError d.G d.r d.sigma h₀)))
      exact add_le_add (mul_le_mul_of_nonneg_left hsum d.hell) le_rfl
    _ = d.ell * (contraction d h₀ ^ N * initialError d) +
          d.ell * (residualBudget d h₀ D / (1 - contraction d h₀)) +
          2 * D.center / (m.factorial : ℝ) := by ring

/-- An epsilon certificate with independent allocations for finite iteration,
row quadrature, and centering. It applies to the unchanged common-seed output. -/
theorem output_error_le (N : ℕ) (hq : contraction d h₀ < 1)
    (ε εiteration εquadrature εcentering : ℝ)
    (hiteration : d.ell * (contraction d h₀ ^ N * initialError d) ≤ εiteration)
    (hquadrature : d.ell * (residualBudget d h₀ D /
      (1 - contraction d h₀)) ≤ εquadrature)
    (hcentering : 2 * D.center / (m.factorial : ℝ) ≤ εcentering)
    (htotal : εiteration + εquadrature + εcentering ≤ ε) :
    ‖output d N - terminalTarget d‖ ≤ ε := by
  calc
    ‖output d N - terminalTarget d‖ ≤
        d.ell * (contraction d h₀ ^ N * initialError d) +
        d.ell * (residualBudget d h₀ D / (1 - contraction d h₀)) +
        2 * D.center / (m.factorial : ℝ) :=
      geometric_final_bound d h₀ h l v hl hv D hreg N hq
    _ ≤ εiteration + εquadrature + εcentering :=
      add_le_add (add_le_add hiteration hquadrature) hcentering
    _ ≤ ε := htotal

/-- The same certificate for the literal raw common-seed output, expressed in
`L²` against the original stationary-score benchmark. -/
theorem raw_output_error_le (N : ℕ) (hq : contraction d h₀ < 1)
    (ε εiteration εquadrature εcentering : ℝ)
    (hiteration : d.ell * (contraction d h₀ ^ N * initialError d) ≤ εiteration)
    (hquadrature : d.ell * (residualBudget d h₀ D /
      (1 - contraction d h₀)) ≤ εquadrature)
    (hcentering : 2 * D.center / (m.factorial : ℝ) ≤ εcentering)
    (htotal : εiteration + εquadrature + εcentering ≤ ε) :
    ∃ he : MemLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω)
        2 (seedMeasure d),
      ‖he.toLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω)‖ ≤ ε := by
  obtain ⟨he, hbound⟩ :=
    MeanSmoothCollocationLp.raw_final_bound d h₀ h l v hl hv D hreg N
  refine ⟨he, ?_⟩
  calc
    ‖he.toLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω)‖ ≤
        d.ell * finiteError d h₀ D N + 2 * D.center / (m.factorial : ℝ) := hbound
    _ ≤ d.ell * (contraction d h₀ ^ N * initialError d +
          residualBudget d h₀ D / (1 - contraction d h₀)) +
          2 * D.center / (m.factorial : ℝ) := by
      have hs : (∑ j ∈ Finset.range N, contraction d h₀ ^ j) ≤
          1 / (1 - contraction d h₀) := by
        simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := N)
          (contraction_nonneg d h₀ h) hq
      have hsum : finiteError d h₀ D N ≤
          contraction d h₀ ^ N * initialError d +
            residualBudget d h₀ D / (1 - contraction d h₀) := by
        unfold finiteError
        simpa only [div_eq_mul_inv, one_mul, residualBudget] using
          add_le_add (le_refl (contraction d h₀ ^ N * initialError d))
            (mul_le_mul_of_nonneg_left hs
              (norm_nonneg (D.rowError d.G d.r d.sigma h₀)))
      exact add_le_add (mul_le_mul_of_nonneg_left hsum d.hell) le_rfl
    _ = d.ell * (contraction d h₀ ^ N * initialError d) +
          d.ell * (residualBudget d h₀ D / (1 - contraction d h₀)) +
          2 * D.center / (m.factorial : ℝ) := by ring
    _ ≤ εiteration + εquadrature + εcentering :=
      add_le_add (add_le_add hiteration hquadrature) hcentering
    _ ≤ ε := htotal

end AcceleratedLogConcave.Numerics.SmoothQuantitativeError
