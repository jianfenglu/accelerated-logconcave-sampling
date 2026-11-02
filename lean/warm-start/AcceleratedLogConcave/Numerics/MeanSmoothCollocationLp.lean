import AcceleratedLogConcave.Numerics.MeanCollocationLp
import AcceleratedLogConcave.Numerics.SmoothAllReceiver

/-!
# The all-fields smooth receiver for the unchanged mean collocation

This additive interface consumes full `AffineResidual.Mean.Regularity` on
`curvesWithSmoothBranches d`. It does not transfer endpoint regularity to the
legacy clamped curves, and it does not replace the iteration or its common seed.

The quantitative velocity, center-mean and physical-angle fields remain explicit
premises. In particular, this file does not supply their derivative budgets or
prove recursive gradient-compiler accuracy, sharp stability, or a returned-law
claim. The final centering defect remains `2 * D.center / m.factorial`.

Candidate source only: no Lean elaboration or compilation receipt is supplied.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.AffineGraph
open Numerics.AffineGraph.MeanGeometry Numerics.MeanCollocationLp
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.MeanSmoothCollocationLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

section Error
variable (d : Data ι m) (h₀ : ℝ) (h : MeshConditions d h₀)
  (l v : ℝ) (hl : l < 0) (hv : backwardEnd d.G.R < v)
  (D : AffineResidual.Mean.DerivativeBudget d.G)
  (hreg : AffineResidual.Mean.Regularity d.G (curvesWithSmoothBranches d)
    (operator d) 0 d.r l v D)
include h hl hv hreg

/-- The actual graph-row residual, before taking the maximum over row budgets. -/
theorem row_residual_bound (i : d.G.MeanNode) :
    ‖(lpGraph d).step (operator d) (reference d) i - reference d i‖ ≤
      D.rowError d.G d.r d.sigma h₀ i := by
  have he := smoothBranches_canonical_equations d
  have hb := AffineResidual.Mean.meanResidual d.G h.order d.r d.sigma h₀ l v
    d.hr d.hsigma h.step_pos.le hl hv (cell_bound d h₀ h)
    (operator d) 0 (initialPosition d) (initialScore d) (initialNoise d)
    (curvesWithSmoothBranches d) D he hreg i
  rw [smoothBranches_reference_eq] at hb
  exact hb

/-- The existing residual budget bounds every row of the original graph. -/
theorem residual_bound (i : d.G.MeanNode) :
    ‖(lpGraph d).step (operator d) (reference d) i - reference d i‖ ≤
      residualBudget d h₀ D := by
  exact (row_residual_bound d h₀ h l v hl hv D hreg i).trans
    ((le_abs_self _).trans (norm_le_pi_norm (D.rowError d.G d.r d.sigma h₀) i))

/-- Finite simultaneous iteration with the original initializer and operator.
The maximum is outside the individual L² norms. -/
theorem finite_bound (N : ℕ) :
    ‖iterate d N - reference d‖ ≤ finiteError d h₀ D N := by
  have hb := Collocation.iteratePhi_error_le ((lpGraph d).step (operator d))
    (lpGraph d).direct (reference d) (contraction d h₀) (residualBudget d h₀ D) N
    (contraction_nonneg d h₀ h) (norm_nonneg _) (contraction_target d h₀ h)
    (residual_bound d h₀ h l v hl hv D hreg)
  simpa only [Collocation.iteratePhi, ← FiniteGraph.iterate_eq_function_iterate,
    Collocation.nodeError, iterate, finiteError, initialError] using hb

/-- A geometric bound requires the separately stated strict contraction. -/
theorem geometric_bound (N : ℕ) (hq : contraction d h₀ < 1) :
    ‖iterate d N - reference d‖ ≤
      contraction d h₀ ^ N * initialError d +
        residualBudget d h₀ D / (1 - contraction d h₀) := by
  have hs : (∑ j ∈ Finset.range N, contraction d h₀ ^ j) ≤
      1 / (1 - contraction d h₀) := by
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := N)
      (contraction_nonneg d h₀ h) hq
  exact (finite_bound d h₀ h l v hl hv D hreg N).trans (by
    unfold finiteError
    simpa only [div_eq_mul_inv, one_mul, residualBudget] using
      add_le_add (le_refl (contraction d h₀ ^ N * initialError d))
        (mul_le_mul_of_nonneg_left hs
          (norm_nonneg (D.rowError d.G d.r d.sigma h₀))))

/-- Literal raw common-seed iterate error, not a new sampler or a law assertion. -/
theorem raw_finite_bound (N : ℕ) (i : d.G.MeanNode) :
    ∃ he : MemLp (fun ω => rawIterate d N i ω - rawReference d i ω) 2 (seedMeasure d),
      ‖he.toLp (fun ω => rawIterate d N i ω - rawReference d i ω)‖ ≤
        finiteError d h₀ D N := by
  refine ⟨raw_error_memLp d N i, ?_⟩
  rw [AffineResidual.toLp_eq_of_ae _ (raw_error_ae d N i)]
  exact (norm_le_pi_norm (iterate d N - reference d) i).trans
    (finite_bound d h₀ h l v hl hv D hreg N)

/-- The finite L², literal raw, and conditional geometric conclusions together. -/
theorem finite_iteration_bound (N : ℕ) :
    ‖iterate d N - reference d‖ ≤ finiteError d h₀ D N ∧
    (∀ i, ∃ he : MemLp (fun ω => rawIterate d N i ω - rawReference d i ω)
        2 (seedMeasure d),
      ‖he.toLp (fun ω => rawIterate d N i ω - rawReference d i ω)‖ ≤
        finiteError d h₀ D N) ∧
    (contraction d h₀ < 1 → ‖iterate d N - reference d‖ ≤
      contraction d h₀ ^ N * initialError d +
        residualBudget d h₀ D / (1 - contraction d h₀)) :=
  ⟨finite_bound d h₀ h l v hl hv D hreg N,
    raw_finite_bound d h₀ h l v hl hv D hreg N,
    geometric_bound d h₀ h l v hl hv D hreg N⟩
end Error

section ReferenceOutput
variable (d : Data ι m) (hm : 2 ≤ m) (l v : ℝ)
  (D : AffineResidual.Mean.DerivativeBudget d.G)
  (hreg : AffineResidual.Mean.Regularity d.G (curvesWithSmoothBranches d)
    (operator d) 0 d.r l v D)
include hm hreg

/-- The smooth receiver gives the original final mean row's centering defect.
This step uses only the center fields of the explicitly supplied full record;
it does not need a contraction or a backward-mesh bound. -/
theorem reference_output_bound :
    ‖d.G.meanOutput d.sigma (initialScore d)
      ((lpGraph d).collect (operator d) (reference d)) - terminalTarget d‖ ≤
        2 * D.center / (m.factorial : ℝ) := by
  have hb := AffineResidual.Mean.meanFinalResidual d.G hm d.r d.sigma d.hr d.hsigma
    (operator d) 0 (initialPosition d) (initialScore d) (initialNoise d)
    (curvesWithSmoothBranches d) D.center hreg.center_nonneg
    (smoothBranches_canonical_equations d) hreg.center_smooth hreg.center_bound
  have hout : d.G.meanOutput d.sigma (initialScore d)
      ((lpGraph d).collect (operator d)
        ((curvesWithSmoothBranches d).reference d.G 0 d.r)) =
      d.G.meanOutput d.sigma (initialScore d)
        ((lpGraph d).collect (operator d) (reference d)) :=
    smoothBranches_meanOutput_eq d (operator d)
  change ‖d.G.meanOutput d.sigma (initialScore d)
    ((lpGraph d).collect (operator d)
      ((curvesWithSmoothBranches d).reference d.G 0 d.r)) -
    (operator d 0 d.r + (d.sigma / 2) • scoreLp d 1)‖ ≤ _ at hb
  rw [hout] at hb
  have ho : operator d 0 d.r = offsetLp d :=
    MeanResidualBridge.offset_eq d _ (primitiveLp_spec _ _)
  rw [ho] at hb
  exact hb
end ReferenceOutput

section Final
variable (d : Data ι m) (h₀ : ℝ) (h : MeshConditions d h₀)
  (l v : ℝ) (hl : l < 0) (hv : backwardEnd d.G.R < v)
  (D : AffineResidual.Mean.DerivativeBudget d.G)
  (hreg : AffineResidual.Mean.Regularity d.G (curvesWithSmoothBranches d)
    (operator d) 0 d.r l v D)
include h hl hv hreg

/-- The original finite output, with its explicit full centering defect. -/
theorem final_bound (N : ℕ) :
    ‖output d N - terminalTarget d‖ ≤
      d.ell * finiteError d h₀ D N + 2 * D.center / (m.factorial : ℝ) := by
  let R := d.G.meanOutput d.sigma (initialScore d)
    ((lpGraph d).collect (operator d) (reference d))
  have htri : ‖output d N - terminalTarget d‖ ≤
      ‖output d N - R‖ + ‖R - terminalTarget d‖ := by
    simpa only [dist_eq_norm] using dist_triangle (output d N) R (terminalTarget d)
  exact htri.trans (add_le_add
    ((output_lipschitz d (by have hm := h.order; omega) (iterate d N) (reference d)).trans
      (mul_le_mul_of_nonneg_left (finite_bound d h₀ h l v hl hv D hreg N) d.hell))
    (reference_output_bound d h.order l v D hreg))

/-- The final bound on the same raw output and raw stationary-score benchmark. -/
theorem raw_final_bound (N : ℕ) :
    ∃ he : MemLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω) 2 (seedMeasure d),
      ‖he.toLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω)‖ ≤
        d.ell * finiteError d h₀ D N + 2 * D.center / (m.factorial : ℝ) := by
  have he : (fun ω => rawOutput d N ω - rawTerminalTarget d ω) =ᵐ[seedMeasure d]
      ((output d N - terminalTarget d : H d) : Seed d → E) := by
    filter_upwards [rawOutput_ae d N, rawTerminalTarget_ae d,
      Lp.coeFn_sub (output d N) (terminalTarget d)] with ω ho ht hs
    simpa only [ho, ht, Pi.sub_apply] using hs.symm
  let hm := (Lp.memLp (output d N - terminalTarget d)).ae_eq he.symm
  refine ⟨hm, ?_⟩
  rw [AffineResidual.toLp_eq_of_ae hm he]
  exact final_bound d h₀ h l v hl hv D hreg N

/-- Both final-output realizations; no regularity is moved to a clamped curve. -/
theorem final_output_bound (N : ℕ) :
    ‖output d N - terminalTarget d‖ ≤
      d.ell * finiteError d h₀ D N + 2 * D.center / (m.factorial : ℝ) ∧
    ∃ he : MemLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω) 2 (seedMeasure d),
      ‖he.toLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω)‖ ≤
        d.ell * finiteError d h₀ D N + 2 * D.center / (m.factorial : ℝ) :=
  ⟨final_bound d h₀ h l v hl hv D hreg N,
    raw_final_bound d h₀ h l v hl hv D hreg N⟩
end Final

end AcceleratedLogConcave.Numerics.MeanSmoothCollocationLp
