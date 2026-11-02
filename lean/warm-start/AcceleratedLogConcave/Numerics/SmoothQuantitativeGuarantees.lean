import AcceleratedLogConcave.Numerics.SmoothQuantitativeAssembly
import AcceleratedLogConcave.Numerics.SmoothQuantitativeError

/-!
# Numerical guarantees from the two remaining actual-source interfaces

These statements specialize the quantitative smooth-receiver bounds to the
original-data budget. Their only analytic inputs are `VelocityBounds d` and
`AngleBounds d`; the mesh and strict contraction are numerical conditions.
They concern the unchanged common-seed collocation output and its original
stationary-score benchmark.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.AffineGraph
open Numerics.AffineGraph.MeanGeometry Numerics.MeanCollocationLp
open scoped BigOperators
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.SmoothQuantitativeGuarantees
open SmoothQuantitativeAssembly Analysis.PositiveVarianceSlab
variable {D m : ℕ}

/-- The strict contraction requirement is exactly this scalar numerical
smallness condition for the original graph and mesh step. -/
theorem contraction_lt_one_iff (d : Data (Fin D) m) (h₀ : ℝ) :
    contraction d h₀ < 1 ↔
      d.ell * (256 * (m : ℝ) ^ 5 * d.r / (d.sigma * d.G.psi * h₀) +
        4 * d.r ^ 2) < 1 := Iff.rfl

/-- The geometric denominator is positive whenever the stated numerical
smallness condition holds. -/
theorem denominator_positive (d : Data (Fin D) m) (h₀ : ℝ)
    (hq : contraction d h₀ < 1) : 0 < 1 - contraction d h₀ :=
  sub_pos.mpr hq

variable (d : Data (Fin D) m) (h₀ : ℝ) (hmesh : MeshConditions d h₀)
  (hvelocity : VelocityBounds d) (hangle : AngleBounds d)
include hmesh hvelocity hangle

/-- Geometric final error, with iteration, actual row residual and the full
centering defect separately visible. -/
theorem geometric_output_bound (N : ℕ) (hq : contraction d h₀ < 1) :
    ‖output d N - terminalTarget d‖ ≤
      d.ell * (contraction d h₀ ^ N * initialError d) +
      d.ell * (residualBudget d h₀ (budget d) / (1 - contraction d h₀)) +
      2 * (budget d).center / (m.factorial : ℝ) := by
  have hm : 1 ≤ m := by have := hmesh.order; omega
  exact SmoothQuantitativeError.geometric_final_bound d h₀ hmesh
    (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))
    (left_margin d) (right_margin d) (budget d)
    (regularity d hm hvelocity hangle) N hq

/-- The geometric estimate for the literal raw output on the common seed. -/
theorem geometric_raw_output_bound (N : ℕ) (hq : contraction d h₀ < 1) :
    ∃ he : MemLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω)
        2 (seedMeasure d),
      ‖he.toLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω)‖ ≤
        d.ell * (contraction d h₀ ^ N * initialError d) +
        d.ell * (residualBudget d h₀ (budget d) / (1 - contraction d h₀)) +
        2 * (budget d).center / (m.factorial : ℝ) := by
  have hm : 1 ≤ m := by have := hmesh.order; omega
  exact SmoothQuantitativeError.raw_output_error_le d h₀ hmesh
    (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))
    (left_margin d) (right_margin d) (budget d)
    (regularity d hm hvelocity hangle) N hq
    (d.ell * (contraction d h₀ ^ N * initialError d) +
      d.ell * (residualBudget d h₀ (budget d) / (1 - contraction d h₀)) +
      2 * (budget d).center / (m.factorial : ℝ))
    (d.ell * (contraction d h₀ ^ N * initialError d))
    (d.ell * (residualBudget d h₀ (budget d) / (1 - contraction d h₀)))
    (2 * (budget d).center / (m.factorial : ℝ))
    le_rfl le_rfl le_rfl le_rfl

/-- An epsilon certificate for the actual L² output. Each allocation is
separately checkable, including the complete centering contribution. -/
theorem output_error_le (N : ℕ) (hq : contraction d h₀ < 1)
    (ε εiteration εquadrature εcentering : ℝ)
    (hiteration : d.ell * (contraction d h₀ ^ N * initialError d) ≤ εiteration)
    (hquadrature : d.ell * (residualBudget d h₀ (budget d) /
      (1 - contraction d h₀)) ≤ εquadrature)
    (hcentering : 2 * (budget d).center / (m.factorial : ℝ) ≤ εcentering)
    (htotal : εiteration + εquadrature + εcentering ≤ ε) :
    ‖output d N - terminalTarget d‖ ≤ ε := by
  have hm : 1 ≤ m := by have := hmesh.order; omega
  exact SmoothQuantitativeError.output_error_le d h₀ hmesh
    (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))
    (left_margin d) (right_margin d) (budget d)
    (regularity d hm hvelocity hangle) N hq
    ε εiteration εquadrature εcentering
    hiteration hquadrature hcentering htotal

/-- The same epsilon certificate for the literal raw common-seed output. -/
theorem raw_output_error_le (N : ℕ) (hq : contraction d h₀ < 1)
    (ε εiteration εquadrature εcentering : ℝ)
    (hiteration : d.ell * (contraction d h₀ ^ N * initialError d) ≤ εiteration)
    (hquadrature : d.ell * (residualBudget d h₀ (budget d) /
      (1 - contraction d h₀)) ≤ εquadrature)
    (hcentering : 2 * (budget d).center / (m.factorial : ℝ) ≤ εcentering)
    (htotal : εiteration + εquadrature + εcentering ≤ ε) :
    ∃ he : MemLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω)
        2 (seedMeasure d),
      ‖he.toLp (fun ω => rawOutput d N ω - rawTerminalTarget d ω)‖ ≤ ε := by
  have hm : 1 ≤ m := by have := hmesh.order; omega
  exact SmoothQuantitativeError.raw_output_error_le d h₀ hmesh
    (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))
    (left_margin d) (right_margin d) (budget d)
    (regularity d hm hvelocity hangle) N hq
    ε εiteration εquadrature εcentering
    hiteration hquadrature hcentering htotal

end AcceleratedLogConcave.Numerics.SmoothQuantitativeGuarantees
