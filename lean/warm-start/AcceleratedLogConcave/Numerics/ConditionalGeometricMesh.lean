import AcceleratedLogConcave.Numerics.ConditionalMeshBudget
import AcceleratedLogConcave.Numerics.ProbabilityGeometricMesh

/-! Concrete conditional schedule. Positivity and the half-step cap are explicit.
Only the numerical mesh is instantiated; the quantitative envelope is still supplied. -/
noncomputable section
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics

/-- Ceiling-balanced probability mesh on the actual conditional interval. -/
def conditionalGeometricInterval (h₀ : ℝ) (hh : 0 < h₀) :
    IntervalMesh 0 conditionalEnd :=
  probabilityGeometricInterval 0 conditionalEnd h₀ conditionalEnd_pos conditionalEnd_lt_one hh

/-- Exact cell-count normalization, including the one-cell ceiling case. -/
theorem conditionalGeometricInterval_cellCount (h₀ : ℝ) (hh : 0 < h₀) :
    (conditionalGeometricInterval h₀ hh).cellsPred + 1 =
      GeometricMesh.cellCount 0 conditionalEnd h₀ :=
  probabilityGeometricInterval_cellCount 0 conditionalEnd h₀ conditionalEnd_pos conditionalEnd_lt_one hh

/-- The prescribed geometric schedule discharges the named conditional step premise. -/
theorem conditionalGeometricInterval_step (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (c : (conditionalGeometricInterval h₀ hh).Cell) :
    (conditionalGeometricInterval h₀ hh).length c ≤
      2*h₀*(1-((conditionalGeometricInterval h₀ hh).right c)^2) :=
  probabilityGeometricInterval_step 0 conditionalEnd h₀ conditionalEnd_pos
    conditionalEnd_lt_one hh hhalf (by norm_num) c

/-- Composed prescribed-mesh budget. `hbudget` remains the quantitative supplier
boundary; this theorem proves no derivative estimate. -/
theorem conditionalGeometricInterval_cellBudget_le (h₀ : ℝ) (hh : 0 < h₀)
    (hhalf : h₀ ≤ 1/2) (m : ℕ)
    (B : (conditionalGeometricInterval h₀ hh).Cell → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hbudget : ∀ c, B c ≤ A/(1-((conditionalGeometricInterval h₀ hh).right c)^2)^m) :
    AffineResidual.cellBudget (conditionalGeometricInterval h₀ hh) m B ≤
      2^(m+1)*conditionalEnd*A*h₀^m/(m.factorial:ℝ) :=
  AffineResidual.conditional_cellBudget_le (conditionalGeometricInterval h₀ hh)
    m B A h₀ hA hh.le (conditionalGeometricInterval_step h₀ hh hhalf) hbudget

/-- On a geometry whose conditional mesh is literally the prescribed partition,
the numerical error estimate is instantiated, still conditional on the envelope. -/
theorem conditionalGeometricInterval_conditionalError_le {m : ℕ} (G : MeanGeometry m)
    (D : AffineResidual.Mean.DerivativeBudget G)
    (r ell Aₘ h₀ : ℝ) (dim : ℕ)
    (hr : 0 ≤ r) (hell : 0 ≤ ell) (hA : 0 ≤ Aₘ)
    (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2) (j : Fin m) (ρ : G.Kernel)
    (hmesh : G.conditional ρ = conditionalGeometricInterval h₀ hh)
    (hbudget : ∀ c, D.conditional j ρ c ≤
      (ell*(r*Real.sqrt (G.variance ρ))*Real.sqrt dim*Aₘ) /
        (1-((G.conditional ρ).right c)^2)^m) :
    D.conditionalError G r j ρ ≤
      2^(m+1)*conditionalEnd*ell*r^2*G.variance ρ*Real.sqrt dim*Aₘ*h₀^m /
        (m.factorial:ℝ) := by
  apply AffineResidual.Mean.DerivativeBudget.conditionalError_le_of_cellEnvelope
    G D r ell Aₘ h₀ dim hr hell hA hh.le j ρ
  · rw [hmesh]
    exact conditionalGeometricInterval_step h₀ hh hhalf
  · exact hbudget

end AcceleratedLogConcave.Numerics
