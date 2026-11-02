import AcceleratedLogConcave.Numerics.ProbabilityMeshBudget

/-!
# Conditional mesh budget cancellation

The conditional step condition is an explicit geometric premise, not a consequence
of original Data or the backward-only MeshConditions. The cell envelope remains
an explicit quantitative supplier boundary. No derivative estimate is asserted.
-/
noncomputable section
open scoped BigOperators
open Set
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.AffineResidual

/-- A named mesh hypothesis is essential: arbitrary conditional meshes do not
satisfy this estimate. The envelope B may be supplied independently of regularity. -/
theorem conditional_cellBudget_le (M : IntervalMesh 0 conditionalEnd) (m : ℕ)
    (B : M.Cell → ℝ) (A h₀ : ℝ) (hA : 0 ≤ A) (_hh : 0 ≤ h₀)
    (hstep : ∀ c, M.length c ≤ 2*h₀*(1-(M.right c)^2))
    (hbudget : ∀ c, B c ≤ A/(1-(M.right c)^2)^m) :
    cellBudget M m B ≤
      2^(m+1)*conditionalEnd*A*h₀^m/(m.factorial:ℝ) := by
  simpa only [sub_zero] using probability_cellBudget_le M (by norm_num)
    conditionalEnd_lt_one m B A h₀ hA _hh hstep hbudget

namespace Mean.DerivativeBudget
variable {m : ℕ} (G : MeanGeometry m) (D : Mean.DerivativeBudget G)

/-- Exact local-radius factor, with no mesh or analytic assumption. -/
theorem conditionalError_eq_localRadius (r : ℝ) (j : Fin m) (ρ : G.Kernel) :
    D.conditionalError G r j ρ =
      (r * Real.sqrt (G.variance ρ)) * cellBudget (G.conditional ρ) m
        (D.conditional j ρ) := rfl

/-- Numerical wrapper only. `hbudget` is the explicit unpaid quantitative
conditional supplier; `hstep` is an independent conditional mesh choice. -/
theorem conditionalError_le_of_cellEnvelope (r ell Aₘ h₀ : ℝ) (dim : ℕ)
    (hr : 0 ≤ r) (hell : 0 ≤ ell) (hA : 0 ≤ Aₘ) (hh : 0 ≤ h₀)
    (j : Fin m) (ρ : G.Kernel)
    (hstep : ∀ c, (G.conditional ρ).length c ≤
      2*h₀*(1-((G.conditional ρ).right c)^2))
    (hbudget : ∀ c, D.conditional j ρ c ≤
      (ell*(r*Real.sqrt (G.variance ρ))*Real.sqrt dim*Aₘ) /
        (1-((G.conditional ρ).right c)^2)^m) :
    D.conditionalError G r j ρ ≤
      2^(m+1)*conditionalEnd*ell*r^2*G.variance ρ*Real.sqrt dim*Aₘ*h₀^m /
        (m.factorial:ℝ) := by
  have hb := conditional_cellBudget_le (G.conditional ρ) m (D.conditional j ρ)
    (ell*(r*Real.sqrt (G.variance ρ))*Real.sqrt dim*Aₘ) h₀
    (by positivity) hh hstep hbudget
  rw [conditionalError_eq_localRadius]
  calc
    _ ≤ (r * Real.sqrt (G.variance ρ)) *
        (2^(m+1)*conditionalEnd*(ell*(r*Real.sqrt (G.variance ρ))*Real.sqrt dim*Aₘ)*
          h₀^m/(m.factorial:ℝ)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      have hv := Real.sq_sqrt (G.variance_pos ρ).le
      calc
        _ = 2^(m+1)*conditionalEnd*ell*r^2*(Real.sqrt (G.variance ρ))^2*
            Real.sqrt dim*Aₘ*h₀^m/(m.factorial:ℝ) := by ring
        _ = _ := by rw [hv]
end Mean.DerivativeBudget
end AcceleratedLogConcave.Numerics.AffineResidual
