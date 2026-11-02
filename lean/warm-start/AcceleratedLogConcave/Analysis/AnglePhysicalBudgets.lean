import AcceleratedLogConcave.Analysis.AngleGradientCoordinatePadding
import AcceleratedLogConcave.Analysis.AngleGradientBudgetScale
import AcceleratedLogConcave.Analysis.AnglePrimitiveBudgetReduction

/-! Exact quantitative receiver for the separately owed physical displacement
split estimate. No physical flow bound is proved or silently assumed here. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.Ordered.Graph Numerics.CenterMeanSecondJetSource Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

theorem anglePrimitiveBudgets_of_physicalSplits (T : E → E) (hT : ContDiff ℝ ∞ T)
    (R q l : ℝ) (hR : 0 < R) (hq : 0 < q) (hl : 0 < l)
    (hphysical : ∀ j y (S : Finset (Fin j ⊕ Fin 2)), NontrivialSplit S →
      splitNorm D S (physicalDisplacementJet T j y) ≤
        2*l*(256:ℝ)^(j+1)*((j+1).factorial : ℝ)*R^((1:ℝ)-((j+1:ℕ):ℝ)))
    (M : E) :
    PhasePrimitiveBudgets (angleCoefficients T M q (2*l*R)) gaussianPotential
      256 (radius R q) := by
  apply anglePrimitiveBudgets_of_gradient T M q (2*l*R) (radius R q) (radius_pos hR hq)
  intro j z S hS
  have ha : 0 < 2*l*R := by positivity
  have hc : 0 ≤ (2*l*R)⁻¹*q^(j+1) := by positivity
  have hp := splitNorm_angleGradientJet_le T hT M q (2*l*R) j z S
  rw [abs_of_nonneg hc] at hp
  have hb := hp.trans (mul_le_mul_of_nonneg_left (hphysical j _ S hS) hc)
  have hs := displacement_pullback_budget_le hR hq hl (j+1)
  have hn : (2*l*R)⁻¹*q^(j+1) = q^(j+1)/(2*l*R) := by rw [div_eq_mul_inv,mul_comm]
  rw [hn] at hb
  apply (hb.trans hs).trans_eq
  congr 2 <;> push_cast <;> ring
end AcceleratedLogConcave.Analysis.AnglePhase
