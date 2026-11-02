import AcceleratedLogConcave.Analysis.AnglePhysicalBudgets
import AcceleratedLogConcave.Analysis.AnglePhaseJetEnergy
import AcceleratedLogConcave.Analysis.AngleEnergyNormalization

/-! The actual normalized Gaussian jet ladder has a dimension-sharp explicit
budget from literal primitive split budgets. AnglePhysicalBudgets assembles
those budgets conditionally on the separately owed physical flow estimate;
no desired angle derivative norm is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.Ordered.Graph Tensor.PhaseExpression Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

theorem norm_angleSourceJetLp_normalized_le (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a R : ℝ)
    (hR : 0 < R) (hq : 0 < q) (hspeed : q⁻¹/(radius R q)^2 ≤ 2/R^2)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential
      256 (radius R q)) (k : ℕ) (t : ℝ) :
    ‖angleSourceJetLp μ T hT q a 256 (radius R q) (by norm_num)
      (radius_pos hR hq) (radius_le_one R q) hb k t‖ ≤
      Real.sqrt (((D+D : ℕ) : ℝ) * AdjointReduction.PhaseBudget.Q 256 (5*(k+1)+1)) *
        (2/R^2)^(k+1) := by
  have h := norm_angleSourceJetLp_le μ T hT q a 256 (radius R q) (by norm_num)
    (radius_pos hR hq) (radius_le_one R q) hb k t
  rw [(observable_jet_budgets k).1,(observable_jet_budgets k).2] at h
  have hexp : -2*((2*((k : NNReal)+1) : NNReal) : ℝ) = -4*((k+1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hexp] at h
  exact h.trans (scaled_sqrt_energy_le hR hq
    (mul_nonneg (Nat.cast_nonneg _) (AdjointReduction.PhaseBudget.Q_nonneg (by norm_num) _))
    hspeed (k+1))
end AcceleratedLogConcave.Analysis.AnglePhase
