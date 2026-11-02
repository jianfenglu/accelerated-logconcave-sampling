import AcceleratedLogConcave.Numerics.VelocityPhaseJetReceiver
import AcceleratedLogConcave.Numerics.VelocityPhaseJetEnergy

/-! Explicit every-order common-seed budget, conditional on named primitive split
estimates. VelocityOriginalData discharges those estimates from original data. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Tensor.Ordered.Graph CenterMeanSecondJetSource
variable {D m : ℕ}

def velocitySourceBudget (d : Data (Fin D) m) (L c R : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt D * Real.sqrt (velocityJetEnergyScale L (d.sigma/2) c R k)

theorem velocitySourceBudget_nonneg (d : Data (Fin D) m) (L c R : ℝ) (k : ℕ) :
    0 ≤ velocitySourceBudget d L c R k :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem norm_iteratedDeriv_velocityLp_le_from_primitives (d : Data (Fin D) m)
    (L a : ℝ) (hL : L ≠ 0) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (velocityLp d) t‖ ≤ velocitySourceBudget d L c R k := by
  rw [iteratedDeriv_velocityLp_from_primitives d L a hL hb k]
  have hn : ‖velocitySourceJetLp d L a hb k t‖^2 ≤
      (D:ℝ)*velocityJetEnergyScale L (d.sigma/2) c R k := by
    simpa [velocitySourceJetLp,phasePullback] using
      norm_velocityJetLp_sq_le (kernelData d) L a (d.sigma/2) (half_pos d.hsigma)
        hc hR hR1 hb k t
  have he := velocityJetEnergyScale_nonneg L (d.sigma/2) (le_trans (by norm_num) hc) hR.le k
  have hd := Real.sq_sqrt (Nat.cast_nonneg D : 0 ≤ (D:ℝ))
  have hs := Real.sq_sqrt he
  have hp : (velocitySourceBudget d L c R k)^2 =
      (D:ℝ)*velocityJetEnergyScale L (d.sigma/2) c R k := by
    unfold velocitySourceBudget
    rw [mul_pow,hd,hs]
  have hb0 := velocitySourceBudget_nonneg d L c R k
  nlinarith [sq_nonneg (‖velocitySourceJetLp d L a hb k t‖ - velocitySourceBudget d L c R k)]


end AcceleratedLogConcave.Numerics.MeanFlowLp
