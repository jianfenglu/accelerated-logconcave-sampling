import AcceleratedLogConcave.Numerics.CenterMeanPhaseJetReceiver
import AcceleratedLogConcave.Numerics.CenterMeanPhaseJetEnergy

/-! Explicit positive-order common-seed budget. Primitive split estimates are
still an unpaid, visible supplier; the final W12 claim cannot be made without them. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Tensor.Ordered.Graph CenterMeanSecondJetSource
variable {D m : ℕ}

def centerSourceBudget (d : Data (Fin D) m) (L a c R : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt D * Real.sqrt (sourceJetEnergyScale L a (d.sigma/2) c R k)

theorem centerSourceBudget_nonneg (d : Data (Fin D) m) (L a c R : ℝ) (k : ℕ) :
    0 ≤ centerSourceBudget d L a c R k :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem norm_iteratedDeriv_centerMeanLp_le_from_primitives (d : Data (Fin D) m)
    (L a : ℝ) (hL : L ≠ 0) (ha : a ≠ 0) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv (k+1) (centerMeanLp d) t‖ ≤ centerSourceBudget d L a c R k := by
  rw [iteratedDeriv_centerMeanLp_from_primitives d L a hL ha hb k]
  have hn : ‖centerMeanSourceJetLp d L a hb k t‖^2 ≤
      (D:ℝ)*sourceJetEnergyScale L a (d.sigma/2) c R k := by
    simpa [centerMeanSourceJetLp,phasePullback] using
      norm_sourceJetLp_sq_le (kernelData d) L a (d.sigma/2) (half_pos d.hsigma)
        hc hR hR1 hb k t
  have he := sourceJetEnergyScale_nonneg L a (d.sigma/2) (le_trans (by norm_num) hc) hR.le k
  have hd := Real.sq_sqrt (Nat.cast_nonneg D : 0 ≤ (D:ℝ))
  have hs := Real.sq_sqrt he
  have hp : (centerSourceBudget d L a c R k)^2 =
      (D:ℝ)*sourceJetEnergyScale L a (d.sigma/2) c R k := by
    unfold centerSourceBudget
    rw [mul_pow,hd,hs]
  have hb0 := centerSourceBudget_nonneg d L a c R k
  nlinarith [sq_nonneg (‖centerMeanSourceJetLp d L a hb k t‖ - centerSourceBudget d L a c R k)]

/-- The three center-only fields needed at a positive collocation order.
No velocity, angle, or other regularity field is asserted here. -/
theorem centerMeanLp_center_fields_from_primitives (d : Data (Fin D) m) (hm : 1 ≤ m)
    (L a : ℝ) (hL : L ≠ 0) (ha : a ≠ 0) {c R : ℝ}
    (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) :
    0 ≤ centerSourceBudget d L a c R (m-1) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ m (centerMeanLp d) t) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedDeriv m (centerMeanLp d) t‖ ≤ centerSourceBudget d L a c R (m-1)) := by
  refine ⟨centerSourceBudget_nonneg d L a c R (m-1), ?_, ?_⟩
  · intro t _
    exact ((centerMeanLp_contDiff_from_primitives d L a hL ha hb).of_le (by simp)).contDiffAt
  · intro t _
    simpa only [Nat.sub_add_cancel hm] using
      norm_iteratedDeriv_centerMeanLp_le_from_primitives d L a hL ha hc hR hR1 hb (m-1) t

end AcceleratedLogConcave.Numerics.MeanFlowLp
