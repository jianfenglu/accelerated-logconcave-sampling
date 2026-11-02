import AcceleratedLogConcave.Numerics.SmoothAllReceiver
import AcceleratedLogConcave.Numerics.MeanCollocationLp

/-! Actual center-mean identification and explicit first-increment estimate.
This is NOT the order-m Regularity supplier: its higher stationary source-jet
moment bound remains open. No derivative norm is used as a numeric budget. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge
open Numerics.AffineGraph Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.CenterMeanSourceModulus
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def actualCenter (d : Data ι m) : ℝ → H d :=
  (curvesWithSmoothBranches d).centerMean d.G (MeanCollocationLp.operator d) 0 d.r

theorem actualCenter_eq (d : Data ι m) (t : ℝ) :
    actualCenter d t = centerMeanLp d t := by
  change (curves d).centerMean d.G (MeanCollocationLp.operator d) 0 d.r t = _
  exact MeanResidualBridge.centerMean_eq d _ (primitiveLp_spec _ _) t

theorem actualCenter_source_eq (d : Data ι m) (t : ℝ) :
    actualCenter d t = phasePullback d
      (CenteringFlowLp.centeredMeanLp (kernelData d)
        (d.sigma / 2) (half_pos d.hsigma) t) + offsetLp d := by
  rw [actualCenter_eq, centerMeanLp_eq]

theorem continuous_actualCenter (d : Data ι m) : Continuous (actualCenter d) := by
  have he : actualCenter d = centerMeanLp d := funext (actualCenter_eq d)
  rw [he]
  exact continuous_centerMeanLp d

/-- Fully explicit, potential-independent Lipschitz coefficient in time.
This controls increments, not the missing order-m derivative. -/
def firstIncrementBudget (d : Data ι m) : ℝ :=
  d.ell * (d.r * backwardEnd d.G.R) *
    ((d.sigma / 2)⁻¹ * CenteringFlowLp.alpha (kernelData d) *
      backwardEnd d.G.R * Real.sqrt (Module.finrank ℝ E))

omit [DecidableEq ι] in
theorem firstIncrementBudget_nonneg (d : Data ι m) :
    0 ≤ firstIncrementBudget d := by
  unfold firstIncrementBudget CenteringFlowLp.alpha kernelData
  have := d.hell
  have := d.hr
  have := d.hsigma
  have := d.G.backwardEnd_pos
  positivity

theorem norm_position_increment_le (d : Data ι m) (a b : ℝ) :
    ‖positionLp d b - positionLp d a‖ ≤
      |b-a| * ((d.sigma / 2)⁻¹ * CenteringFlowLp.alpha (kernelData d) *
        backwardEnd d.G.R * Real.sqrt (Module.finrank ℝ E)) := by
  rw [positionLp_eq, positionLp_eq, ← map_sub]
  have hn (z : Lp E 2 (KernelFlowLp.seedMeasure (kernelData d))) :
      ‖phasePullback d z‖ = ‖z‖ :=
    Lp.norm_compMeasurePreserving z (phase_projection_preserving d)
  rw [hn]
  exact CenteringFlowLp.norm_positionLp_sub_le (kernelData d)
    (d.sigma / 2) (half_pos d.hsigma) a b

theorem norm_actualCenter_increment_le (d : Data ι m) (a b : ℝ) :
    ‖actualCenter d b - actualCenter d a‖ ≤ |b-a| * firstIncrementBudget d := by
  have hb : 0 ≤ d.r * backwardEnd d.G.R :=
    mul_nonneg d.hr.le d.G.backwardEnd_pos.le
  have h := (primitiveLp_lipschitz (primitiveData d) (seedMeasure d)
    (mul_pos d.hr d.G.R_pos)).norm_sub_le
      ((d.r * backwardEnd d.G.R) • positionLp d b)
      ((d.r * backwardEnd d.G.R) • positionLp d a)
  have h0 : ‖actualCenter d b - actualCenter d a‖ ≤
      d.ell * ‖(d.r * backwardEnd d.G.R) • positionLp d b -
        (d.r * backwardEnd d.G.R) • positionLp d a‖ := by
    simp only [actualCenter, AffineResidual.Mean.Curves.centerMean, zero_add]
    exact h
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb] at h0
  calc
    _ ≤ d.ell * ((d.r * backwardEnd d.G.R) *
      ‖positionLp d b - positionLp d a‖) := h0
    _ ≤ d.ell * ((d.r * backwardEnd d.G.R) *
      (|b-a| * ((d.sigma / 2)⁻¹ * CenteringFlowLp.alpha (kernelData d) *
        backwardEnd d.G.R * Real.sqrt (Module.finrank ℝ E)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_position_increment_le d a b) hb) d.hell
    _ = |b-a| * firstIncrementBudget d := by unfold firstIncrementBudget; ring

end AcceleratedLogConcave.Numerics.CenterMeanSourceModulus
