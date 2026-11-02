import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoordinates

/-! NEW reconstruction, source-only pending validation.
The literal complete centering orbit conjugated by the existing phase chart.
No stationarity, ODE, moments, or quantitative estimates are assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

/-- Actual source flow in the Euclidean chart, with time last. -/
def phaseOrbit (d : Data (Fin D)) (s : ℝ) (hs : 0 < s) (z : EP) (t : ℝ) : EP :=
  phaseCoordinateEquiv.symm (phase d s hs t (phaseCoordinateEquiv z))

/-- Signs agree with the upper-right K, lower-left negative-transpose convention. -/
def phaseVelocity (d : Data (Fin D)) (s : ℝ) (z : EP) : EP :=
  phaseCoordinateEquiv.symm (WithLp.toLp 2
    (-s⁻¹ • K d (phasePosition z) (phaseMomentum z),
      s⁻¹ • (M d (phasePosition z) - meanOffset d)))

@[simp] theorem phaseCoordinateEquiv_phaseOrbit (d : Data (Fin D)) (s : ℝ)
    (hs : 0 < s) (z : EP) (t : ℝ) :
    phaseCoordinateEquiv (phaseOrbit d s hs z t) =
      phase d s hs t (phaseCoordinateEquiv z) := by
  simp only [phaseOrbit, LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem phaseOrbit_zero (d : Data (Fin D)) (s : ℝ) (hs : 0 < s) (z : EP) :
    phaseOrbit d s hs z 0 = z := by
  simp only [phaseOrbit, phase_initial, LinearIsometryEquiv.symm_apply_apply]

theorem phasePosition_phaseOrbit (d : Data (Fin D)) (s : ℝ) (hs : 0 < s)
    (z : EP) (t : ℝ) :
    phasePosition (phaseOrbit d s hs z t) = position d s hs t (phaseCoordinateEquiv z) := by
  simp only [phasePosition, phaseCoordinateEquiv_phaseOrbit, position, WithLp.fst]

theorem phaseMomentum_phaseOrbit (d : Data (Fin D)) (s : ℝ) (hs : 0 < s)
    (z : EP) (t : ℝ) :
    phaseMomentum (phaseOrbit d s hs z t) = momentum d s hs t (phaseCoordinateEquiv z) := by
  simp only [phaseMomentum, phaseCoordinateEquiv_phaseOrbit, momentum, WithLp.snd]

/-- Only positive speed s is needed; no nonzero curvature or normalized scale is used. -/
theorem hasDerivAt_phaseOrbit (d : Data (Fin D)) (s : ℝ) (hs : 0 < s)
    (z : EP) (t : ℝ) :
    HasDerivAt (phaseOrbit d s hs z) (phaseVelocity d s (phaseOrbit d s hs z t)) t := by
  have h := Centering.sourceCenteringFlow_deriv d.hF d.hell d.hlo d.hup d.x d.hr d.hb
    d.hb1 d.hsmall hs (phaseCoordinateEquiv z) t
  have hc := phaseCoordinateEquiv.symm.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t h
  convert hc using 1 <;>
    simp only [phaseOrbit, phaseVelocity, phasePosition, phaseMomentum,
    LinearIsometryEquiv.apply_symm_apply, phase, Numerics.KernelFlowLp.centering,
    Centering.velocity, K, M, meanOffset, neg_smul, WithLp.fst, WithLp.snd, Function.comp_def] <;> rfl

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
