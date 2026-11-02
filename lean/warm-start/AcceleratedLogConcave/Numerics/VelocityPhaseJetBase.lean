import AcceleratedLogConcave.Numerics.VelocityPhaseJetLp
import AcceleratedLogConcave.Numerics.CenterMeanPhaseJetBase

/-! Exact whole-function identification with the physical position velocity. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Tensor.CoordinateReduction Tensor.Ordered.Graph
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "P" => WithLp 2 (E × E)
local notation "ep" => EuclideanSpace.basisFun (Fin (D+D)) ℝ

theorem hasDerivAt_position_velocityJet (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s) (z : P) (t : ℝ) :
    HasDerivAt (fun u => position d s hs u z)
      (seedVelocityJet d L a s 0 (phase d s hs t z)) t := by
  have hΨ (i : Fin (D+D)) : ContDiff ℝ ∞ (fun x => phasePaddedPosition x i) := by
    simpa only [EuclideanSpace.basisFun_inner] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : EP => ep i)).inner ℝ smooth_phasePaddedPosition
  have hv := hasDerivAt_sourceVector_along (phaseCoefficients d L a) (phasePotential d)
    phasePaddedPosition (phaseCoefficients_smooth d L a) hΨ
    (fun x i j => phaseTransportEntry_skew d L x i j) Tensor.PhaseExpression.P
    (phaseCoefficients_position_gradient d L a)
    (hasDerivAt_phaseOrbit_generator d L a s hL hs (phaseCoordinateEquiv.symm z) t)
  have hp := phasePositionCLM.hasFDerivAt.comp_hasDerivAt t hv
  convert hp using 1
  · funext u
    simp [phasePaddedPosition,phaseOrbit,phasePosition,position]
  · simp [seedVelocityJet,phaseVelocityJet,phaseOrbit,jet,map_smul]

theorem velocityJetLp_zero_eq (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R)
    (t : ℝ) : velocityJetLp d L a s hs hb 0 t = -s⁻¹ • kernelLp d s hs t := by
  have h := CenterMeanStationaryLp.hasDerivAt_orbit_of_source d s hs
    (fun z : P => z.fst) (seedVelocityJet d L a s 0)
    (position_initial_memLp d) (seedVelocityJet_memLp d L a s hb 0)
    (seedVelocityJet_contDiff d L a s 0).continuous
    (fun u z => hasDerivAt_position_velocityJet d L a s hL hs z u) t
  exact h.unique (hasDerivAt_positionLp d s hs t)

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
