import AcceleratedLogConcave.Numerics.CenterMeanPhaseCalculus
import AcceleratedLogConcave.Tensor.PhasePolynomialPullback
import AcceleratedLogConcave.Conditional.ScaledJetPolynomial

/-! Exact surviving phase_score_polynomialJets declaration only.
The full Gibbs environment still requires the independent missing moments module. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor.AdjointReduction Tensor.PolynomialClosure
open Conditional.ScaledJetPolynomial Analysis.PositiveVarianceSlab
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem phase_score_polynomialJets (d : Data (Fin D)) (v : EP) :
    HasPolynomialJets (dir v (phasePotential d)) := by
  have ht : d.b ∈ Set.Icc (left d.b) (right d.b) := by
    constructor
    · dsimp [left]; linarith [d.hb, d.hb1]
    · dsimp [right]; linarith [d.hb1]
  have hs := contDiff_interpolationPotential d.hF d.hlo d.hup d.x d.r
    (by linarith [d.hb]) d.hb1
  have hp := (score_direction_polynomialJets d.hF d.hlo d.hup d.hb d.hb1
    d.x d.r ht (phasePosition v)).comp_linear
      (contDiff_dir hs (phasePosition v)) phasePositionCLM
  let L : EP →L[ℝ] ℝ := (innerSL ℝ (phaseMomentum v)).comp phaseMomentumCLM
  have hm : HasPolynomialJets L := (NormJets.clm L).polynomialJets L.contDiff
  have he : dir v (phasePotential d) = fun z =>
      ((dir (phasePosition v) (interpolationPotential d.F d.x d.r d.b)) ∘ phasePositionCLM) z + L z := by
    funext z
    change fderiv ℝ (phasePotential d) z v =
      fderiv ℝ (interpolationPotential d.F d.x d.r d.b) (phasePosition z) (phasePosition v) +
      inner ℝ (phaseMomentum v) (phaseMomentum z)
    rw [fderiv_phasePotential, ← inner_gradient_left,
      gradient_interpolationPotential d.hF d.hlo d.hup d.x d.r (by linarith [d.hb]) d.hb1]
    change inner ℝ (sourceScore d (phasePosition z)) (phasePosition v) +
      inner ℝ (phaseMomentum z) (phaseMomentum v) =
      inner ℝ (sourceScore d (phasePosition z)) (phasePosition v) +
      inner ℝ (phaseMomentum v) (phaseMomentum z)
    rw [real_inner_comm (phaseMomentum z) (phaseMomentum v)]
  rw [he]
  exact hp.add hm ((contDiff_dir hs _).comp phasePositionCLM.contDiff) L.contDiff

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
