import AcceleratedLogConcave.Conditional.Flow.ActualJacobianWords
import AcceleratedLogConcave.Conditional.Flow.ExtendedGaussianMoment
import AcceleratedLogConcave.Numerics.SmoothKernelJets

/-! Exact quantitative join: the actual common-seed kernel's derivative norm
is the spatial Hilbert--Schmidt second moment of its actual ordered Jacobian
words. No B/C identities, independence or integrability are new assumptions.
The remaining sharp whole-expression moment estimate is not asserted here. -/
noncomputable section
open Set MeasureTheory
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Analysis.PositiveVarianceSlab
open Conditional.PositiveVarianceFlowData
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def actualJacobianWordSum (d : MeanFlowLp.Data ι m) (n : ℕ) (t : ℝ) (y : E) : E →L[ℝ] E :=
  let sd := KernelFlowLp.smoothData (kernelData d)
  sd.jacobian t y * Analysis.OrderedJacobianWords.evaluateSum
    (fun k u => sd.jacobianCoefficientJet k u y)
    (Analysis.OrderedJacobianWords.words n) t

omit [DecidableEq ι] in
/-- The actual B factor has an explicit dimension-free source constant.
The sharper exp(1/2) bound implies the manuscript's exp(1). -/
theorem norm_actualJacobian_le (d : MeanFlowLp.Data ι m) (t : ℝ) (y : E) :
    ‖(KernelFlowLp.smoothData (kernelData d)).jacobian t y‖ ≤ Real.exp (1/2 : ℝ) := by
  apply ((KernelFlowLp.smoothData (kernelData d)).norm_jacobian_le t y).trans
  apply Real.exp_le_exp.mpr
  exact (kernelData d).hsmall

omit [DecidableEq ι] in
/-- All orders, including order zero, identify the exact existing state jet. -/
theorem actualJacobianWordSum_eq_stateJet (d : MeanFlowLp.Data ι m) (n : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) (y : E) :
    actualJacobianWordSum d n t y =
      ((KernelFlowLp.smoothData (kernelData d)).jet n t y).snd := by
  exact ((KernelFlowLp.smoothData (kernelData d)).stateJet_snd_eq_words n
    (source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht) y).symm

/-- Positive kernel derivatives remove the reference subtraction; the
common-seed map is an isometry and Gaussian contraction is exact. -/
theorem norm_sq_iteratedDeriv_smoothKernel_eq_words (d : MeanFlowLp.Data ι m)
    (j : Fin m) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖iteratedDeriv (n+1) (smoothKernel d j) t‖ ^ 2 =
      ∫ y : E, ∑ i : Fin (Module.finrank ℝ E),
        ‖actualJacobianWordSum d (n+1) t y ((stdOrthonormalBasis ℝ E) i)‖ ^ 2
        ∂Conditional.interpolationLaw (kernelData d).F (kernelData d).x
          (kernelData d).r (kernelData d).b := by
  rw [norm_iteratedDeriv_smoothKernel_source d j n ht, momentumJetLp,
    Analysis.DominatedLp.norm_sq_toLp]
  rw [(KernelFlowLp.smoothData (kernelData d)).integral_momentumJet_norm_sq]
  apply integral_congr_ae
  filter_upwards [] with y
  apply Finset.sum_congr rfl
  intro i _
  rw [actualJacobianWordSum_eq_stateJet d (n+1) ht y]

end AcceleratedLogConcave.Numerics.MeanResidualBridge
