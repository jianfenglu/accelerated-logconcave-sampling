import AcceleratedLogConcave.Tensor.MaterialVectorBudget
import AcceleratedLogConcave.Numerics.SmoothBackwardReplacement

noncomputable section
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Analysis.PositiveVarianceSlab
open Tensor.ActualCoefficientIntegrability MeasureTheory Set
variable {D m : ℕ}

/-- Explicit budget for the positive derivative order k+1. -/
def materialBackwardDerivativeBudget (d : MeanFlowLp.Data (Fin D) m) (k : ℕ) : ℝ :=
  (d.ell*d.r) * (3*(3+3*(k:ℝ)+1)^2)^k * Real.sqrt (materialRmsNumeric D (3+3*k))

 theorem smoothBackwardMean_derivative_bound (d : MeanFlowLp.Data (Fin D) m)
    (j : Fin m) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖iteratedDeriv (k+1) (smoothBackwardMean d j) t‖ ≤
      materialBackwardDerivativeBudget d k / (1-t^2)^(k+1) := by
  let sd := backwardSmoothData d
  have hv : 0<1-t^2 := Conditional.conditionalVariance_pos (by linarith [ht.1])
    (by linarith [ht.2,d.G.backwardEnd_lt_one])
  have hM0 : 0≤Real.sqrt (materialRmsNumeric D (3+3*k))/(1-t^2)^(k+1) := by positivity
  have hh := positionJetLp_norm_le_massBudget sd d.hsmall k ht hM0
    (materialMean_expression_moment_variance sd d.hsmall k ht)
  rw [norm_iteratedDeriv_smoothBackwardMean d j (k+1)
    (source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht)]
  have hn := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr d.hr.le)
  convert hn using 1
  dsimp [materialBackwardDerivativeBudget,sd,backwardSmoothData,KernelFlowLp.smoothData,kernelData]
  field_simp [d.hr.ne']

 theorem replacement_backwardMean_derivative_bound (d : MeanFlowLp.Data (Fin D) m)
    (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖iteratedDeriv (k+1) ((curvesWithBackward d).backwardMean d.G U 0 d.r j) t‖ ≤
      materialBackwardDerivativeBudget d k / (1-t^2)^(k+1) := by
  rw [norm_iteratedDeriv_replacement_backwardMean d U hu j (k+1) ht,
    ←norm_iteratedDeriv_smoothBackwardMean d j (k+1)
      (source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht)]
  exact smoothBackwardMean_derivative_bound d j k ht

end AcceleratedLogConcave.Numerics.MeanResidualBridge
