import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoefficients

/-! Genuine original-data primitive smoothness, independent of moment/tail
and quantitative split-budget obligations. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open CenteringFlowLp Tensor.AdjointReduction
variable {D : ℕ}
theorem phaseCoefficients_smooth (d : Data (Fin D)) (ellScale a : ℝ)
    (c : Tensor.PhaseExpression.Primitive) (v : Fin 2 → Fin (D+D)) :
    ContDiff ℝ ∞ (fun z => phaseCoefficients d ellScale a c z v) := by
  cases c with
  | transport => exact smooth_phaseTransportEntry d ellScale (v 0) (v 1)
  | scoreHessian =>
    have h1 : ContDiff ℝ ∞ (fderiv ℝ (phasePotential d)) :=
      (smooth_phasePotential d).fderiv_right (by simp)
    have h : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (phasePotential d))) :=
      h1.fderiv_right (by simp)
    exact (h.clm_apply contDiff_const).clm_apply contDiff_const
  | observableGradient =>
    exact contDiff_dir ((EuclideanSpace.proj (v 0)).contDiff.comp
      (smooth_phaseObservable d a)) _
  | positionProjection =>
    exact contDiff_dir ((EuclideanSpace.proj (v 0)).contDiff.comp
      smooth_phasePaddedPosition) _

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
