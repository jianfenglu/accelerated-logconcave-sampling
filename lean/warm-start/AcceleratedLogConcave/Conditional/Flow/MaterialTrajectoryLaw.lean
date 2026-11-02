import AcceleratedLogConcave.Conditional.Flow.ExtendedAgreement
import AcceleratedLogConcave.Conditional.Stein.TransportLaw

noncomputable section
open Set MeasureTheory
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis.PositiveVarianceSlab OAI.LogConcaveSampling.GlobalODE
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

theorem state_fst_eq_source {t : ℝ} (ht : t ∈ Icc 0 d.b)
    (y : EuclideanSpace ℝ (Fin D)) :
    (d.state t y).fst = backwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t y := by
  change flow d.lipschitz_clippedVelocity d.continuous_clippedVelocity d.reference y t = _
  rw [backwardProbabilityTransport_eq_flow,projIcc_of_mem d.hb0 ht]
  exact d.flow_eq_source ⟨d.b,d.hb0,le_rfl⟩ ⟨t,ht⟩ y

theorem state_fst_measurePreserving {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    MeasurePreserving (fun y => (d.state t y).fst)
      (interpolationLaw d.F d.x d.r d.b) (interpolationLaw d.F d.x d.r t) := by
  have hf := forwardProbabilityTransport_measurePreserving d.hF d.hell d.hlo d.hhi
    d.x d.hr d.hb0 d.hb1 ht
  have hb := MeasurePreserving.symm
    (forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t).toMeasurableEquiv hf
  have he : (fun y => (d.state t y).fst) =
      (backwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t : _ → _) :=
    funext (d.state_fst_eq_source ht)
  rw [he]
  exact hb

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
