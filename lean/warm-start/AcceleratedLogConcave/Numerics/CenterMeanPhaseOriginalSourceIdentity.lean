import AcceleratedLogConcave.Numerics.CenterMeanPhaseSourceIdentity
import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoefficientSmooth

/-! Original-data source identity, with primitive smoothness discharged rather
than assumed. Quantitative primitive split bounds remain a separate supplier. -/
noncomputable section
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.PhaseExpression Tensor.CoordinateReduction
variable {D : ℕ}
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem originalData_iteratedDeriv_phaseObservable_eq_jet (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s) (z : EP) (i : Fin (D+D)) (k : ℕ) :
    iteratedDeriv (k+1) (fun t => phaseObservable d a (phaseOrbit d s hs z t) i) =
      fun t => (L/s)^(k+1) * sectionValue (phaseCoefficients d L a)
        (phasePotential d) (jet F k) ![i] (phaseOrbit d s hs z t) :=
  iteratedDeriv_phaseObservable_eq_jet d L a s hL hs
    (phaseCoefficients_smooth d L a) z i k

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
