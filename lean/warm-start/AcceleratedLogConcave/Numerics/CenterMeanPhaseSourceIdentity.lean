import AcceleratedLogConcave.Numerics.CenterMeanPhaseVelocityJoin
import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoefficients

/-! Literal positive-order source identification. Primitive smoothness is a
qualitative supplier interface; no moment or quantitative derivative budget is
assumed here. The original-data supplier is joined separately. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.PhaseExpression Tensor.CoordinateReduction
open Tensor.PhaseGeneratorIdentification Tensor.PhaseSourceJetInduction
variable {D : ℕ}
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "ep" => EuclideanSpace.basisFun (Fin (D+D)) ℝ

private theorem coordinateDirection_eq_basis : coordinateDirection (D+D) = ep := by
  funext i
  simp [coordinateDirection,EuclideanSpace.basisFun_apply,EuclideanSpace.single]

private theorem phaseOrbit_normalized_ode (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s) (z : EP) (t : ℝ) :
    HasDerivAt (phaseOrbit d s hs z)
      ((L/s) • SkewCoordinateGenerator.velocity (coordinateDirection (D+D))
        (transportEntry (phaseCoefficients d L a)) (phasePotential d)
        (phaseOrbit d s hs z t)) t := by
  have h := hasDerivAt_phaseOrbit d s hs z t
  rw [phaseVelocity_eq_normalized_generator d L s hL (ne_of_gt hs)] at h
  have he : transportEntry (phaseCoefficients d L a) = phaseTransportEntry d L :=
    funext fun i => funext fun j => phaseCoefficients_transport d L a i j
  simpa only [coordinateDirection_eq_basis,he] using h

theorem iteratedDeriv_phaseObservable_eq_jet (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s)
    (hρ : ∀ c v, ContDiff ℝ ∞ (fun x => phaseCoefficients d L a c x v))
    (z : EP) (i : Fin (D+D)) (k : ℕ) :
    iteratedDeriv (k+1) (fun t => phaseObservable d a (phaseOrbit d s hs z t) i) =
      fun t => (L/s)^(k+1) * sectionValue (phaseCoefficients d L a)
        (phasePotential d) (jet F k) ![i] (phaseOrbit d s hs z t) := by
  have hψ : ContDiff ℝ ∞ (fun x => phaseObservable d a x i) := by
    simpa only [EuclideanSpace.basisFun_inner] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : EP => ep i)).inner ℝ
        (smooth_phaseObservable d a)
  exact iteratedDeriv_eq_jet (phaseCoefficients d L a) (phasePotential d)
    (fun x => phaseObservable d a x i) hρ (smooth_phasePotential d) hψ
    (fun x j k => phaseTransportEntry_skew d L x j k) F i
    (phaseCoefficients_observable_gradient d L a i) (phaseOrbit d s hs z) (L/s)
    (phaseOrbit_normalized_ode d L a s hL hs z) k

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
