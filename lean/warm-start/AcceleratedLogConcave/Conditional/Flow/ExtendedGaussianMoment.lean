import AcceleratedLogConcave.Analysis.GaussianLinearIsometry
import AcceleratedLogConcave.Conditional.Flow.ExtendedLp

/-! Exact Gaussian contraction for the actual higher material momentum jets.
This is an identity, not a sharp bound on the remaining spatial tensor moment. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => Kinetic.CoupledPhase E
variable (d : PositiveVarianceFlowData E)

/-- The genuine coupled phase law gives the exact spatial Hilbert–Schmidt
moment of each higher material Jacobian jet, with integrability derived from
the existing actual jet supplier, not assumed. -/
theorem integral_momentumJet_norm_sq (d : PositiveVarianceFlowData (EuclideanSpace ℝ ι)) (k : ℕ) (t : ℝ) :
    (∫ z : P, ‖(d.momentumJet (ι := ι) k t z : E)‖ ^ 2 ∂(d.phaseMeasure (ι := ι))) =
      ∫ x : E, ∑ i : Fin (Module.finrank ℝ E), ‖((d.jet k t x).snd ((stdOrthonormalBasis ℝ E) i) : E)‖ ^ 2
        ∂interpolationLaw d.F d.x d.r d.b := by
  let μ : Measure E := interpolationLaw d.F d.x d.r d.b
  let := interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r d.b
  have hm := (d.momentumJet_memLp (ι := ι) k t).norm.integrable_sq
  have hc : Continuous (fun z : P => ‖(d.momentumJet (ι := ι) k t z : E)‖ ^ 2) :=
    (((d.continuous_momentumJet (ι := ι) k).comp (continuous_const.prodMk continuous_id)).norm).pow 2
  change Integrable (fun z : P => ‖(d.momentumJet (ι := ι) k t z : E)‖ ^ 2)
    ((μ.prod (stdGaussian E)).map (WithLp.toLp 2)) at hm
  have hp := (integrable_map_measure hc.aestronglyMeasurable (by fun_prop)).mp hm
  change (∫ z : P, ‖(d.momentumJet (ι := ι) k t z : E)‖ ^ 2
    ∂(μ.prod (stdGaussian E)).map (WithLp.toLp 2)) = _
  rw [integral_map (by fun_prop) hc.aestronglyMeasurable]
  exact Analysis.GaussianLinearIsometry.integral_norm_sq_linear_prod μ
    (stdOrthonormalBasis ℝ E) (fun x => (d.jet k t x).snd) hp

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
