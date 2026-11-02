import AcceleratedLogConcave.Root.CoolingSourceDyadicKL

/-! The existing phase/cooling returned-law comparison with its cooling side
filled by the actual public program and the proved original-data local KL.
The phase-side input is explicit; no cooling correctness premise remains. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
namespace AcceleratedLogConcave.Root.CoolingSourceReturnedLaw
open Oracle Numerics Numerics.AffineGraph TapeLowering SourceExecutableTables
open Probability Schedule

variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : MeanSourceScalarAbsorption.threshold P≤P.y)
  {d : ℕ} (V : Point d → ℝ) (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z w,m*‖w‖^2≤fderiv ℝ (fderiv ℝ V) z w w)
  (hup : ∀ z w,fderiv ℝ (fderiv ℝ V) z w w≤‖w‖^2)

include hup in
/-- Actual public cooling supplies every local cooling estimate in the
source returned-law comparison. The two phase kernels can be the separately
constructed exact and implemented phase kernels. -/
theorem implementation_error {ν : Measure (Point d × Point d)} [IsProbabilityMeasure ν]
    {B κ C : ℝ} (hκ : 1≤κ) (hConst : 180≤C)
    (hWarm : L2Warm (Dyadic.phaseReference V (Dyadic.sourceVariance P.delta)) ν B)
    (phase implementedPhase : Kernel (Point d × Point d) (Point d × Point d))
    [IsMarkovKernel phase] [IsMarkovKernel implementedPhase]
    (hphase : phase ∘ₘ Dyadic.phaseReference V (Dyadic.sourceVariance P.delta)=
      Dyadic.phaseReference V (Dyadic.sourceVariance P.delta))
    (N L : ℕ)
    (hphaseKL : (∫⁻ z,klDiv (phase z) (implementedPhase z)
        ∂Dyadic.phaseReference V (Dyadic.sourceVariance P.delta))≤
      ENNReal.ofReal (C*(d:ℝ)*P.delta^(2*P.K-2)/Dyadic.sourceRate κ P.delta)) :
    let hI := Gibbs.integrable_exp_neg_of_hessian_lower hV hm hlo
    let : ∀ j,IsMarkovKernel (CoolingSourceDyadicKL.implemented P hK hc hsmall hC hy V j) :=
      fun j => CoolingSourceDyadicKL.implemented_markov P hK hc hsmall hC hy V hV j
    totalVariationDistance
      (PhaseCooling.returnedLaw ν phase Prod.fst measurable_fst
        (Dyadic.coolingKernel V hV.continuous.measurable hI (Dyadic.sourceVariance P.delta)) N L)
      (PhaseCooling.returnedLaw ν implementedPhase Prod.fst measurable_fst
        (CoolingSourceDyadicKL.implemented P hK hc hsmall hC hy V) N L)≤
      Real.sqrt (B/2*(C*(d:ℝ)*P.delta^(2*P.K-2))*
        ((N:ℝ)/Dyadic.sourceRate κ P.delta+(L:ℝ))) := by
  dsimp only
  let _ : ∀ j,IsMarkovKernel (CoolingSourceDyadicKL.implemented P hK hc hsmall hC hy V j) :=
    fun j => CoolingSourceDyadicKL.implemented_markov P hK hc hsmall hC hy V hV j
  apply Dyadic.source_implementation_error d P.K N L hV.continuous.measurable
    (Gibbs.integrable_exp_neg_of_hessian_lower hV hm hlo) P.delta_pos hκ
    (by linarith : 0≤C) hWarm phase implementedPhase
    (CoolingSourceDyadicKL.implemented P hK hc hsmall hC hy V) hphase hphaseKL
  intro j _
  refine (CoolingSourceDyadicKL.source_KL_le P hK hc hsmall hC hy V hV hm hlo hup j).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hConst (Nat.cast_nonneg d)) (pow_nonneg P.delta_pos.le _)
end AcceleratedLogConcave.Root.CoolingSourceReturnedLaw
