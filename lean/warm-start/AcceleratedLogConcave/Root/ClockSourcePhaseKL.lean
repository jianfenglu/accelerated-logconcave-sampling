import AcceleratedLogConcave.Root.ClockPhysicalRmsPayment
import AcceleratedLogConcave.Root.ClockReferencePhaseLaw

/-! The fixed-clock retained phase KL estimate with its original-data root
error paid. The reference is the prescribed reference phase, with the same
original input and both fresh Gaussian blocks. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal
namespace AcceleratedLogConcave.Root.ClockSourcePhaseKL
open Oracle Oracle.TapeLowering Oracle.CanonicalTapeMeasurability
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (clock : ClockLaw.Clock) (label : ℕ)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
  (hyQuad : ClockQuadratureResolution.threshold P.K≤P.y)
local notation "Hlo" => OuterRootFlowIdentification.lower_nonneg hm hlo
local notation "μX" => OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup
local notation "γ" => stdGaussian (Point d)
local notation "ν" => (μX).prod γ
local notation "μ" => ClockCompletedPhaseLaw.law P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ν
local notation "host" => ClockChronologicalCoupling.Host P hR hc hsmall clock label
local notation "Sample" => (ClockChronologicalCoupling.History P d × Tape d host) × (ClockNoisyLayer.Index P→Point d)
local instance center_probability : IsProbabilityMeasure μX := by
  unfold OuterRootExactTapePath.centerLaw
  infer_instance

include hyQuad in
/-- The retained Gaussian-shift cost is paid by the actual full-source root
RMS, with no conditional independence assertion involving original momentum. -/
theorem retained_cost_le {Γ : ℝ} (hΓ : 0<Γ) (hhalf : Γ≤1/2) :
    (∫⁻ z,ENNReal.ofReal (‖ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z-
      ClockCompletedPhaseLaw.actualRoot (V:=V) P hR hc hsmall clock label z‖^2/
        (2*(1-Real.exp (-2*Γ)))) ∂μ)≤
      ENNReal.ofReal (512*(d:ℝ)*(P.delta^P.K)^2/Γ) := by
  obtain ⟨he,_,hb⟩ := ClockPhysicalRmsPayment.source_error_bound P clock hR hc hsmall label hK hC hy
    hV hm hlo hup hyMean hyQuad
  let err := ClockPhysicalRms.actualError P hR hc hsmall clock label hK hC hy hV hm hlo hup
  have hint : Integrable (fun z => ‖err z‖^2) μ := he.integrable_norm_pow (by norm_num)
  have hs (z : Sample) :
      ‖ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z-
        ClockCompletedPhaseLaw.actualRoot (V:=V) P hR hc hsmall clock label z‖=‖err z‖ := norm_sub_rev _ _
  calc
    _ ≤ ∫⁻ z,ENNReal.ofReal (‖err z‖^2/(2*Γ)) ∂μ := by
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      simpa only [hs] using ClockPhaseGaussianKL.refresh_cost_le hΓ hhalf
        (ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z-
          ClockCompletedPhaseLaw.actualRoot (V:=V) P hR hc hsmall clock label z)
    _ = ENNReal.ofReal ((∫ z,‖err z‖^2 ∂μ)/(2*Γ)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hint.div_const (2*Γ))
        (Filter.Eventually.of_forall fun z => div_nonneg (sq_nonneg _) (by positivity)),integral_div]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have heq : (32*Real.sqrt (d:ℝ)*P.delta^P.K)^2/(2*Γ)=512*(d:ℝ)*(P.delta^P.K)^2/Γ := by
        rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg d)]
        ring
      exact (div_le_div_of_nonneg_right hb (by positivity)).trans_eq heq
include hyQuad in
/-- Closed input-retaining phase KL estimate on the actual completed source.
The reference readout has the exact prescribed-frame law established in
`ClockReferencePhaseLaw.reference_phase_law`. -/
theorem completed_phase_KL_paid {Γ : ℝ} (hΓ : 0<Γ) (hhalf : Γ≤1/2) :
    let inp := fun z : Sample => ClockCompletedPhaseLaw.sourceInput P hR hc hsmall clock label
      (ClockCompletedPhaseLaw.original P hR hc hsmall clock label z)
    klDiv (((μ).prod ((γ).prod γ)).map (fun z =>
      (inp z.1,ClockPhaseGaussianKL.phaseOutput P.delta Γ clock (inp z.1).1
        (ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z.1) z.2.1 z.2.2)))
      (ClockCompletedPhaseLaw.implementedLaw P hR hc hsmall clock label ν Γ (gradient V))≤
        ENNReal.ofReal (512*(d:ℝ)*(P.delta^P.K)^2/Γ) := by
  exact (ClockCompletedPhaseLaw.implemented_phase_KL P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ν hΓ).trans
    (retained_cost_le P hR hc hsmall hK hC hy hV hm hlo hup clock label hyMean hyQuad hΓ hhalf)

include hyQuad in
/-- The literal source refresh parameter satisfies the quantitative phase
bound at every clock, including clock zero. -/
theorem source_completed_phase_KL_paid {κ : ℝ} (hκ : 1≤κ) :
    let Γ := ClockFinitePhaseKernel.sourceGamma P κ
    let inp := fun z : Sample => ClockCompletedPhaseLaw.sourceInput P hR hc hsmall clock label
      (ClockCompletedPhaseLaw.original P hR hc hsmall clock label z)
    klDiv (((μ).prod ((γ).prod γ)).map (fun z =>
      (inp z.1,ClockPhaseGaussianKL.phaseOutput P.delta Γ clock (inp z.1).1
        (ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z.1) z.2.1 z.2.2)))
      (ClockCompletedPhaseLaw.implementedLaw P hR hc hsmall clock label ν Γ (gradient V))≤
        ENNReal.ofReal (512*(d:ℝ)*(P.delta^P.K)^2/Γ) := by
  exact completed_phase_KL_paid P hR hc hsmall hK hC hy hV hm hlo hup clock label hyMean hyQuad
    (ClockPhaseGaussianKL.sourceGamma_pos P hκ)
    ((ClockPhaseGaussianKL.sourceGamma_le_delta P hκ).trans
      (FinalMeanScheduledData.delta_half P hK hc hsmall hC hy))

end AcceleratedLogConcave.Root.ClockSourcePhaseKL
