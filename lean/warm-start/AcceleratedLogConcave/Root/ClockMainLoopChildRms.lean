import AcceleratedLogConcave.Root.ClockMainChildRms
import AcceleratedLogConcave.Root.ClockMainErrorHistory

/-! Closed main-child L2 payments on the final actual main-loop law. Every
later reference extension preserves the earlier full source error. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockMainLoopChildRms
open Oracle Oracle.TapeLowering Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open ClockChronologicalCoupling ClockNoisyLayer ClockMainErrorTransport ClockMainErrorHistory
open OuterRootFlowIdentification
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "Hlo" => lower_nonneg hm hlo
local notation "sigma" => CovarianceSetup.sigma (N P) (rhoC P) (a P)
local notation "amp" => 4*sigma*P.delta^(P.K:ℝ)
local instance center_probability : IsProbabilityMeasure
    (OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup) := by
  unfold OuterRootExactTapePath.centerLaw
  infer_instance

/-- The actual final main-loop sample pays every earlier main-child error
with the proved source accuracy and genuine 10d center moment. -/
theorem loop_child_error_bound (k : ℕ) (hk : k<P.K+4) (i : Index P) :
    let νInput := (OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup).prod (stdGaussian (Point d))
    let μLoop := kernel P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ∘ₘ
      νInput.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))
    ∃ hmem : MemLp (stageError P hR hc hsmall clock label hV Hlo hup k hk i) 2 μLoop,
      (∫ z,‖stageError P hR hc hsmall clock label hV Hlo hup k hk i z‖^2 ∂μLoop) ≤ amp^2*(10*(d:ℝ)) ∧
      ‖hmem.toLp (stageError P hR hc hsmall clock label hV Hlo hup k hk i)‖ ≤
        Real.sqrt (amp^2*(10*(d:ℝ))) := by
  let νInput := (OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup).prod (stdGaussian (Point d))
  obtain ⟨hmem,hpay⟩ := ClockMainChildRms.averaged_main_error_bound
    P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean k hk i
  have hlaw := (loop_error_law P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean νInput k hk i).trans
    (stage_error_law P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean νInput k hk i)
  have hmeas := stageError_measurable P hR hc hsmall clock label hK hC hy hV Hlo hup k hk i
  have hlower := lowerError_measurable P hR hc hsmall clock hV Hlo hup i
  obtain ⟨hactual,heq⟩ := PrivateCompletedRms.memLp_integral_of_law _ _ _ _ hmeas hlower hlaw hmem
  have hbound := heq.le.trans hpay
  refine ⟨hactual,hbound,?_⟩
  apply FreshChildBatchErrorTransfer.norm_toLp_le_of_square_integral _ _ hactual _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (le_trans (integral_nonneg fun _ => sq_nonneg _) hbound)]
  exact hbound

end AcceleratedLogConcave.Root.ClockMainLoopChildRms
