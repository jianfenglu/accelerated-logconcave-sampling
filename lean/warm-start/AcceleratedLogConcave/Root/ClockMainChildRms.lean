import AcceleratedLogConcave.Root.ClockMainErrorTransport
import AcceleratedLogConcave.Root.ClockCenterMoment
import AcceleratedLogConcave.Oracle.PrivateCompletedRms

/-! Concrete main-child L2 payments for the literal Clock loop. Accuracy of
the same recursive lower kernels and original stationary moments are proved
suppliers, not input certificates. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockMainChildRms
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.TailOccurrenceCut Oracle.PrivateCausalLayer
open TailCut Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockChronologicalCoupling ClockChronologicalLowerProjection ClockNoisyLayer
open ClockMainErrorTransport OuterRootFlowIdentification
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
local notation "pot" => scaledPotential V (Real.sqrt P.delta)
local notation "sigma" => CovarianceSetup.sigma (N P) (rhoC P) (a P)
local notation "amp" => 4*sigma*P.delta^(P.K:ℝ)
local notation "μ" => ClockCenterMoment.baseLaw P hV hm hlo hup

local instance center_probability : IsProbabilityMeasure
    (OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup) := by
  unfold OuterRootExactTapePath.centerLaw
  infer_instance

/-- Exact same lower joint, averaged at the true root-flow benchmark center.
Its variable primitive scale costs at most 10d under the actual coarse law. -/
theorem averaged_main_error_bound (k : ℕ) (hk : k<P.K+4) (i : Index P) :
    MemLp (lowerError P hR hc hsmall clock hV Hlo hup i) 2
      (μ ⊗ₘ ((lower P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk)).joint i).comap
        (center P clock hV Hlo hup i) (center_measurable P clock hV Hlo hup i)) ∧
    (∫ z,‖lowerError P hR hc hsmall clock hV Hlo hup i z‖^2
      ∂μ ⊗ₘ ((lower P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk)).joint i).comap
        (center P clock hV Hlo hup i) (center_measurable P clock hV Hlo hup i)) ≤ amp^2*(10*(d:ℝ)) := by
  let B := data P hR hc hsmall clock label hK hC hy (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk)
  let J := lower P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk)
  have hf : MeanStandaloneLowerErrorBound.Fiber (F := pot) (gradient V)
      (child P hR hc hsmall clock i) (J.joint i) (radius P clock i) sigma amp := by
    dsimp only [J,lower,ClockMeanChildAccuracy.mainKernel]
    simpa only [ClockMeanChildAccuracy.main_radius,ClockMeanChildAccuracy.main_width] using
      ClockMeanChildAccuracy.main_fiber P hK hc hsmall hC hyMean hV Hlo hup clock i
  have he := lowerError_measurable P hR hc hsmall clock hV Hlo hup i
  obtain ⟨hi,hpay⟩ := ClockCenterMoment.center_scale_square P hV hm hlo hup
    (FinalMeanScheduledData.delta_half P hK hc hsmall hC hy) clock i
  have hcost : Integrable (fun b => (amp*Gibbs.primitiveScale pot (center P clock hV Hlo hup i b))^2) μ := by
    convert hi.const_mul (amp^2) using 1
    funext b
    ring
  obtain ⟨hmem,hbound⟩ := FreshChildBatchErrorTransfer.averaged_error_memLp_of_bound
    (Probability.CanonicalNativeTapeLaw.primitiveLaws d) B J
    (fun j => center P clock hV Hlo hup j) (center_measurable P clock hV Hlo hup) μ i
    (lowerError P hR hc hsmall clock hV Hlo hup i) he.stronglyMeasurable
    (Filter.Eventually.of_forall fun b => (hf (center P clock hV Hlo hup i b)).1)
    (fun b => amp*Gibbs.primitiveScale pot (center P clock hV Hlo hup i b)) hcost
    (Filter.Eventually.of_forall fun b => (hf (center P clock hV Hlo hup i b)).2)
  refine ⟨hmem,hbound.trans ?_⟩
  simp only [mul_pow]
  rw [integral_const_mul]
  simpa only [mul_pow] using mul_le_mul_of_nonneg_left hpay (sq_nonneg amp)

/-- Actual pre-record source callback payment. Its law is constructed from
original stationary input and the complete canonical tape. -/
theorem benchmark_error_bound (k : ℕ) (hk : k<P.K+4) (i : Index P) :
    let ρ := adjoin P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk) ∘ₘ
      stageLaw P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean
        (((OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup).prod (stdGaussian (Point d))).prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))) k hk.le
    ∃ hmem : MemLp (benchmarkError P hR hc hsmall clock label hV Hlo hup k i) 2 ρ,
      (∫ z,‖benchmarkError P hR hc hsmall clock label hV Hlo hup k i z‖^2 ∂ρ) ≤ amp^2*(10*(d:ℝ)) ∧
      ‖hmem.toLp (benchmarkError P hR hc hsmall clock label hV Hlo hup k i)‖ ≤
        Real.sqrt (amp^2*(10*(d:ℝ))) := by
  obtain ⟨hmem,hpay⟩ := averaged_main_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean k hk i
  have hp := mainLowerProjection_preserving P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ((OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup).prod (stdGaussian (Point d))) k hk i
  have hmerr := lowerError_measurable P hR hc hsmall clock hV Hlo hup i
  have he : benchmarkError P hR hc hsmall clock label hV Hlo hup k i =
      lowerError P hR hc hsmall clock hV Hlo hup i ∘
        mainLowerProjection P hR hc hsmall clock label hK hC hy k hk i := by
    funext z
    exact benchmarkError_eq_lowerError P hR hc hsmall clock label hK hC hy hV Hlo hup k hk i z
  have hmeas := hmerr.comp hp.measurable
  rw [← he] at hmeas
  have hlaw := benchmark_error_law P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ((OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup).prod (stdGaussian (Point d))) k hk i
  obtain ⟨hactual,heq⟩ := PrivateCompletedRms.memLp_integral_of_law _ _ _ _ hmeas hmerr hlaw hmem
  have hbound := heq.le.trans hpay
  refine ⟨hactual,hbound,?_⟩
  apply FreshChildBatchErrorTransfer.norm_toLp_le_of_square_integral _ _ hactual _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (le_trans (integral_nonneg fun _ => sq_nonneg _) hbound)]
  exact hbound

end AcceleratedLogConcave.Root.ClockMainChildRms
