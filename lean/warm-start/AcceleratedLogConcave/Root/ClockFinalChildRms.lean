import AcceleratedLogConcave.Root.ClockFinalReferenceLaw
import AcceleratedLogConcave.Root.ClockCenterMoment
import AcceleratedLogConcave.Root.ClockOriginalGradientKernel
import AcceleratedLogConcave.Oracle.DesignatedChildBatchBenchmarkError
import AcceleratedLogConcave.Oracle.PrivateCompletedRms

/-! Full-seed final-child benchmark RMS on the actual completed Clock law.
The primitive mean row is explicit. Lower accuracy is the already constructed
source recursion, and its scale moment comes from original stationary data. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockFinalChildRms
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut Oracle.PrivateCausalLayer
open ClockNoisyLayer ClockChronologicalCoupling OuterRootFlowIdentification
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
local notation "host" => Host P hR hc hsmall clock label
local notation "batch" => ClockFinalBatchCoupling.data P hR hc hsmall clock label hK hC hy
local notation "cut" => ClockFinalBatchCoupling.batchCut P hR hc hsmall clock label hK hC hy
local notation "J" => ClockFinalBatchCoupling.lower P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d
local notation "γ" => stdGaussian (Point d)
local notation "μX" => OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup
local notation "ξ" => ((μX).prod γ).prod γ
local notation "ctr" => ClockFinalJointLaw.center P clock hV Hlo hup
local notation "hctr" => ClockFinalJointLaw.center_measurable P clock hV Hlo hup
local notation "obs" => ClockFinalObservationLaw.observation (V := V) P hR hc hsmall clock label hK hC hy
local notation "hobs" => ClockFinalObservationLaw.observation_measurable P hR hc hsmall clock label hK hC hy hV
local notation "width" => ClockRetainedFinalSplice.width P clock
local notation "radius" => (fun i => (FinalMeanScheduledData.state P i clock).radius)
local instance center_probability : IsProbabilityMeasure μX := by unfold OuterRootExactTapePath.centerLaw; infer_instance
local instance cutPrefixSpace : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance afterPrefixSpace : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d (afterBatch cut)

/-- Actual source primitive mean at the exact conditional benchmark center. -/
def meanRow (i : Index P) (c : (Point d × Point d) × Point d) : Point d :=
  Gibbs.primitiveMean pot (ctr i c) (radius i)

theorem meanRow_measurable (i : Index P) : Measurable (meanRow P clock hV hm hlo hup i) := by
  have hF : ContDiff ℝ 2 pot := hV.comp (contDiff_id.const_smul (Real.sqrt P.delta))
  exact (Gibbs.primitive_mean_lipschitz hF P.delta_pos.le
    (ClockMeanChildAccuracy.scaled_hessian_nonneg P hV Hlo)
    (ClockMeanChildAccuracy.scaled_hessian_upper P hV hup)
    (FinalMeanScheduledData.root_positive P i clock).1).continuous.measurable.comp (hctr i)

/-- Averaged physical lower-child error, retaining its complete standalone seed. -/
def lowerError (i : Index P)
    (z : ((Point d × Point d) × Point d) ×
      ((Point d × Tape d (ClockRetainedFinalSplice.final P hR hc hsmall clock i).program) × Point d)) : Point d :=
  DesignatedChildRunShift.lowerError (ClockRetainedFinalSplice.final P hR hc hsmall clock i).program
    (gradient V) (ClockRetainedFinalSplice.final P hR hc hsmall clock i).coefficient
    (ctr i z.1) (meanRow P clock hV hm hlo hup i z.1) (width i) z.2

theorem lowerError_measurable (i : Index P) : Measurable (lowerError P hR hc hsmall clock hV hm hlo hup i) := by
  have hp := program_point_of_measurable (ClockRetainedFinalSplice.final P hR hc hsmall clock i).program
    (gradient V) (ClockOriginalGradientKernel.originalGradient_measurable hV)
    (fun _ => (ClockRetainedFinalSplice.final P hR hc hsmall clock i).coefficient)
    (fun z : ((Point d × Point d) × Point d) ×
      ((Point d × Tape d (ClockRetainedFinalSplice.final P hR hc hsmall clock i).program) × Point d) => ctr i z.1)
    (fun z => z.2.1.1) (fun z => z.2.1.2) measurable_const ((hctr i).comp measurable_fst)
    measurable_snd.fst.fst measurable_snd.fst.snd
  exact hp.sub (((meanRow_measurable P clock hV hm hlo hup i).comp measurable_fst).add
    (measurable_snd.snd.const_smul (width i)))

include hK hc hsmall hC hy in
/-- The actual coarse source pair and retained assembly reserve pay 10d. -/
theorem center_scale_square (i : Index P) :
    Integrable (fun c => (Gibbs.primitiveScale pot (ctr i c))^2) ξ ∧
      (∫ c,(Gibbs.primitiveScale pot (ctr i c))^2 ∂ξ)≤10*(d:ℝ) := by
  obtain ⟨hi,hb⟩ := ClockCenterMoment.center_scale_square P hV hm hlo hup
    (FinalMeanScheduledData.delta_half P hK hc hsmall hC hy) clock i
  let _ : IsProbabilityMeasure (Measure.pi fun _ : Index P => γ) := inferInstance
  have hp := (measurePreserving_fst (μ := ξ) (ν := Measure.pi fun _ : Index P => γ)).comp
    (ClockFinalObservationLaw.baseAssembly_preserving P clock μX)
  have he : (fun c => (Gibbs.primitiveScale pot (ctr i c))^2) ∘
      (fun b => (ClockFinalObservationLaw.baseAssembly P clock b).1) =
      (fun b => (Gibbs.primitiveScale pot (ClockChronologicalCoupling.center P clock hV Hlo hup i b))^2) := rfl
  have hF : ContDiff ℝ 2 pot := hV.comp (contDiff_id.const_smul (Real.sqrt P.delta))
  have hmeas : Measurable (fun c => (Gibbs.primitiveScale pot (ctr i c))^2) := by
    unfold Gibbs.primitiveScale
    exact (measurable_const.add (((ClockOriginalGradientKernel.originalGradient_measurable hF).comp (hctr i)).norm)).pow_const 2
  have hcomp : Integrable ((fun c => (Gibbs.primitiveScale pot (ctr i c))^2) ∘
      (fun b => (ClockFinalObservationLaw.baseAssembly P clock b).1)) (ClockCenterMoment.baseLaw P hV hm hlo hup) := by
    rw [he]
    exact hi
  have ht := (hp.integrable_comp hmeas.aestronglyMeasurable).mp hcomp
  have heq := integral_map hp.measurable.aemeasurable (by rw [hp.map_eq]; exact ht.aestronglyMeasurable)
  rw [hp.map_eq] at heq
  refine ⟨ht,?_⟩
  exact heq.trans_le hb

/-- Lower final accuracy and original stationary moments are closed suppliers. -/
theorem averaged_error_bound (i : Index P) :
    MemLp (lowerError P hR hc hsmall clock hV hm hlo hup i) 2
      (ξ ⊗ₘ ((J).joint i).comap (ctr i) (hctr i)) ∧
    (∫ z,‖lowerError P hR hc hsmall clock hV hm hlo hup i z‖^2
      ∂ξ ⊗ₘ ((J).joint i).comap (ctr i) (hctr i)) ≤
      (4*width i*P.delta^(P.K:ℝ))^2*(10*(d:ℝ)) := by
  let amp := 4*width i*P.delta^(P.K:ℝ)
  have hf : MeanStandaloneLowerErrorBound.Fiber (F := pot) (gradient V)
      (ClockRetainedFinalSplice.final P hR hc hsmall clock i) ((J).joint i) (radius i) (width i) amp :=
    ClockMeanChildAccuracy.final_fiber P hK hc hsmall hC hyMean hV Hlo hup clock i
  obtain ⟨hi,hpay⟩ := center_scale_square (P := P) (hc := hc) (hsmall := hsmall) (clock := clock) (hK := hK) (hC := hC) (hy := hy) hV hm hlo hup i
  have hcost : Integrable (fun c => (amp*Gibbs.primitiveScale pot (ctr i c))^2) ξ := by
    convert hi.const_mul (amp^2) using 1
    funext c
    ring
  obtain ⟨hmem,hbound⟩ := DesignatedChildBatchErrorTransfer.averaged_error_memLp_of_bound L batch J ctr hctr ξ i
    (lowerError P hR hc hsmall clock hV hm hlo hup i)
    (lowerError_measurable P hR hc hsmall clock hV hm hlo hup i).stronglyMeasurable
    (Filter.Eventually.of_forall fun c => (hf (ctr i c)).1)
    (fun c => amp*Gibbs.primitiveScale pot (ctr i c)) hcost
    (Filter.Eventually.of_forall fun c => (hf (ctr i c)).2)
  refine ⟨hmem,hbound.trans ?_⟩
  simp only [mul_pow]
  rw [integral_const_mul]
  simpa only [amp,mul_pow] using mul_le_mul_of_nonneg_left hpay (sq_nonneg amp)

/-- Benchmark callback uses the actual compiler-transformed final child tape,
original Pi and center Phi+rho current; this is not an independently run child. -/
def prefixError (i : Index P) := DesignatedChildBatchBenchmarkError.sourceError batch ctr obs i
  (gradient V) (meanRow P clock hV hm hlo hup i) (width i)

def benchmarkError (i : Index P) (z : (History P d × Tape d host) × (Index P→Point d)) : Point d :=
  prefixError P hR hc hsmall clock label hK hC hy hV hm hlo hup i
    ((z.1.1,(split (afterBatch cut) z.1.2).1),z.2)

/-- Actual completed fullsource final benchmark payment. No child accuracy,
source projection, or moment premise remains. -/
theorem benchmark_error_bound (i : Index P) :
    let completedLaw := ClockFinalBatchCoupling.completedKernel P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ∘ₘ
      (((μX).prod γ).prod (tapeLaw L host))
    ∃ hmem : MemLp (benchmarkError P hR hc hsmall clock label hK hC hy hV hm hlo hup i) 2 completedLaw,
      (∫ z,‖benchmarkError P hR hc hsmall clock label hK hC hy hV hm hlo hup i z‖^2 ∂completedLaw)≤
        (4*width i*P.delta^(P.K:ℝ))^2*(10*(d:ℝ)) ∧
      ‖hmem.toLp (benchmarkError P hR hc hsmall clock label hK hC hy hV hm hlo hup i)‖≤
        Real.sqrt ((4*width i*P.delta^(P.K:ℝ))^2*(10*(d:ℝ))) := by
  dsimp only
  obtain ⟨μ,hμ,hsplit,hprojection⟩ := ClockFinalObservationLaw.kernel_observation_laws
    P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean μX
  let _ : IsProbabilityMeasure μ := hμ
  let _ : ∀ i,IsProbabilityMeasure (tapeLaw L (DesignatedChildBatchCoupling.program batch i)) :=
    fun i => tapeLaw_probability L _
  let _ : IsProbabilityMeasure (advancedLaw L cut μ) := by unfold advancedLaw; infer_instance
  obtain ⟨hlower,hbound⟩ := averaged_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean i
  have hshift := (FinalMeanScheduledData.final_queryShift_and_mass P hK hc hsmall hC hy i clock).1
  let E := prefixError P hR hc hsmall clock label hK hC hy hV hm hlo hup i
  have hE := DesignatedChildBatchBenchmarkError.source_error_memLp batch ctr obs L rfl J hctr
    (advancedLaw L cut μ) ξ hobs hprojection i (gradient V) (meanRow P clock hV hm hlo hup i) (width i) hshift hlower
  have hEsq := DesignatedChildBatchBenchmarkError.source_error_square_integral batch ctr obs L rfl J hctr
    (advancedLaw L cut μ) ξ hobs hprojection i (gradient V) (meanRow P clock hV hm hlo hup i) (width i) hshift hlower
  have hwhole := ClockFinalBatchCoupling.whole_suffix P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean _ μ hsplit
  rw [ClockFinalJointLaw.conditional_eq P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean] at hwhole
  have hfull := FreshChildBatchErrorTransfer.full_sample_error_memLp L (afterBatch cut) _ _ hwhole E hE
  have hfullsq := FreshChildBatchErrorTransfer.full_sample_error_square_integral L (afterBatch cut) _ _ hwhole E hE
  have hi := (memLp_two_iff_integrable_sq_norm hlower.aestronglyMeasurable).mp hlower
  have hpay : (∫ z,‖E z‖^2 ∂DesignatedChildBatchErrorTransfer.observedLaw L rfl batch J ctr hctr
      (advancedLaw L cut μ) obs hobs)≤(4*width i*P.delta^(P.K:ℝ))^2*(10*(d:ℝ)) := by
    change (∫ z,‖E z‖^2 ∂DesignatedChildBatchErrorTransfer.observedLaw L rfl batch J ctr hctr
      (advancedLaw L cut μ) obs hobs) = _ at hEsq
    exact hEsq.trans_le ((Measure.integral_compProd hi).symm.trans_le hbound)
  have he : ClockFinalBatchCoupling.kernel P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ∘ₘ
      (ClockChronologicalCoupling.kernel P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ∘ₘ
        (((μX).prod γ).prod (tapeLaw L host)))=
      ClockFinalBatchCoupling.completedKernel P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ∘ₘ
        (((μX).prod γ).prod (tapeLaw L host)) := by
    rw [ClockFinalBatchCoupling.completedKernel,← Measure.comp_assoc]
  rw [he] at hfull hfullsq
  change MemLp (benchmarkError P hR hc hsmall clock label hK hC hy hV hm hlo hup i) 2 _ at hfull
  have hs := hfullsq.trans_le hpay
  refine ⟨hfull,hs,?_⟩
  apply FreshChildBatchErrorTransfer.norm_toLp_le_of_square_integral _ _ hfull _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (le_trans (integral_nonneg fun _ => sq_nonneg _) hs)]
  exact hs

end AcceleratedLogConcave.Root.ClockFinalChildRms
