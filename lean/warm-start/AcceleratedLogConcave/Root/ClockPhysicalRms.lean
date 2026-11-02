import AcceleratedLogConcave.Root.ClockFinalRms
import AcceleratedLogConcave.Root.ClockCompletedPhaseLaw
import AcceleratedLogConcave.Oracle.MeanPaidFinalRms

/-! Closed weighted physical error of the literal Clock root, including the
original-data quadrature defect and every actually executed final child. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockPhysicalRms
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open ClockChronologicalCoupling ClockNoisyLayer Numerics
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "Hlo" => OuterRootFlowIdentification.lower_nonneg hm hlo
local notation "host" => Host P hR hc hsmall clock label
local notation "X" => History P d × Tape d host
local notation "W" => X × (Index P→Point d)
local notation "lawF" => ClockFinalRms.law P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean
local notation "err" => ClockFinalEvaluator.finalError P hR hc hsmall clock label hV hup hm hlo
local notation "pc" => ClockPhysicalReadout.physicalCoefficient P clock
local notation "width" => ClockRetainedFinalSplice.width P clock

def budget : ℝ :=
  (∑ i : Index P, |pc i| * (2*P.delta*ClockMainRms.budget (d := d) P clock+
    Real.sqrt ((4*width i*P.delta^(P.K:ℝ))^2*(10*(d:ℝ))))) +
  ClockPublicSetup.s*ClockQuadraturePower.orderConstant P.K*Real.sqrt (d:ℝ)*P.delta^(P.K+6)

def weightedError (z : W) : Point d := ∑ i,pc i • err i z

def fullError (z : W) : Point d := weightedError P hR hc hsmall clock label hV hm hlo hup z +
  ClockFinalQuadrature.defect P hV hm hlo hup clock z.1.1.1

theorem base_preserving : MeasurePreserving (fun z : W => z.1.1.1) lawF (ClockCenterMoment.baseLaw P hV hm hlo hup) :=
  (ClockMainRms.base_preserving P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean).comp
    (ClockFinalRms.original_preserving P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean)

/-- The complete physical sum is paid on the actual completed law. -/
theorem full_error_bound :
    ∃ h : MemLp (fullError P hR hc hsmall clock label hV hm hlo hup) 2 lawF,
      ‖h.toLp (fullError P hR hc hsmall clock label hV hm hlo hup)‖≤budget (d := d) P clock := by
  have he i := (ClockFinalRms.final_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean i).choose
  have heb i := (ClockFinalRms.final_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean i).choose_spec
  obtain ⟨hs,hsb⟩ := MeanPaidFinalRms.weighted_norm_le lawF pc err he _ heb
  have hp := base_preserving P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean
  have hq := (ClockFinalQuadrature.defect_memLp P hV hm hlo hup clock).comp_measurePreserving hp
  have hqb : ‖hq.toLp (ClockFinalQuadrature.defect P hV hm hlo hup clock ∘ (fun z : W=>z.1.1.1))‖≤
      ClockPublicSetup.s*ClockQuadraturePower.orderConstant P.K*Real.sqrt (d:ℝ)*P.delta^(P.K+6) := by
    rw [← Lp.toLp_compMeasurePreserving (ClockFinalQuadrature.defect_memLp P hV hm hlo hup clock) hp,
      Lp.norm_compMeasurePreserving]
    exact ClockFinalQuadrature.defect_norm_le P hV hm hlo hup clock
      (FinalMeanScheduledData.delta_half P hK hc hsmall hC hy)
  refine ⟨hs.add hq,?_⟩
  change ‖(hs.add hq).toLp ((fun z : W=>∑ i,pc i • err i z)+
    (ClockFinalQuadrature.defect P hV hm hlo hup clock ∘ (fun z : W=>z.1.1.1)))‖≤_
  rw [MemLp.toLp_add hs hq]
  exact (norm_add_le _ _).trans (add_le_add hsb hqb)

/-- The original split and raw assembly coordinates remain literally true. -/
theorem sourceBase_ae : ∀ᵐ z ∂lawF,
    z.1.1.1=ClockFinalAssemblySupport.sourceBase P hR hc hsmall clock label
      (ClockFinalAssemblySupport.baseTape P hR hc hsmall clock label z.1) :=
  (ClockFinalRms.original_preserving P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean).quasiMeasurePreserving.ae
    (ClockFinalAssemblySupport.kernel_sourceBase_ae P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean
      (ClockMainRms.sourceLaw P hR hc hsmall clock label hV hm hlo hup))

private theorem split_reconstruct (momentum E0 : Point d) :
    momentum=ClockPublicSetup.s • ClockPublicSetup.splitValues momentum E0 0+
      ClockPublicSetup.noise • ClockPublicSetup.splitValues momentum E0 1 := by
  have hs : ClockPublicSetup.s^2+ClockPublicSetup.noise^2=1 := by
    dsimp [ClockPublicSetup.s,ClockPublicSetup.noise]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  dsimp [ClockPublicSetup.splitValues]
  calc
    momentum = (ClockPublicSetup.s^2+ClockPublicSetup.noise^2) • momentum := by rw [hs,one_smul]
    _ = _ := by simp only [smul_add,smul_smul,pow_two,add_smul]; module

/-- Same-source algebra retains the full mathematical mean row. -/
theorem actual_error_eq_ae : ∀ᵐ z ∂lawF,
    ClockCompletedPhaseLaw.actualRoot (V := V) P hR hc hsmall clock label z -
      ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z =
    fullError P hR hc hsmall clock label hV hm hlo hup z := by
  filter_upwards [sourceBase_ae P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean] with z hz
  have he0 := congrArg (fun b : Base P d=>b.2.1) hz
  have hraw := congrArg (fun b : Base P d=>b.2.2) hz
  change z.1.1.1.2.1=ClockFinalAssemblyReadout.splitDraw P hR hc hsmall clock label z.1.2 at he0
  change z.1.1.1.2.2=ClockFinalAssemblyReadout.assemblyRaw P hR hc hsmall clock label z.1.2 at hraw
  let U := fun i => ClockFinalChildRms.meanRow P clock hV hm hlo hup i
    (ClockFinalObservationLaw.baseAssembly P clock z.1.1.1).1
  have hout := ClockFinalCorrectionReadout.output_sub_reference P hR hc hsmall clock label
    (gradient V) z.1.1.1.1.1 z.1.1.1.1.2 z.1.2 U z.2
  have hquad := ClockFinalQuadrature.defect_eq_primitive_row P hV hm hlo hup clock z.1.1.1
  have hsplit := split_reconstruct (d := d) z.1.1.1.1.2 z.1.1.1.2.1
  have hreserve : ClockFinalCorrectionReadout.reserve P hR hc hsmall clock label z.1.1.1.1.2 z.1.2 =
      (ClockFinalObservationLaw.baseAssembly P clock z.1.1.1).1.2 := by
    unfold ClockFinalCorrectionReadout.reserve ClockFinalObservationLaw.baseAssembly
    rw [← he0,← hraw]
  have hw := congrArg (fun v : Point d=>ClockPublicSetup.noise • v) hout
  rw [smul_sub,Finset.smul_sum] at hw
  simp only [smul_smul] at hw
  simp_rw [← ClockPhysicalReadout.physicalCoefficient_eq_noise_correction] at hw
  change ClockPublicSetup.noise • ClockFinalCorrectionReadout.output P hR hc hsmall clock label
      (gradient V) z.1.1.1.1.1 z.1.1.1.1.2 z.1.2 -
    ClockPublicSetup.noise • ClockFinalCorrectionReadout.referenceOutput P hR hc hsmall clock label U z.2
      z.1.1.1.1.2 z.1.2 = weightedError P hR hc hsmall clock label hV hm hlo hup z at hw
  dsimp only [ClockCompletedPhaseLaw.actualRoot,ClockCompletedPhaseLaw.sourceRoot,
    ClockCompletedPhaseLaw.original,ClockChronologicalCoupling.original,ClockPhysicalReadout.physicalOutput]
  change z.1.1.1.1.2+ClockPublicSetup.noise •
      (ClockFinalCorrectionReadout.output P hR hc hsmall clock label (gradient V) z.1.1.1.1.1 z.1.1.1.1.2 z.1.2-
        ClockPublicSetup.splitValues z.1.1.1.1.2 (ClockFinalAssemblyReadout.splitDraw P hR hc hsmall clock label z.1.2) 1) -
      ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z = _
  rw [← he0]
  nth_rw 1 [hsplit]
  dsimp only [ClockCompletedPhaseLaw.referenceRoot,ClockFinalReferenceLaw.gaussianCorrection,
    ClockFinalReferenceLaw.recombine,ClockFinalReferenceLaw.referenceObservation,ClockFinalJointLaw.retainedPairs,
    ClockFinalObservationLaw.observation]
  rw [fullError,hquad,← hw]
  dsimp only [ClockFinalCorrectionReadout.referenceOutput] at *
  rw [hreserve]
  simp only [smul_add,smul_smul,Finset.smul_sum]
  have hmean : (∑ i, (ClockPublicSetup.noise*ClockRetainedFinalSplice.correctionWeight P clock i) •
      Gibbs.primitiveMean (OuterRootOriginalData.potential V P.delta)
        (center P clock hV Hlo hup i z.1.1.1) (radius P clock i)) =
      ∑ i, (ClockPublicSetup.noise*ClockRetainedFinalSplice.correctionWeight P clock i) • U i := rfl
  rw [hmean]
  dsimp only [ClockFinalObservationLaw.baseAssembly] at *
  module

theorem budget_nonneg : 0≤budget (d := d) P clock := by
  unfold budget
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (abs_nonneg _)
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) P.delta_pos.le) (ClockMainRms.budget_nonneg (d := d) P clock))
      (Real.sqrt_nonneg _)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num [ClockPublicSetup.s])
      (ClockQuadraturePower.orderConstant_nonneg P.K)) (Real.sqrt_nonneg _)) (pow_nonneg P.delta_pos.le _)

/-- Literal implemented physical output minus the actual retained reference root. -/
def actualError (z : W) : Point d :=
  ClockCompletedPhaseLaw.actualRoot (V := V) P hR hc hsmall clock label z -
    ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z

/-- Both implementation and reference are the existing source-facing readouts. -/
theorem actual_error_bound :
    ∃ h : MemLp (actualError P hR hc hsmall clock label hK hC hy hV hm hlo hup) 2 lawF,
      ‖h.toLp (actualError P hR hc hsmall clock label hK hC hy hV hm hlo hup)‖≤budget (d := d) P clock ∧
      (∫ z,‖actualError P hR hc hsmall clock label hK hC hy hV hm hlo hup z‖^2 ∂lawF)≤(budget (d := d) P clock)^2 := by
  obtain ⟨hf,hfb⟩ := full_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean
  have hae : actualError P hR hc hsmall clock label hK hC hy hV hm hlo hup =ᵐ[lawF]
      fullError P hR hc hsmall clock label hV hm hlo hup :=
    actual_error_eq_ae P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean
  have ha := hf.ae_eq hae.symm
  have hb : ‖ha.toLp (actualError P hR hc hsmall clock label hK hC hy hV hm hlo hup)‖≤budget (d := d) P clock := by
    rw [MemLp.toLp_congr ha hf hae]
    exact hfb
  refine ⟨ha,hb,?_⟩
  rw [← Analysis.DominatedLp.norm_sq_toLp ha]
  exact (sq_le_sq₀ (norm_nonneg _) (budget_nonneg (d := d) P clock)).2 hb

end AcceleratedLogConcave.Root.ClockPhysicalRms
