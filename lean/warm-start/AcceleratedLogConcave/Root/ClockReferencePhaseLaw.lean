import AcceleratedLogConcave.Root.ClockPrescribedReference
import AcceleratedLogConcave.Kinetic.SourcePhaseReadout
import AcceleratedLogConcave.Kinetic.ReferencePhaseLaw

/-! Change of frame for the actual full retained Clock reference, including
both fresh phase Gaussians and the original visible input. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockReferencePhaseLaw
open Oracle Oracle.TapeLowering Oracle.CubicExecutableWorkShift
open ClockPrescribedReference Kinetic Kinetic.Reheating
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (clock : ClockLaw.Clock)
local notation "E" => Point d
local notation "γ" => stdGaussian E
local notation "Fphys" => OuterRootFlowIdentification.family hV hm P.delta_pos hlo hup
local notation "ell" => Real.sqrt (2*P.delta^2)
local notation "Hlo" => OuterRootFlowIdentification.lower_nonneg hm hlo
local notation "μX" => OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup
local instance centerLaw_probability : IsProbabilityMeasure μX := by
  unfold OuterRootExactTapePath.centerLaw
  infer_instance
local notation "s" => ClockPublicSetup.s
local notation "n" => ClockPublicSetup.noise
local notation "hsn" => Kinetic.source_split_coefficients
include hc hsmall hC in
private theorem order_pos : 0<P.m := by
  have h := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  omega
local notation "Q" => Kinetic.OriginalReferenceMixing.referenceKernel hV (inv_pos.mpr hm) P.delta_pos
  (FinalMeanScheduledData.delta_half P hK hc hsmall hC hy)
  (by simpa only [inv_inv] using hlo) hup (source P hR).M (order_pos P hc hsmall hC)
  P.t (P.t_pos hc) P.K
local notation "k" => ClockPrescribedReference.prescribedKernel P hR hc hsmall hK hC hy hV hm hlo hup clock

/-- Invert the actual original Gaussian split; this restores both original
momentum and E0, rather than adjoining a new conditional Gaussian. -/
def initialFrame (y : (E × E) × E) : GaussianPhase E :=
  phaseSplit s n hsn ((Real.sqrt P.delta • y.1.1,y.1.2),y.2)

theorem initialFrame_measurable : Measurable (initialFrame (d:=d) P) :=
  (phaseSplit  s n hsn).measurable.comp
    (((measurable_fst.fst.const_smul (Real.sqrt P.delta)).prodMk measurable_fst.snd).prodMk measurable_snd)

/-- Full independent source product, transported through the exact inverse
split and physical position scaling. -/
theorem initialFrame_preserving : MeasurePreserving (initialFrame P)
    (((μX).prod γ).prod γ) (gaussianPhaseMeasure ((Fphys).law 0)) := by
  have hp : MeasurePreserving (fun x : E => Real.sqrt P.delta • x) μX ((Fphys).law 0) :=
    ⟨by fun_prop,OuterRootExactTapePath.centerLaw_physical_map P hV hm P.delta_pos hlo hup⟩
  exact (phaseSplit_measurePreserving ((Fphys).law 0) s n hsn).comp
    ((hp.prod (MeasurePreserving.id γ)).prod (MeasurePreserving.id γ))

/-- The accepted pre-collision map sees the identical terminal parent and H0. -/
theorem initialFrame_preCollision (y : (E × E) × E) :
    preCollisionMap Fphys ell clock s n hsn (initialFrame P y)=
      (terminalParent P hV hm hlo hup clock y.1,y.2) := by
  have hi := gaussianSplit_involutive  s n hsn (y.1.2,y.2)
  change (referenceCoupledPairFlow Fphys ell clock
    (Real.sqrt P.delta • y.1.1,(gaussianSplit s n (gaussianSplit s n (y.1.2,y.2))).1),
    (gaussianSplit s n (gaussianSplit s n (y.1.2,y.2))).2)=_
  rw [hi]
  rfl

/-- Exact accepted frame-kernel section at the same complete initial seed. -/
theorem frameKernel_apply (y : (E × E) × E) :
    frameKernel Fphys ell s n hsn Q (clock,initialFrame P y)=k y := by
  change Q (clock,preCollisionMap Fphys ell clock s n hsn (initialFrame P y))=_
  rw [initialFrame_preCollision]
  rfl

/-- The full original-frame seed/root law is the accepted frame disintegration. -/
theorem prescribed_frame_law :
    ((((μX).prod γ).prod γ) ⊗ₘ k).map (Prod.map (initialFrame P) id)=
      (gaussianPhaseMeasure ((Fphys).law 0)) ⊗ₘ
        (frameKernel Fphys ell s n hsn Q).comap (fun z => (clock,z)) measurable_prodMk_left := by
  have he : ((frameKernel Fphys ell s n hsn Q).comap (fun z => (clock,z)) measurable_prodMk_left).comap
      (initialFrame P) (initialFrame_measurable P)=k := by
    ext y : 1
    exact frameKernel_apply P hR hc hsmall hK hC hy hV hm hlo hup clock y
  have h := Kinetic.compProd_map_comap (((μX).prod γ).prod γ) (initialFrame P)
    (initialFrame_measurable P)
    ((frameKernel Fphys ell s n hsn Q).comap (fun z => (clock,z)) measurable_prodMk_left)
  rw [(initialFrame_preserving P hV hm hlo hup).map_eq,he] at h
  exact h.symm

local instance canonicalTapeSpace {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := CanonicalTapeMeasurability.tapeSpace d p
variable (label : ℕ) (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "host" => ClockChronologicalCoupling.Host P hR hc hsmall clock label
local notation "Sample" => (ClockChronologicalCoupling.History P d × Tape d host) × (ClockNoisyLayer.Index P→E)
local notation "μ" => ClockCompletedPhaseLaw.law P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ((μX).prod γ)
local notation "rootObs" => ClockPrescribedReference.rootObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label
local notation "RootFrame" => GaussianPhase E × E
local notation "PhaseTape" => (RootFrame × E) × E

def frameObservation (z : Sample) : RootFrame :=
  (initialFrame P (rootObs z).1,(rootObs z).2)

theorem frameObservation_measurable : Measurable
    (frameObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label) :=
  ((initialFrame_measurable P).comp
    (ClockPrescribedReference.rootObservation_measurable P hR hc hsmall hK hC hy hV hm hlo hup clock label).fst).prodMk
      (ClockPrescribedReference.rootObservation_measurable P hR hc hsmall hK hC hy hV hm hlo hup clock label).snd

/-- Same completed root, restored to the exact accepted initial-time frame. -/
theorem frameObservation_law :
    (μ).map (frameObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label)=
      (gaussianPhaseMeasure ((Fphys).law 0)) ⊗ₘ
        (frameKernel Fphys ell s n hsn Q).comap (fun z => (clock,z)) measurable_prodMk_left := by
  have hp := ClockPrescribedReference.rootObservation_prescribed_law
    P hR hc hsmall hK hC hy hV hm hlo hup clock label hyMean μX
  have h := congrArg (fun ν => ν.map (Prod.map (initialFrame P) id)) hp
  rw [Measure.map_map ((initialFrame_measurable P).prodMap measurable_id)
    (ClockPrescribedReference.rootObservation_measurable P hR hc hsmall hK hC hy hV hm hlo hup clock label)] at h
  exact h.trans (prescribed_frame_law P hR hc hsmall hK hC hy hV hm hlo hup clock)

/-- Keep both actual independent final Gaussian blocks, without changing any
coordinate of the original retained root sample. -/
def frameTapeObservation (z : Sample × (E × E)) : PhaseTape :=
  ((frameObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label z.1,z.2.1),z.2.2)

theorem frameTapeObservation_measurable : Measurable
    (frameTapeObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label) :=
  (((frameObservation_measurable P hR hc hsmall hK hC hy hV hm hlo hup clock label).comp
    measurable_fst).prodMk measurable_snd.fst).prodMk measurable_snd.snd

/-- Exact accepted frameTape, with the same two fresh Gaussian coordinates. -/
theorem frameTapeObservation_law :
    ((μ).prod ((γ).prod γ)).map
      (frameTapeObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label)=
        frameTape Fphys ell s n hsn Q clock := by
  let η := (gaussianPhaseMeasure ((Fphys).law 0)) ⊗ₘ
    (frameKernel Fphys ell s n hsn Q).comap (fun z => (clock,z)) measurable_prodMk_left
  have hp : MeasurePreserving (frameObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label) μ η :=
    ⟨frameObservation_measurable P hR hc hsmall hK hC hy hV hm hlo hup clock label,
      frameObservation_law P hR hc hsmall hK hC hy hV hm hlo hup clock label hyMean⟩
  have ha := (measurePreserving_prodAssoc η γ γ).symm MeasurableEquiv.prodAssoc
  have hs := ha.comp (hp.prod (MeasurePreserving.id ((γ).prod γ)))
  have he : (((Kernel.const ClockLaw.Clock (gaussianPhaseMeasure ((Fphys).law 0))) ⊗ₖ
      frameKernel Fphys ell s n hsn Q) clock)=η := by
    ext S hS
    rw [Kernel.compProd_apply hS,Measure.compProd_apply hS]
    rfl
  change ((μ).prod ((γ).prod γ)).map
    (frameTapeObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label)=_
  rw [frameTape,Kernel.prod_apply,Kernel.prod_apply,Kernel.const_apply,he]
  exact hs.map_eq

private theorem variance_pos : 0<2*P.delta^2 := by
  nlinarith [sq_pos_of_pos P.delta_pos]
private theorem variance_lt : 2*P.delta^2<2*(2*P.delta^2) := by
  nlinarith [sq_pos_of_pos P.delta_pos]
/-- The very same original-potential heat family used by the accepted reference
phase, with no new moment or stochastic-law premise. -/
def heatFamily := originalHeatMixingFamily (R:=2*(2*P.delta^2)) hV (inv_pos.mpr hm) P.delta_pos
  (variance_lt P) (by simpa only [inv_inv] using hlo) hup

/-- Accepted fixed-clock phase readout retaining its original visible input. -/
def referenceFrameOutput (Γ : ℝ) (z : PhaseTape) : (E × E) × (E × E) :=
  let : IsProbabilityMeasure (volume.tilted (fun x : E => -V x)) :=
    Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  (z.1.1.1.1,Kinetic.ReferencePhaseLaw.output (heatFamily P hV hm hlo hup)
    (variance_pos P) (variance_lt P) ell Γ (clock,z))

theorem referenceFrameOutput_measurable (Γ : ℝ) : Measurable
    (referenceFrameOutput P hV hm hlo hup clock Γ) := by
  let : IsProbabilityMeasure (volume.tilted (fun x : E => -V x)) :=
    Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  exact measurable_fst.fst.fst.fst.prodMk
    ((Kinetic.ReferencePhaseLaw.output_measurable (heatFamily P hV hm hlo hup)
      (variance_pos P) (variance_lt P) ell Γ).comp (measurable_const.prodMk measurable_id))

/-- Literal accepted fixed-clock output uses the true terminal velocity and
the same returned dormant output, followed by these exact two fresh draws. -/
theorem referenceFrameOutput_eq (Γ : ℝ) (z : PhaseTape) :
    referenceFrameOutput P hV hm hlo hup clock Γ z=
      (z.1.1.1.1,ClockPhaseGaussianKL.phaseOutput P.delta Γ clock z.1.1.1.1.1
        (s • (preCollisionMap Fphys ell clock s n hsn z.1.1.1).1.2+n • z.1.1.2) z.1.2 z.2) := by
  let : IsProbabilityMeasure (volume.tilted (fun x : E => -V x)) :=
    Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  refine Prod.ext rfl ?_
  have h := sourceFixedClockOutput_eq_actual (heatFamily P hV hm hlo hup)
    (variance_pos P) (variance_lt P) ell (Real.sqrt_nonneg _) (Real.sq_sqrt (by positivity))
    clock Γ z.1.1.1 z.1.1.2 z.1.2 z.2
  simpa only [referenceFrameOutput,Kinetic.ReferencePhaseLaw.output,
    Kinetic.ReferencePhaseLaw.toPhysicalTape,ClockPhaseGaussianKL.phaseOutput,
    ClockPublicSetup.s,ClockPublicSetup.noise,gaussianMix,Prod.map_def,id_eq,
    heatFamily,OuterRootFlowIdentification.family,RecursiveInnovation.originalPhysicalReference,originalHeatMixingFamily,
    mul_assoc,mul_left_comm,mul_comm] using h

/-- Deterministic physical phase readout from the completed retained sample;
only the original-input reconstruction requires its proved AE support. -/
theorem frameTapeOutput_eq_ae (Γ : ℝ) :
    ∀ᵐ z ∂(μ).prod ((γ).prod γ),
      referenceFrameOutput P hV hm hlo hup clock Γ
        (frameTapeObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label z)=
      (ClockCompletedPhaseLaw.sourceInput P hR hc hsmall clock label
        (ClockCompletedPhaseLaw.original P hR hc hsmall clock label z.1),
        ClockPhaseGaussianKL.phaseOutput P.delta Γ clock
          (ClockCompletedPhaseLaw.sourceInput P hR hc hsmall clock label
            (ClockCompletedPhaseLaw.original P hR hc hsmall clock label z.1)).1
          (ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z.1)
          z.2.1 z.2.2) := by
  have hp := ClockPrescribedReference.physicalRetained_input_ae
    P hR hc hsmall hK hC hy hV hm hlo hup clock label hyMean μX
  have hfst : MeasurePreserving (Prod.fst : Sample × (E × E) → Sample)
      ((μ).prod ((γ).prod γ)) μ := measurePreserving_fst
  have hpfst := hfst.quasiMeasurePreserving.ae hp
  filter_upwards [hpfst] with z hz
  rw [referenceFrameOutput_eq]
  change (initialFrame P (rootObs z.1).1).1=
    ClockCompletedPhaseLaw.sourceInput P hR hc hsmall clock label
      (ClockCompletedPhaseLaw.original P hR hc hsmall clock label z.1) at hz
  have hpre := initialFrame_preCollision P hV hm hlo hup clock (rootObs z.1).1
  have hroot : s • (terminalParent P hV hm hlo hup clock (rootObs z.1).1.1).2+
      n • (rootObs z.1).2=
      ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z.1 :=
    ClockPrescribedReference.physicalRetained_output P hR hc hsmall hK hC hy hV hm hlo hup clock label z.1
  change ((initialFrame P (rootObs z.1).1).1,
    ClockPhaseGaussianKL.phaseOutput P.delta Γ clock ((initialFrame P (rootObs z.1).1).1).1
      (s • (preCollisionMap Fphys ell clock s n hsn (initialFrame P (rootObs z.1).1)).1.2+
        n • (rootObs z.1).2) z.2.1 z.2.2)=_
  rw [hpre,hroot,hz]

/-- Exact full original-input/output law of the accepted physical reference
phase at this clock, including both fresh Gaussian blocks. -/
theorem reference_phase_law (Γ : ℝ) :
    ((μ).prod ((γ).prod γ)).map (fun z =>
      (ClockCompletedPhaseLaw.sourceInput P hR hc hsmall clock label
        (ClockCompletedPhaseLaw.original P hR hc hsmall clock label z.1),
        ClockPhaseGaussianKL.phaseOutput P.delta Γ clock
          (ClockCompletedPhaseLaw.sourceInput P hR hc hsmall clock label
            (ClockCompletedPhaseLaw.original P hR hc hsmall clock label z.1)).1
          (ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z.1)
          z.2.1 z.2.2))=
      (frameTape Fphys ell s n hsn Q clock).map
        (referenceFrameOutput P hV hm hlo hup clock Γ) := by
  rw [← frameTapeObservation_law P hR hc hsmall hK hC hy hV hm hlo hup clock label hyMean,
    Measure.map_map (referenceFrameOutput_measurable P hV hm hlo hup clock Γ)
      (frameTapeObservation_measurable P hR hc hsmall hK hC hy hV hm hlo hup clock label)]
  apply Measure.map_congr
  filter_upwards [frameTapeOutput_eq_ae P hR hc hsmall hK hC hy hV hm hlo hup clock label hyMean Γ] with z hz
  exact hz.symm

/-- The source physical length agrees with the reference mixing convention. -/
theorem length_eq : Real.sqrt (2*P.delta^2)=Real.sqrt 2*P.delta := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.sqrt_sq_eq_abs,abs_of_pos P.delta_pos]

/-- Exact reference family, including the heat envelope, used by the genuine
source phase law. -/
theorem family_eq : Fphys=Kinetic.Reheating.clockTransportFamily
    (heatFamily P hV hm hlo hup) (variance_pos P) (variance_lt P) := rfl

end AcceleratedLogConcave.Root.ClockReferencePhaseLaw
