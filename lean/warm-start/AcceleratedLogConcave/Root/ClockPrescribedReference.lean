import AcceleratedLogConcave.Root.ClockFinalReferenceChildren
import AcceleratedLogConcave.Root.OuterRootCenterMoment
import AcceleratedLogConcave.Root.OuterRootLiteralScore
import AcceleratedLogConcave.Root.ConditionalPairedLaw
import AcceleratedLogConcave.Root.ClockCompletedPhaseLaw
import AcceleratedLogConcave.Kinetic.OriginalReferenceMixing

/-! Exact prescribed source reference at the actual forward Clock centers,
identified with the same backward-center physicalRadiusChildren construction.
This concerns the complete retained transition, not only its Gaussian marginal. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockPrescribedReference
open Oracle Oracle.CubicExecutableWorkShift Oracle.TapeLowering
open ClockNoisyLayer ClockBackwardKernel RecursiveRadiusFamily
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (clock : ClockLaw.Clock)
local notation "Hlo" => OuterRootFlowIdentification.lower_nonneg hm hlo
local notation "Fphys" => OuterRootFlowIdentification.family hV hm P.delta_pos hlo hup
local notation "ell" => Real.sqrt (2*P.delta^2)
local notation "hhalf" => FinalMeanScheduledData.delta_half P hK hc hsmall hC hy
local notation "Gmean" => (source P hR).M
local notation "kids" => ClockFinalReferenceChildren.children P hR hc hsmall hK hC hy hV Hlo hup
include hc hsmall hC in
private theorem order_pos : 0<P.m := by
  have h := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  omega

/-- Initial source pair is normalized only in its position coordinate. -/
def physicalInput (c : Point d × Point d) : Point d × Point d := (Real.sqrt P.delta • c.1,c.2)

def terminalParent (c : Point d × Point d) : Point d × Point d :=
  Kinetic.referenceCoupledPairFlow Fphys ell clock (physicalInput P c)

theorem terminalParent_measurable : Measurable (terminalParent P hV hm hlo hup clock) :=
  (Kinetic.referenceCoupledPairFlow Fphys ell clock).measurable.comp
    ((measurable_fst.const_smul (Real.sqrt P.delta)).prodMk measurable_snd)

/-- Exact source child center is the normalized physical position on the
same original parent trajectory at its literal quadrature node. -/
theorem forward_center_eq (i : Index P) (c : Point d × Point d) :
    ClockFinalBatchCoupling.center P clock hV Hlo hup i c =
      (Real.sqrt P.delta)⁻¹ •
        (Kinetic.referenceCoupledPairFlow Fphys ell (ClockSchedule.node
          (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K)
          (ClockSchedule.sourceCells_pos P.delta_pos) clock i) (physicalInput P c)).1 := by
  let u : Set.Icc (0:ℝ) (1/2) := ⟨ClockCollocation.u P.delta P.K clock i,
    (ClockCollocation.u_mem P.delta_pos P.K clock i).1,
    (ClockCollocation.u_mem P.delta_pos P.K clock i).2.trans clock.2.2⟩
  have he : ClockFinalBatchCoupling.center P clock hV Hlo hup i c=
      OuterRootCenterMoment.center hV hm P.delta_pos hlo hup u (physicalInput P c) := by
    unfold ClockFinalBatchCoupling.center
    rw [Numerics.ConditionalSmoothing.jointPath_snd_eq_source _ _ _ u.property]
    rw [OuterRootLiteralScore.path_eq_rawY hV P.delta_pos Hlo hup _ _ u.property]
    simp only [OuterRootCenterMoment.center,physicalInput,smul_smul,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr P.delta_pos).ne',one_smul,ClockCollocation.rF]
    rfl
  exact he.trans (OuterRootCenterMoment.center_eq_pairFlow hV hm P.delta_pos hlo hup u (physicalInput P c))

/-- Concrete forward-center retained data, with the exact prescribed children. -/
def forwardData : ConditionalLaw.Data (Point d × Point d) (Fin d) (N P) where
  weight _ := ClockRetainedFinalSplice.weight P clock
  measurable_weight := measurable_const
  admissible _ := ClockRetainedFinalSplice.coefficient_admissible P clock
  child i := ClockFinalReferenceChildren.forwardChild P hR hc hsmall hK hC hy hV Hlo hup clock i
  markov _ := inferInstance
  invariant i c := ClockFinalReferenceChildren.forwardChild_invariant P hR hc hsmall hK hC hy hV Hlo hup clock i c

/-- The accepted source's physical backward-center data at the terminal parent. -/
def terminalData : ConditionalLaw.Data (Point d × Point d) (Fin d) (N P) :=
  ClockBackwardKernel.fixedData Fphys ell (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K)
    (ClockSchedule.sourceCells_pos P.delta_pos) (ClockSchedule.sourceOrder_pos P.K)
    (Real.sqrt P.delta)⁻¹ (sourceClockChildren P.delta P.delta_pos P.K kids) clock

/-- Equality of each prescribed child transition at the very same original
Pi, after exact forward/backward parent-path identification. -/
theorem child_forward_backward (i : Index P) (c : Point d × Point d) (p : Point d) :
    (forwardData P hR hc hsmall hK hC hy hV hm hlo hup clock).child i (c,p)=
      (terminalData P hR hc hsmall hK hC hy hV hm hlo hup clock).child i
        (terminalParent P hV hm hlo hup clock c,p) := by
  change ((kids).kernel i) ((radiusParameter P.delta P.delta_pos P.K i clock,
      ClockFinalBatchCoupling.center P clock hV Hlo hup i c),p)=
    ((kids).kernel i) ((radiusParameter P.delta P.delta_pos P.K i clock,
      (Real.sqrt P.delta)⁻¹ • ClockBackwardKernel.center Fphys ell
        (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K)
        (ClockSchedule.sourceCells_pos P.delta_pos) i (clock,terminalParent P hV hm hlo hup clock c)),p)
  rw [terminalParent,ClockBackwardKernel.center_forward]
  rw [forward_center_eq]

private theorem retainedData_ext {n : ℕ} (A B : RetainedLaw.Data (Fin d) n)
    (hw : A.weight=B.weight) (hchild : A.child=B.child) : A=B := by
  cases A
  cases B
  cases hw
  cases hchild
  rfl

/-- The fixed parent retains the exact same child kernels and weights. -/
theorem atParent_eq (c : Point d × Point d) :
    ConditionalLaw.atParent (forwardData P hR hc hsmall hK hC hy hV hm hlo hup clock) c=
      ConditionalLaw.atParent (terminalData P hR hc hsmall hK hC hy hV hm hlo hup clock)
        (terminalParent P hV hm hlo hup clock c) := by
  apply retainedData_ext
  · rfl
  · funext i
    ext p : 1
    exact child_forward_backward P hR hc hsmall hK hC hy hV hm hlo hup clock i c p

/-- Exact entire root kernel at the same dormant input, not just its marginal. -/
theorem root_forward_backward (c : Point d × Point d) (H0 : Point d) :
    ConditionalLaw.rootKernel (forwardData P hR hc hsmall hK hC hy hV hm hlo hup clock) (c,H0)=
      ConditionalLaw.rootKernel (terminalData P hR hc hsmall hK hC hy hV hm hlo hup clock)
        (terminalParent P hV hm hlo hup clock c,H0) := by
  have hl := congrArg (fun k : Kernel (Point d) (Point d) => k H0)
    (ConditionalLaw.rootKernel_section (forwardData P hR hc hsmall hK hC hy hV hm hlo hup clock) c)
  have hr := congrArg (fun k : Kernel (Point d) (Point d) => k H0)
    (ConditionalLaw.rootKernel_section (terminalData P hR hc hsmall hK hC hy hV hm hlo hup clock)
      (terminalParent P hV hm hlo hup clock c))
  rw [atParent_eq] at hl
  exact hl.trans hr.symm

/-- Prescribed original-potential reference kernel at the terminal physical
parent, with the unchanged original dormant input. -/
theorem root_eq_referenceKernel (c : Point d × Point d) (H0 : Point d) :
    ConditionalLaw.rootKernel (forwardData P hR hc hsmall hK hC hy hV hm hlo hup clock) (c,H0)=
      Kinetic.OriginalReferenceMixing.referenceKernel hV (inv_pos.mpr hm) P.delta_pos hhalf
        (by simpa only [inv_inv] using hlo) hup Gmean (order_pos P hc hsmall hC)
        P.t (P.t_pos hc) P.K (clock,(terminalParent P hV hm hlo hup clock c,H0)) := by
  rw [root_forward_backward]
  exact (ClockBackwardKernel.kernel_section_apply Fphys ell
    (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K)
    (ClockSchedule.sourceCells_pos P.delta_pos) (ClockSchedule.sourceOrder_pos P.K)
    (Real.sqrt P.delta)⁻¹ (sourceClockChildren P.delta P.delta_pos P.K kids)
    clock (terminalParent P hV hm hlo hup clock c) H0).symm

local instance canonicalTapeSpace {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := CanonicalTapeMeasurability.tapeSpace d p
variable (label : ℕ) (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "D" => forwardData P hR hc hsmall hK hC hy hV hm hlo hup clock
local notation "host" => ClockChronologicalCoupling.Host P hR hc hsmall clock label
local notation "Sample" => (ClockChronologicalCoupling.History P d × Tape d host) × (Index P→Point d)
local notation "joint" => ClockFinalBatchCoupling.completedKernel P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean
local notation "retained" => ClockFinalJointLaw.retainedPairs (V:=V) P hR hc hsmall clock label hK hC hy
local notation "γ" => stdGaussian (Point d)
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d

/-- The actual finite paired transition equals the prescribed children at all
coarse inputs, retaining the common reserve. -/
theorem averagedPairs_eq :
    ClockFinalJointLaw.averagedPairs P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean=
      ConditionalPairedLaw.pairedChildren D := by
  ext c : 1
  rw [ClockFinalReferenceChildren.averagedPairs_apply,ConditionalPairedLaw.pairedChildren_apply]
  rfl

/-- Entire normalized dormant input and returned root, retaining the actual
forward parent pair. -/
def rootObservation (z : Sample) : ((Point d × Point d) × Point d) × Point d :=
  (((retained z).1.1,ConditionalPairedLaw.originalInput D (retained z)),
    ConditionalPairedLaw.referenceOutput D (retained z))

theorem rootObservation_measurable : Measurable
    (rootObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label) := by
  have ht := ClockFinalJointLaw.retainedPairs_measurable P hR hc hsmall clock label hK hC hy hV
  exact ((ht.fst.fst.prodMk ((ConditionalPairedLaw.originalInput_measurable D).comp ht)).prodMk
    ((ConditionalPairedLaw.referenceOutput_measurable D).comp ht))

/-- Actual completed source has exactly the full prescribed retained root
joint, including its correlated original dormant input. -/
theorem rootObservation_law (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (joint ∘ₘ ((μX.prod γ).prod (CanonicalTapeLaw.tapeLaw L host))).map
      (rootObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label)=
        ((μX.prod γ).prod γ) ⊗ₘ ConditionalLaw.rootKernel D := by
  have hp := ClockFinalJointLaw.retained_pairs_law P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean μX
  rw [averagedPairs_eq P hR hc hsmall hK hC hy hV hm hlo hup clock label hyMean] at hp
  have hs := congrArg (fun ν => ν.map (fun y =>
    ((y.1.1,ConditionalPairedLaw.originalInput D y),ConditionalPairedLaw.referenceOutput D y))) hp
  rw [Measure.map_map
    ((measurable_fst.fst.prodMk (ConditionalPairedLaw.originalInput_measurable D)).prodMk
      (ConditionalPairedLaw.referenceOutput_measurable D))
    (ClockFinalJointLaw.retainedPairs_measurable P hR hc hsmall clock label hK hC hy hV)] at hs
  exact hs.trans (ConditionalPairedLaw.paired_retained_root D (μX.prod γ))

/-- The original-potential reference kernel read along this actual parent path. -/
def prescribedKernel : Kernel ((Point d × Point d) × Point d) (Point d) :=
  (Kinetic.OriginalReferenceMixing.referenceKernel hV (inv_pos.mpr hm) P.delta_pos hhalf
    (by simpa only [inv_inv] using hlo) hup Gmean (order_pos P hc hsmall hC)
    P.t (P.t_pos hc) P.K).comap
      (fun y => (clock,(terminalParent P hV hm hlo hup clock y.1,y.2)))
      (measurable_const.prodMk (((terminalParent_measurable P hV hm hlo hup clock).comp measurable_fst).prodMk measurable_snd))

instance prescribedKernel_markov : IsMarkovKernel
    (prescribedKernel P hR hc hsmall hK hC hy hV hm hlo hup clock) := by
  unfold prescribedKernel
  infer_instance

theorem rootKernel_eq_prescribedKernel : ConditionalLaw.rootKernel D=
    prescribedKernel P hR hc hsmall hK hC hy hV hm hlo hup clock := by
  ext y : 1
  exact root_eq_referenceKernel P hR hc hsmall hK hC hy hV hm hlo hup clock y.1 y.2

/-- Exact full joint with the prescribed original-potential source kernel. -/
theorem rootObservation_prescribed_law (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (joint ∘ₘ ((μX.prod γ).prod (CanonicalTapeLaw.tapeLaw L host))).map
      (rootObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label)=
        ((μX.prod γ).prod γ) ⊗ₘ prescribedKernel P hR hc hsmall hK hC hy hV hm hlo hup clock := by
  rw [rootObservation_law,rootKernel_eq_prescribedKernel]

/-- Physical source input and true endpoint readout from the complete retained
root joint. The original P remains the correlated reconstruction from Y0,H0. -/
def physicalRetained (y : ((Point d × Point d) × Point d) × Point d) :
    (Point d × Point d) × Point d :=
  ((Real.sqrt P.delta • y.1.1.1,ClockPublicSetup.s • y.1.1.2+ClockPublicSetup.noise • y.1.2),
    ClockPublicSetup.s • (terminalParent P hV hm hlo hup clock y.1.1).2+
      ClockPublicSetup.noise • y.2)

theorem physicalRetained_measurable : Measurable
    (physicalRetained P hV hm hlo hup clock) := by
  have ht := (terminalParent_measurable P hV hm hlo hup clock).comp
    (show Measurable (fun y : ((Point d × Point d) × Point d) × Point d => y.1.1) from measurable_fst.fst)
  exact ((measurable_fst.fst.fst.const_smul (Real.sqrt P.delta)).prodMk
    ((measurable_fst.fst.snd.const_smul ClockPublicSetup.s).add
      (measurable_fst.snd.const_smul ClockPublicSetup.noise))).prodMk
        ((ht.snd.const_smul ClockPublicSetup.s).add (measurable_snd.const_smul ClockPublicSetup.noise))

/-- The physical terminal velocity is the same literal conditional flow. -/
theorem terminalParent_snd (c : Point d × Point d) :
    (terminalParent P hV hm hlo hup clock c).2=
      OuterRootPhysicalPath.rawY hV P.delta_pos Hlo hup c.1 c.2 clock := by
  exact (congrArg Prod.snd (OuterRootFlowIdentification.conditional_eq_reference_trajectory
    hV hm P.delta_pos hlo hup c.1 c.2 clock.property)).symm

/-- Same returned references and same reserve, now as the exact physical
referenceRoot used by the completed phase comparison. -/
theorem physicalRetained_output (z : Sample) :
    (physicalRetained P hV hm hlo hup clock
      (rootObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label z)).2=
      ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z := by
  unfold physicalRetained
  rw [terminalParent_snd]
  rfl

/-- The actual original momentum is restored, with its retained correlations. -/
theorem physicalRetained_input_ae (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    ∀ᵐ z ∂joint ∘ₘ ((μX.prod γ).prod (CanonicalTapeLaw.tapeLaw L host)),
      (physicalRetained P hV hm hlo hup clock
        (rootObservation P hR hc hsmall hK hC hy hV hm hlo hup clock label z)).1=
      (Real.sqrt P.delta • z.1.1.1.1.1,z.1.1.1.1.2) := by
  filter_upwards [ClockFinalReconstruction.original_momentum_reconstruction_ae
    P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean
    ((μX.prod γ).prod (CanonicalTapeLaw.tapeLaw L host))] with z hz
  apply Prod.ext
  · rfl
  · exact hz

/-- Complete original-input/true-reference-root law. No conditional Gaussian
replacement of the original P, or of any Pi/Pref pair, occurs. -/
theorem physical_reference_law (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (joint ∘ₘ ((μX.prod γ).prod (CanonicalTapeLaw.tapeLaw L host))).map
      (fun z => ((Real.sqrt P.delta • z.1.1.1.1.1,z.1.1.1.1.2),
        ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV Hlo hup z))=
      (((μX.prod γ).prod γ) ⊗ₘ prescribedKernel P hR hc hsmall hK hC hy hV hm hlo hup clock).map
        (physicalRetained P hV hm hlo hup clock) := by
  rw [← rootObservation_prescribed_law P hR hc hsmall hK hC hy hV hm hlo hup clock label hyMean μX,
    Measure.map_map (physicalRetained_measurable P hV hm hlo hup clock)
      (rootObservation_measurable P hR hc hsmall hK hC hy hV hm hlo hup clock label)]
  apply Measure.map_congr
  filter_upwards [physicalRetained_input_ae P hR hc hsmall hK hC hy hV hm hlo hup clock label hyMean μX] with z hz
  exact (Prod.ext hz (physicalRetained_output P hR hc hsmall hK hC hy hV hm hlo hup clock label z)).symm

end AcceleratedLogConcave.Root.ClockPrescribedReference
