import AcceleratedLogConcave.Root.ClockFinalReferenceLaw

/-! Original momentum reconstruction from the actual Clock final paired law.
The original momentum is a deterministic function of (Y0,GE,Pi), with its
correlations preserved; it is not adjoined as an independent Gaussian. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockFinalReconstruction
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut Oracle.PrivateCausalLayer
open ClockNoisyLayer ClockChronologicalCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}

/-- Recover H0 from its literal assembly and then the original pre-split P. -/
def reconstruct (y : ((Point d × Point d) × Point d) × (Index P → Point d × Point d)) : Point d :=
  ClockPublicSetup.s • y.1.1.2 + ClockPublicSetup.noise •
    ((∑ i,ClockRetainedFinalSplice.coefficient P clock i • (y.2 i).1) +
      Conditional.GaussianAssembly.reserve (ClockRetainedFinalSplice.coefficient P clock) • y.1.2)

theorem reconstruct_measurable : Measurable (reconstruct (d := d) P clock) := by
  unfold reconstruct
  fun_prop

/-- Deterministic source reconstruction, before choosing any law or references. -/
theorem base_reconstruct (b : Base P d) (Pref : Index P→Point d) :
    reconstruct P clock ((ClockFinalObservationLaw.baseAssembly P clock b).1,
      fun i => ((ClockFinalObservationLaw.baseAssembly P clock b).2 i,Pref i))=b.1.2 := by
  have hr := Conditional.GaussianAssembly.residual_reconstruction
    (ClockRetainedFinalSplice.coefficient_admissible P clock)
    (ClockPublicSetup.splitValues b.1.2 b.2.1 1) b.2.2
  change ClockPublicSetup.splitValues b.1.2 b.2.1 1 =
    (∑ i,ClockRetainedFinalSplice.coefficient P clock i •
      (ClockFinalObservationLaw.baseAssembly P clock b).2 i) +
    Conditional.GaussianAssembly.reserve (ClockRetainedFinalSplice.coefficient P clock) •
      (ClockFinalObservationLaw.baseAssembly P clock b).1.2 at hr
  change ClockPublicSetup.s • ClockPublicSetup.splitValues b.1.2 b.2.1 0+
    ClockPublicSetup.noise • _=b.1.2
  rw [← hr]
  exact congrArg Prod.fst (Kinetic.gaussianSplit_involutive ClockPublicSetup.s ClockPublicSetup.noise
    Kinetic.source_split_coefficients (b.1.2,b.2.1))

variable (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
  {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "host" => Host P hR hc hsmall clock label
local notation "cut" => ClockFinalBatchCoupling.batchCut P hR hc hsmall clock label hK hC hy
local notation "joint" => ClockFinalBatchCoupling.completedKernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
local notation "mainJoint" => ClockChronologicalCoupling.kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
local notation "retained" => ClockFinalJointLaw.retainedPairs (V := V) P hR hc hsmall clock label hK hC hy
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d
local notation "γ" => stdGaussian (Point d)

/-- The final augmentation preserves the complete actual chronological sample. -/
theorem completed_fst (source : Measure ((Point d × Point d) × Tape d host)) :
    (joint ∘ₘ source).map Prod.fst=mainJoint ∘ₘ source := by
  rw [ClockFinalBatchCoupling.completedKernel,← Measure.comp_assoc,
    Measure.map_comp _ _ measurable_fst,← Kernel.fst_eq,
    ClockFinalBatchCoupling.original_preserved,Measure.id_comp]

/-- True initial-assembly support survives the actual final augmentation. -/
theorem completed_sourceBase_ae (source : Measure ((Point d × Point d) × Tape d host)) :
    ∀ᵐ z ∂joint ∘ₘ source,
      z.1.1.1=ClockFinalAssemblySupport.sourceBase P hR hc hsmall clock label
        (ClockFinalAssemblySupport.baseTape P hR hc hsmall clock label z.1) := by
  have h := ClockFinalAssemblySupport.kernel_sourceBase_ae P hR hc hsmall clock label hK hC hy hV hlo hup hyMean source
  rw [← completed_fst P hR hc hsmall clock label hK hC hy hV hlo hup hyMean source] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

/-- Every Pi in the paired projection is the same literal assembly value. -/
theorem pairedPi_eq_base_of_support
    (z : (History P d × Tape d host) × (Index P→Point d))
    (hsupport : z.1.1.1=ClockFinalAssemblySupport.sourceBase P hR hc hsmall clock label
      (ClockFinalAssemblySupport.baseTape P hR hc hsmall clock label z.1)) (i : Index P) :
    ((retained z).2 i).1=(ClockFinalObservationLaw.baseAssembly P clock z.1.1.1).2 i := by
  have he0 := congrArg (fun b : Base P d => b.2.1) hsupport
  have hraw := congrArg (fun b : Base P d => b.2.2) hsupport
  change z.1.1.1.2.1=ClockFinalAssemblyReadout.splitDraw P hR hc hsmall clock label z.1.2 at he0
  change z.1.1.1.2.2=ClockFinalAssemblyReadout.assemblyRaw P hR hc hsmall clock label z.1.2 at hraw
  simp only [ClockFinalJointLaw.retainedPairs,ClockFinalObservationLaw.observation,
    ClockFinalBatchCoupling.observation,split_afterBatch,batchParts_append]
  change ClockFinalBatchCoupling.storedPi (V := V) P hR hc hsmall clock label hK hC hy i
    (z.1.1,(split cut z.1.2).1)=
      ClockRetainedFinalSplice.activeValues P clock
        (ClockPublicSetup.splitValues z.1.1.1.1.2 z.1.1.1.2.1 1) z.1.1.1.2.2 i
  rw [he0,hraw]
  exact ClockFinalAssemblyReadout.terminal_designated_assembled P hR hc hsmall clock label
    (gradient V) z.1.1.1.1.1 z.1.1.1.1.2 z.1.2 i

/-- Reconstruct the original pre-split momentum from the actual paired law. -/
theorem original_momentum_reconstruction_ae (source : Measure ((Point d × Point d) × Tape d host)) :
    ∀ᵐ z ∂joint ∘ₘ source,reconstruct P clock (retained z)=z.1.1.1.1.2 := by
  filter_upwards [completed_sourceBase_ae P hR hc hsmall clock label hK hC hy hV hlo hup hyMean source] with z hz
  have hPi := pairedPi_eq_base_of_support (V := V) P hR hc hsmall clock label hK hC hy z hz
  change ClockPublicSetup.s • (ClockFinalObservationLaw.baseAssembly P clock z.1.1.1).1.1.2+
    ClockPublicSetup.noise • ((∑ i,ClockRetainedFinalSplice.coefficient P clock i • ((retained z).2 i).1)+
      Conditional.GaussianAssembly.reserve (ClockRetainedFinalSplice.coefficient P clock) •
        (ClockFinalObservationLaw.baseAssembly P clock z.1.1.1).1.2)=z.1.1.1.1.2
  simp_rw [hPi]
  exact base_reconstruct P clock z.1.1.1 z.2

/-- Full retained joint law including the actual original momentum. It is
reconstructed from GE and Pi, preserving their true correlations. -/
theorem retained_with_original_law (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (joint ∘ₘ ((μX.prod γ).prod (tapeLaw L host))).map
      (fun z => (z.1.1.1.1.2,retained z))=
    (((μX.prod γ).prod γ) ⊗ₘ ClockFinalJointLaw.averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean).map
      (fun y => (reconstruct P clock y,y)) := by
  have hAE : (fun z => (z.1.1.1.1.2,retained z)) =ᵐ[joint ∘ₘ ((μX.prod γ).prod (tapeLaw L host))]
      (fun z => (reconstruct P clock (retained z),retained z)) := by
    filter_upwards [original_momentum_reconstruction_ae P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
      ((μX.prod γ).prod (tapeLaw L host))] with z hz
    rw [hz]
  rw [Measure.map_congr hAE]
  have hm : Measurable (fun y => (reconstruct (d := d) P clock y,y)) :=
    (reconstruct_measurable P clock).prodMk measurable_id
  rw [← ClockFinalJointLaw.retained_pairs_law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean μX,
    Measure.map_map hm (ClockFinalJointLaw.retainedPairs_measurable P hR hc hsmall clock label hK hC hy hV)]
  rfl

end AcceleratedLogConcave.Root.ClockFinalReconstruction
