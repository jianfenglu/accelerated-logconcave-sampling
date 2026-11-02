import AcceleratedLogConcave.Root.ClockFinalObservationLaw

/-! Full final retained pairs on the actual Clock kernel, with the literal
initial assembly reserve still present. The unchanged final conditional
ignores that reserve; its correct source conditioning pair is (xF,Y0). -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockFinalJointLaw
open Oracle Oracle.TapeLowering Oracle.NoisyLayer Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut Oracle.PrivateCausalLayer
open ClockNoisyLayer ClockChronologicalCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "host" => Host P hR hc hsmall clock label
local notation "batch" => ClockFinalBatchCoupling.data P hR hc hsmall clock label hK hC hy
local notation "cut" => ClockFinalBatchCoupling.batchCut P hR hc hsmall clock label hK hC hy
local notation "J" => ClockFinalBatchCoupling.lower P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d
local notation "γ" => stdGaussian (Point d)
local notation "Obs" => ClockFinalObservationLaw.observation (V := V) P hR hc hsmall clock label hK hC hy
local instance cutPrefixSpace : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance afterPrefixSpace : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d (afterBatch cut)

/-- The reference centers depend on (xF,Y0), while the reserve is retained. -/
def center (i : Index P) (z : (Point d × Point d) × Point d) : Point d :=
  ClockFinalBatchCoupling.center P clock hV hlo hup i z.1

theorem center_measurable (i : Index P) : Measurable (center P clock hV hlo hup i) :=
  (ClockFinalBatchCoupling.center_measurable P clock hV hlo hup i).comp measurable_fst

/-- The identical actual finite conditional, written with its larger coarse datum. -/
def conditional : Kernel (History P d × Prefix d (afterBatch cut)) (Index P → Point d) :=
  (DesignatedChildBatchCoupling.referenceBatch L rfl batch J
    (center P clock hV hlo hup) (center_measurable P clock hV hlo hup)).comap
    Obs (ClockFinalObservationLaw.observation_measurable P hR hc hsmall clock label hK hC hy hV)
instance conditional_markov : IsMarkovKernel
    (conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) := by
  unfold conditional
  infer_instance

/-- This is equality of the actual conditional, not an alternative coupling. -/
theorem conditional_eq :
    ClockFinalBatchCoupling.referenceConditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean =
      conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean := by
  ext z : 1
  simp only [ClockFinalBatchCoupling.referenceConditional,conditional,Kernel.comap_apply,
    DesignatedChildBatchCoupling.referenceBatch,
    Conditional.MeanReferenceLayer.finiteProduct_apply (N P) _ (fun _ => inferInstance),Kernel.comap_apply]
  rfl

/-- Exact finite paired law from the same lower source-recursive kernels. -/
def averagedPairs := DesignatedChildBatchJointTransfer.averagedPairs L rfl batch J
  (center P clock hV hlo hup) (center_measurable P clock hV hlo hup)
instance averagedPairs_markov : IsMarkovKernel
    (averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) := by
  unfold averagedPairs
  infer_instance

theorem averagedPairs_apply (z : (Point d × Point d) × Point d) :
    averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean z =
      Measure.pi (fun i => (ClockMeanChildAccuracy.finalKernel P hK hc hsmall hC hyMean hV hlo hup clock i
        (ClockFinalBatchCoupling.center P clock hV hlo hup i z.1)).map (fun a => (a.1.1,a.2))) :=
  DesignatedChildBatchJointTransfer.averagedPairs_apply L rfl batch J
    (center P clock hV hlo hup) (center_measurable P clock hV hlo hup) z

/-- Same complete original sample, actual Pi, returned reference and GE. -/
def retainedPairs (z : (History P d × Tape d host) × (Index P → Point d)) :
    ((Point d × Point d) × Point d) × (Index P → Point d × Point d) :=
  let obs := Obs (z.1.1,(split (afterBatch cut) z.1.2).1)
  (obs.1,fun i => ((obs.2 i).2.1,z.2 i))

include hV in
theorem retainedPairs_measurable : Measurable (retainedPairs (V := V) P hR hc hsmall clock label hK hC hy) := by
  have hp : Measurable (fun z : (History P d × Tape d host) × (Index P → Point d) =>
      (z.1.1,(split (afterBatch cut) z.1.2).1)) :=
    measurable_fst.fst.prodMk ((measurePreserving_split L (afterBatch cut)).measurable.comp measurable_fst.snd).fst
  have ho := (ClockFinalObservationLaw.observation_measurable P hR hc hsmall clock label hK hC hy hV).comp hp
  exact ho.fst.prodMk (Measurable.of_eval fun i =>
    (((measurable_pi_apply i).comp ho.snd).snd.fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))

/-- Correct joint averaging retains GE while conditioning only the lower
kernels on the actual source pair (xF,Y0). -/
theorem retained_pairs_law (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (ClockFinalBatchCoupling.completedKernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ
      ((μX.prod γ).prod (tapeLaw L host))).map
        (retainedPairs (V := V) P hR hc hsmall clock label hK hC hy)=
      ((μX.prod γ).prod γ) ⊗ₘ averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean := by
  obtain ⟨μ,hμ,hsplit,hprojection⟩ := ClockFinalObservationLaw.kernel_observation_laws
    P hR hc hsmall clock label hK hC hy hV hlo hup hyMean μX
  let _ : IsProbabilityMeasure μ := hμ
  let _ : ∀ i,IsProbabilityMeasure (tapeLaw L (DesignatedChildBatchCoupling.program batch i)) :=
    fun i => tapeLaw_probability L _
  let _ : IsProbabilityMeasure (advancedLaw L cut μ) := by unfold advancedLaw; infer_instance
  have hw := ClockFinalBatchCoupling.whole_suffix P hR hc hsmall clock label hK hC hy hV hlo hup hyMean _ μ hsplit
  rw [conditional_eq P hR hc hsmall clock label hK hC hy hV hlo hup hyMean] at hw
  have hp := FreshChildBatchErrorTransfer.full_sample_projection_preserving L (afterBatch cut) _ _ hw
  have ho : Measurable Obs :=
    ClockFinalObservationLaw.observation_measurable P hR hc hsmall clock label hK hC hy hV
  have hj := DesignatedChildBatchJointTransfer.observed_coarse_pairs L rfl batch J
    (center P clock hV hlo hup) (center_measurable P clock hV hlo hup)
    (advancedLaw L cut μ) ((μX.prod γ).prod γ) Obs ho hprojection
  have hm : Measurable (fun z : (History P d × Prefix d (afterBatch cut)) × (Index P → Point d) =>
      ((Obs z.1).1,fun i => (((Obs z.1).2 i).2.1,z.2 i))) :=
    (ho.comp measurable_fst).fst.prodMk (Measurable.of_eval fun i =>
      (((measurable_pi_apply i).comp (ho.comp measurable_fst).snd).snd.fst.prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  have hf : MeasurePreserving
      (fun z : (History P d × Prefix d (afterBatch cut)) × (Index P → Point d) =>
        ((Obs z.1).1,fun i => (((Obs z.1).2 i).2.1,z.2 i)))
      ((advancedLaw L cut μ) ⊗ₘ conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean)
      (((μX.prod γ).prod γ) ⊗ₘ averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) := ⟨hm,hj⟩
  have h := (hf.comp hp).map_eq
  change (ClockFinalBatchCoupling.kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ
    (ClockChronologicalCoupling.kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ
      ((μX.prod γ).prod (tapeLaw L host)))).map
        (retainedPairs (V := V) P hR hc hsmall clock label hK hC hy) = _ at h
  simpa only [ClockFinalBatchCoupling.completedKernel,← Measure.comp_assoc] using h

end AcceleratedLogConcave.Root.ClockFinalJointLaw
