import AcceleratedLogConcave.Root.ClockChronologicalCoupling
import AcceleratedLogConcave.Oracle.DesignatedChildBatchJointTransfer

/-! Actual designated final children of the retained Clock execution. The
lower kernels are the existing source recursion. Every Pi is read from the
literal interpreter store, and the complete original sample and correction
tail remain present after augmentation. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockFinalBatchCoupling
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut
open Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability Oracle.PrivateCausalLayer
open ClockNoisyLayer ClockChronologicalCoupling Numerics
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ)
  (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
local notation "cur" => terminalCursor P hR hc hsmall clock label
local notation "host" => Host P hR hc hsmall clock label

def data : DesignatedChildBatchCoupling.Data (N P) (ClockRetainedFinalSplice.size P hR hc hsmall clock) (cur).ctx where
  child := ClockRetainedFinalSplice.final P hR hc hsmall clock
  slot := ClockRetainedFinalSplice.finalSlot P hR hc hsmall clock
  old := (cur).old
  designated i := (cur).saved (ClockRetainedFinalSplice.designatedRef P i)
  auxiliary := ClockRetainedFinalSplice.finalAuxiliary P hR hc hsmall clock label
  rho _ := rhoC P
  radius i := (FinalMeanScheduledData.state P i clock).radius
  Ds := P.Ds
  rho_nonneg _ := (rhoC_pos P).le
  radius_pos i := (FinalMeanScheduledData.root_positive P i clock).1
  Ds_pos := P.Ds_pos
  shift_budget i := (FinalMeanScheduledData.final_queryShift_and_mass P hK hc hsmall hC hy i clock).2
  small i := rhoC_le_radius P clock i
local notation "batch" => data P hR hc hsmall clock label hK hC hy

/-- Literal arithmetic after the designated children, including subtraction
of the same stored Pi and the original split parent H0. -/
def suffix : Prog (ClockRetainedFinalSplice.size P hR hc hsmall clock)
    (replyCtx (N P) (cur).ctx) .point :=
  (RetainedMeanCorrection.code
    (RefMap.shiftMany (N P) ((cur).saved (ClockRetainedFinalSplice.parentRef P)))
    batchRef (fun i => RefMap.shiftMany (N P) ((cur).saved (ClockRetainedFinalSplice.designatedRef P i)))).lower
      (ClockRetainedFinalSplice.correctionSlot P hR hc hsmall clock) (fun q => q)
      (RefMap.shiftMany (N P) ((cur).saved (ClockRetainedFinalSplice.parentRef P)))
      (RefMap.shiftMany (N P) ((cur).saved (ClockRetainedFinalSplice.parentRef P)))

/-- This is exactly the reached final cut in the original complete program. -/
def batchCut : TailCut (.batch [] (DesignatedChildBatchCoupling.program batch)
    (suffix P hR hc hsmall clock label)) host :=
  terminalCut P hR hc hsmall clock label

theorem data_table (i : Index P) :
    ClockRetainedFinalSplice.table P hR hc hsmall clock ∘ (batch).slot i =
      matrixTable (CovarianceSetup.childRoot ((batch).rho i) ((batch).radius i)
        ((batch).child i).shiftVector) ((batch).child i).coefficient :=
  ClockRetainedFinalSplice.table_final P hR hc hsmall clock i

variable {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d

/-- Concrete actual final lower joints; no Lower or coupling kernel is supplied. -/
def lower : DesignatedChildBatchCoupling.Lower L batch where
  joint i := ClockMeanChildAccuracy.finalKernel P hK hc hsmall hC hyMean hV hlo hup clock i
  markov i := ClockMeanChildAccuracy.final_markov P hK hc hsmall hC hyMean hV hlo hup clock i
  source i := ClockMeanChildAccuracy.final_source P hK hc hsmall hC hyMean hV hlo hup clock i

local notation "cut" => batchCut P hR hc hsmall clock label hK hC hy
local notation "J" => lower P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
local instance cutPrefixSpace : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance afterPrefixSpace : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d (afterBatch cut)
local notation "Past" => ClockChronologicalCoupling.History P d

def input (z : Past) : Inputs d (ClockRetainedFinalSplice.size P hR hc hsmall clock) :=
  ⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,z.1.1.1,z.1.1.2⟩

/-- The conditioning datum is the actual source pair (xF,Y0). In particular
it does not condition on the original momentum before the public split. -/
def coarse (z : Past × Prefix d cut) : Point d × Point d :=
  (z.1.1.1.1,ClockPublicSetup.splitValues z.1.1.1.2 z.1.1.2.1 0)

theorem coarse_measurable : Measurable (coarse (d := d) P hR hc hsmall clock label hK hC hy) := by
  unfold coarse
  simp only [ClockPublicSetup.splitValues,Matrix.cons_val_zero]
  fun_prop

/-- Conditional root-flow center at the same literal outer node. -/
def center (i : Index P) (z : Point d × Point d) : Point d :=
  z.1+(ClockCollocation.rF P.delta*ClockCollocation.u P.delta P.K clock i) •
    (ConditionalSmoothing.jointPath (OuterRootOriginalData.data hV P.delta_pos hlo hup)
      (ClockCollocation.u P.delta P.K clock i) z).2

theorem center_measurable (i : Index P) : Measurable (center P clock hV hlo hup i) := by
  have hp : Measurable (fun z : Point d × Point d =>
      ConditionalSmoothing.jointPath (OuterRootOriginalData.data hV P.delta_pos hlo hup)
        (ClockCollocation.u P.delta P.K clock i) z) :=
    (ConditionalSmoothing.continuous_jointPath
      (OuterRootOriginalData.data hV P.delta_pos hlo hup)).measurable.comp
      (measurable_const.prodMk (measurable_id : Measurable (id : Point d × Point d → _)))
  exact measurable_fst.add (hp.snd.const_smul (ClockCollocation.rF P.delta*ClockCollocation.u P.delta P.K clock i))

/-- Source history comparison, already updated by every actual main batch. -/
def comparison (i : Index P) (z : Past × Prefix d cut) : Point d := z.1.2.2 i

theorem comparison_measurable (i : Index P) :
    Measurable (comparison (d := d) P hR hc hsmall clock label hK hC hy i) := by
  unfold comparison
  fun_prop

/-- Prefix interpreter store; its Pi and parent H0 are the original saved
references rather than new Gaussian coordinates. -/
def store (z : Past × Prefix d cut) : Env d (cur).ctx :=
  envAt (gradient V) (input P hR hc hsmall clock z.1) cut Env.empty z.2

include hV in
private theorem store_measurable : OperationalMeasurability.EnvPathMeasurable
    (store (V := V) P hR hc hsmall clock label hK hC hy) := by
  have hG : Measurable (gradient V) :=
    ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp (hV.continuous_fderiv (by norm_num))).measurable
  have he : OperationalMeasurability.EnvPathMeasurable (fun _ : Past × Prefix d cut => (Env.empty : Env d [])) :=
    by intro ty ref; cases ref
  intro ty ref
  exact envAt_pathMeasurable (gradient V) hG cut
    (fun z : Past × Prefix d cut => input P hR hc hsmall clock z.1) (fun _ => Env.empty) Prod.snd
    (fun _ => measurable_const) (by unfold input; fun_prop) (by unfold input; fun_prop)
    he measurable_snd ref

def storedPi (i : Index P) (z : Past × Prefix d cut) : Point d :=
  storedPoint (store (V := V) P hR hc hsmall clock label hK hC hy z) ((batch).designated i)

include hV in
theorem storedPi_measurable (i : Index P) :
    Measurable (storedPi (V := V) P hR hc hsmall clock label hK hC hy i) :=
  store_measurable P hR hc hsmall clock label hK hC hy hV ((batch).designated i)

def storedParent (z : Past × Prefix d cut) : Point d :=
  storedPoint (store (V := V) P hR hc hsmall clock label hK hC hy z)
    ((cur).saved (ClockRetainedFinalSplice.parentRef P))

include hV in
theorem storedParent_measurable : Measurable (storedParent (V := V) P hR hc hsmall clock label hK hC hy) :=
  store_measurable P hR hc hsmall clock label hK hC hy hV ((cur).saved (ClockRetainedFinalSplice.parentRef P))

/-- Read the actual Pi together with its full consumed designated-child tape. -/
def observation (z : Past × Prefix d (afterBatch cut)) :
    (Point d × Point d) × (∀ i,DesignatedChildBatchCoupling.Raw d batch i) :=
  let parts := batchParts (d := d) cut z.2
  let old := (z.1,parts.1)
  (coarse P hR hc hsmall clock label hK hC hy old,fun i =>
    (comparison P hR hc hsmall clock label hK hC hy i old,
      (storedPi (V := V) P hR hc hsmall clock label hK hC hy i old,parts.2 i)))

include hV in
theorem observation_measurable : Measurable (observation (V := V) P hR hc hsmall clock label hK hC hy) := by
  have hp : Measurable (fun z : Past × Prefix d (afterBatch cut) => batchParts cut z.2) :=
    (measurable_batchParts (d := d) cut).comp measurable_snd
  have ho := measurable_fst.prodMk hp.fst
  exact ((coarse_measurable P hR hc hsmall clock label hK hC hy).comp ho).prodMk
    (Measurable.of_eval fun i =>
      (((comparison_measurable P hR hc hsmall clock label hK hC hy i).comp ho).prodMk
        (((storedPi_measurable P hR hc hsmall clock label hK hC hy hV i).comp ho).prodMk
          ((measurable_pi_apply i).comp hp.snd))))

/-- Finite same-source conditional at the actual designated batch. -/
def referenceConditional : Kernel (Past × Prefix d (afterBatch cut)) (Index P → Point d) :=
  (DesignatedChildBatchCoupling.referenceBatch L rfl batch J
    (center P clock hV hlo hup) (center_measurable P clock hV hlo hup)).comap
    (observation (V := V) P hR hc hsmall clock label hK hC hy)
    (observation_measurable P hR hc hsmall clock label hK hC hy hV)

instance referenceConditional_markov : IsMarkovKernel
    (referenceConditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) := by
  unfold referenceConditional
  infer_instance

/-- Actual full original source and every past coordinate are copied pointwise;
the conditional inspects no coordinate of the correction suffix. -/
def kernel : Kernel (Past × Tape d host) ((Past × Tape d host) × (Index P → Point d)) :=
  CausalTailHistory.onTape L (afterBatch cut)
    (referenceConditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean)

instance kernel_markov : IsMarkovKernel (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) := by
  unfold kernel
  infer_instance

theorem original_preserved : (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean).fst=Kernel.id :=
  CausalTailHistory.onTape_original L (afterBatch cut) _

/-- Exact finite retained-pair kernel at the correct (xF,Y0) datum. -/
def averagedPairs := DesignatedChildBatchJointTransfer.averagedPairs L rfl batch J
  (center P clock hV hlo hup) (center_measurable P clock hV hlo hup)

instance averagedPairs_markov : IsMarkovKernel (averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) := by
  unfold averagedPairs
  infer_instance

/-- Each original Pi and returned reference retain their actual lower joint. -/
theorem averagedPairs_apply (z : Point d × Point d) :
    averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean z =
      Measure.pi (fun i => ((ClockMeanChildAccuracy.finalKernel P hK hc hsmall hC hyMean hV hlo hup clock i)
        (center P clock hV hlo hup i z)).map (fun a => (a.1.1,a.2))) :=
  DesignatedChildBatchJointTransfer.averagedPairs_apply L rfl batch J
    (center P clock hV hlo hup) (center_measurable P clock hV hlo hup) z

/-- The full untouched correction tape stays fresh after final augmentation. -/
theorem whole_suffix (oldLaw : Measure (Past × Tape d host))
    (μ : Measure (Past × Prefix d cut)) [SFinite μ]
    (hsplit : oldLaw.map (CausalTailHistory.unpack cut)=
      μ.prod (tapeLaw L (.batch [] (DesignatedChildBatchCoupling.program batch)
        (suffix P hR hc hsmall clock label)))) :
    ((kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) ∘ₘ oldLaw).map (CausalTailHistory.unpackExtended (afterBatch cut))=
      ((advancedLaw L cut μ) ⊗ₘ (referenceConditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean)).prod
        (tapeLaw L (suffix P hR hc hsmall clock label)) :=
  CausalTailHistory.whole_suffix_fresh_of_split L (afterBatch cut) oldLaw
    (advancedLaw L cut μ) (advanced_split_of_split L cut oldLaw μ hsplit) _

/-- Observable pairs keep the actual Pi in the full original sample. -/
def retainedPairs (z : (Past × Tape d host) × (Index P → Point d)) :
    (Point d × Point d) × (Index P → Point d × Point d) :=
  let obs := observation (V := V) P hR hc hsmall clock label hK hC hy (z.1.1,(split (afterBatch cut) z.1.2).1)
  (obs.1,fun i => ((obs.2 i).2.1,z.2 i))

/-- Transfer of the exact chronological coarse/raw observation. The full
history and source survive; no independence conditional on momentum is used. -/
theorem retained_pairs_law (oldLaw : Measure (Past × Tape d host))
    (μ : Measure (Past × Prefix d cut)) [IsProbabilityMeasure μ]
    (hsplit : oldLaw.map (CausalTailHistory.unpack cut)=
      μ.prod (tapeLaw L (.batch [] (DesignatedChildBatchCoupling.program batch)
        (suffix P hR hc hsmall clock label))))
    (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν]
    (hprojection : (advancedLaw L cut μ).map (observation (V := V) P hR hc hsmall clock label hK hC hy)=
      ν.prod (Measure.pi (DesignatedChildBatchCoupling.rawLaw L batch))) :
    ((kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) ∘ₘ oldLaw).map (retainedPairs (V := V) P hR hc hsmall clock label hK hC hy)=
      ν ⊗ₘ averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean := by
  let _ : ∀ i,IsProbabilityMeasure (tapeLaw L (DesignatedChildBatchCoupling.program batch i)) :=
    fun i => tapeLaw_probability L _
  let _ : IsProbabilityMeasure (advancedLaw L cut μ) := by unfold advancedLaw; infer_instance
  have hw := whole_suffix P hR hc hsmall clock label hK hC hy hV hlo hup hyMean oldLaw μ hsplit
  have hp := FreshChildBatchErrorTransfer.full_sample_projection_preserving L (afterBatch cut) _ _ hw
  let obs := observation (V := V) P hR hc hsmall clock label hK hC hy
  have ho : Measurable obs := observation_measurable P hR hc hsmall clock label hK hC hy hV
  have hj := DesignatedChildBatchJointTransfer.observed_coarse_pairs L rfl batch J
    (center P clock hV hlo hup) (center_measurable P clock hV hlo hup)
    (advancedLaw L cut μ) ν obs ho hprojection
  have hm : Measurable (fun z : (Past × Prefix d (afterBatch cut)) × (Index P → Point d) =>
      ((obs z.1).1,fun i => (((obs z.1).2 i).2.1,z.2 i))) :=
    (ho.comp measurable_fst).fst.prodMk (Measurable.of_eval fun i =>
      (((measurable_pi_apply i).comp (ho.comp measurable_fst).snd).snd.fst.prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  have hf : MeasurePreserving
      (fun z : (Past × Prefix d (afterBatch cut)) × (Index P → Point d) =>
        ((obs z.1).1,fun i => (((obs z.1).2 i).2.1,z.2 i)))
      ((advancedLaw L cut μ) ⊗ₘ (referenceConditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean))
      (ν ⊗ₘ averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) := ⟨hm,hj⟩
  exact (hf.comp hp).map_eq

/-- Append the actual final batch to the actual finite main chronology. -/
def completedKernel := (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) ∘ₖ
  (ClockChronologicalCoupling.kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean)

instance completedKernel_markov : IsMarkovKernel (completedKernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) := by
  unfold completedKernel
  infer_instance

/-- The complete source input and whole original tape survive both the main
chronology and final augmentation, without any source-law premise. -/
theorem completed_original : (completedKernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean).map
    (fun z => ClockChronologicalCoupling.original P hR hc hsmall clock label z.1)=Kernel.id := by
  rw [completedKernel,Kernel.map_comp]
  change ((kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean).map
    ((ClockChronologicalCoupling.original P hR hc hsmall clock label) ∘ Prod.fst)) ∘ₖ _=Kernel.id
  rw [Kernel.map_comp_right _ measurable_fst (ClockChronologicalCoupling.original_measurable P hR hc hsmall clock label),
    ← Kernel.fst_eq,original_preserved,Kernel.id_map,Kernel.deterministic_comp_eq_map,
    ClockChronologicalCoupling.kernel_original]
  exact ClockChronologicalCoupling.original_measurable P hR hc hsmall clock label

end AcceleratedLogConcave.Root.ClockFinalBatchCoupling
