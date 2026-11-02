import AcceleratedLogConcave.Root.ClockMeanChildAccuracy
import AcceleratedLogConcave.Root.ClockRetainedWholeTapeLaw
import AcceleratedLogConcave.Root.OuterRootOriginalData
import AcceleratedLogConcave.Oracle.PrivateCausalAdvance
import AcceleratedLogConcave.Numerics.SmoothConditional

/-! Chronological augmentation of the literal retained-final Clock program.
The current main batch uses full standalone lower seeds; its comparison
coordinates are returned references, rather than designated source draws. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockChronologicalCoupling
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open Oracle.TailOccurrenceCut Oracle.PrivateCausalLayer Oracle.PrivateCausalAdvance
open TailCut
open Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockNoisyLayer Numerics
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ)

def Host : Program (ClockRetainedFinalSplice.size P hR hc hsmall clock) .point := ClockRetainedFinalSplice.code P hR hc hsmall clock label
def Loop {Γ : Ctx} (remaining : ℕ) (old direct : Index P → Ref Γ .point)
    (saved : RefMap (ClockRetainedFinalSplice.entryCtx P) Γ) :
    Prog (ClockRetainedFinalSplice.size P hR hc hsmall clock) Γ .point :=
  iterateThen (c P hR hc hsmall clock) (p P hR hc hsmall clock)
    (ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock) (e P hR hc hsmall clock) (fun _ => [])
    (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
    (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
    (ClockRetainedFinalSplice.finish P hR hc hsmall clock label) remaining old direct saved

structure Cursor where
  remaining : ℕ
  ctx : Ctx
  old : Index P → Ref ctx .point
  direct : Index P → Ref ctx .point
  saved : RefMap (ClockRetainedFinalSplice.entryCtx P) ctx
  cut : TailCut (Loop P hR hc hsmall clock label remaining old direct saved)
    (Host P hR hc hsmall clock label)

def entry : Cursor P hR hc hsmall clock label where
  remaining := P.K+4
  ctx := ClockRetainedFinalSplice.entryCtx P
  old := ClockRetainedFinalSplice.oldRef P
  direct := ClockRetainedFinalSplice.directRef P
  saved q := q
  cut := by
    unfold Host ClockRetainedFinalSplice.code ClockRetainedFinalSplice.assembled
      MeanGaussianSetup.setup ClockRetainedFinalSplice.initialized initializeCenters
    exact .step _ _ _ (.step _ _ _ (.step _ _ _ (.batch _ _ _ (.batch _ _ _
      (.batch _ _ _ (.batch _ _ _ (.batch _ _ _ (.batch _ _ _ .here))))))))

def focus (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    GeneralMainFocus.Focus (c P hR hc hsmall clock) (p P hR hc hsmall clock)
      (ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock) (e P hR hc hsmall clock) (fun _ => [])
      (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
      (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
      (ClockRetainedFinalSplice.finish P hR hc hsmall clock label) (Host P hR hc hsmall clock label) where
  remainingAfter := s.remaining-1
  ctx := s.ctx
  old := s.old
  direct := s.direct
  saved := s.saved
  cut := by rw [Nat.sub_add_cancel hs]; exact s.cut

def advance (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    Cursor P hR hc hsmall clock label where
  remaining := s.remaining-1
  ctx := nextCtx (N P) s.ctx
  old := batchRef
  direct i := preserveDirect (s.direct i)
  saved q := preserveDirect (s.saved q)
  cut := afterLayer (c P hR hc hsmall clock) (p P hR hc hsmall clock)
    (ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock) (e P hR hc hsmall clock) (fun _ => [])
    (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
    (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
    (ClockRetainedFinalSplice.finish P hR hc hsmall clock label)
    (s.remaining-1) s.old s.direct s.saved (focus P hR hc hsmall clock label s hs).cut

def stage : (k : ℕ) → (hk : k≤P.K+4) →
    {s : Cursor P hR hc hsmall clock label // s.remaining=P.K+4-k}
  | 0,_ => ⟨entry P hR hc hsmall clock label,by simp [entry]⟩
  | k+1,hk =>
    let s := stage k (by omega)
    ⟨advance P hR hc hsmall clock label s.1 (by rw [s.2]; omega),by
      change s.1.remaining-1=P.K+4-(k+1)
      rw [s.2]; omega⟩

theorem stage_remaining (k : ℕ) (hk : k≤P.K+4) :
    (stage P hR hc hsmall clock label k hk).1.remaining=P.K+4-k :=
  (stage P hR hc hsmall clock label k hk).2

def terminalCursor := (stage P hR hc hsmall clock label (P.K+4) le_rfl).1
@[simp] theorem terminal_remaining : (terminalCursor P hR hc hsmall clock label).remaining=0 :=
  (stage_remaining P hR hc hsmall clock label (P.K+4) le_rfl).trans (Nat.sub_self _)

def terminalCut : TailCut
    (ClockRetainedFinalSplice.finish P hR hc hsmall clock label
      (terminalCursor P hR hc hsmall clock label).old
      (terminalCursor P hR hc hsmall clock label).direct
      (terminalCursor P hR hc hsmall clock label).saved) (Host P hR hc hsmall clock label) := by
  have h := (terminalCursor P hR hc hsmall clock label).cut
  rw [terminal_remaining] at h
  exact h

variable (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)

def data (s : Cursor P hR hc hsmall clock label) (_hs : 0<s.remaining) :
    FreshChildBatchCoupling.Data (N P) (ClockRetainedFinalSplice.size P hR hc hsmall clock) s.ctx where
  child := child P hR hc hsmall clock
  slot i := ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock ∘
    childSlot (c P hR hc hsmall clock) (p P hR hc hsmall clock) i
  old := s.old
  designated := ClockRepeatedLayers.designated P (P.K+4) (s.remaining-1)
  auxiliary := ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4) (s.remaining-1)
  rho _ := rhoC P
  radius i := radius P clock i
  Ds := P.Ds
  rho_nonneg _ := (rhoC_pos P).le
  radius_pos i := radius_pos P clock i
  Ds_pos := P.Ds_pos
  shift_budget i := (OuterMainStability.main_queryShift_and_mass P hK hc hsmall hC hy (N P) i clock).2
  small i := rhoC_le_radius P clock i

def next (s : Cursor P hR hc hsmall clock label) :
    Prog (ClockRetainedFinalSplice.size P hR hc hsmall clock) (replyCtx (N P) s.ctx) .point :=
  .batch [] (fun j => residualDraw (ClockRepeatedLayers.residual P (P.K+4) (s.remaining-1) j))
    (.batch [] (noisyRow
      (fun j l => ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock (aSlot (c P hR hc hsmall clock) (p P hR hc hsmall clock) j l))
      (fun j l => ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock (residualSlot (c P hR hc hsmall clock) (p P hR hc hsmall clock) j l)) s.direct)
      (Loop P hR hc hsmall clock label (s.remaining-1) batchRef
        (fun j => preserveDirect (s.direct j)) (fun q => preserveDirect (s.saved q))))

def batchCut (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    TailCut (.batch [] (FreshChildBatchCoupling.program (data P hR hc hsmall clock label hK hC hy s hs))
      (next P hR hc hsmall clock label s)) (Host P hR hc hsmall clock label) :=
  (focus P hR hc hsmall clock label s hs).cut

/-- Actual full child table, including its unchanged original coefficients. -/
theorem data_table (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) (i : Index P) :
    ClockRetainedFinalSplice.table P hR hc hsmall clock ∘
      (data P hR hc hsmall clock label hK hC hy s hs).slot i =
      matrixTable (CovarianceSetup.childRoot (rhoC P) (radius P clock i)
        (shiftVector P hR hc hsmall clock i)) (coeff P hR hc hsmall clock i) := by
  funext j
  change ClockRetainedFinalSplice.table P hR hc hsmall clock
    (ClockRetainedFinalSplice.oldSlot P hR hc hsmall clock
      (ClockRepeatedLayers.slots P hR hc hsmall clock (childSlot _ _ i j))) = _
  rw [ClockRetainedFinalSplice.table_old]
  change (ClockPublicSetup.table P hR hc hsmall clock ∘ ClockRepeatedLayers.slots P hR hc hsmall clock) (childSlot _ _ i j) = _
  rw [ClockRepeatedLayers.table_slots]
  exact table_child P hR hc hsmall clock i j



variable {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)

/-- Concrete main lower joints from the already constructed precision recursion. -/
def lower (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    FreshChildBatchCoupling.Lower (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
      (data P hR hc hsmall clock label hK hC hy s hs) where
  joint i := ClockMeanChildAccuracy.mainKernel P hK hc hsmall hC hyMean hV hlo hup clock i
  markov i := ClockMeanChildAccuracy.main_markov P hK hc hsmall hC hyMean hV hlo hup clock i
  source i := ClockMeanChildAccuracy.main_source P hK hc hsmall hC hyMean hV hlo hup clock i
  reference i x := FreshChildBatchCoupling.recursive_reference_marginal _ _ _ _ _ _ _ _ _ _ _ _
    ((ClockMeanChildAccuracy.mainLaw P hK hc hsmall hC hyMean hV hlo hup clock i).retained x)

abbrev Base (d : ℕ) := (Point d × Point d) × (Point d × (Index P → Point d))
abbrev History (d : ℕ) := Base P d × ((Fin (P.K+4) → Index P → Point d) × (Index P → Point d))

/-- The actual conditional root-flow center at its literal Clock node. -/
def center (i : Index P) (z : Base P d) : Point d :=
  z.1.1 + (ClockCollocation.rF P.delta * ClockCollocation.u P.delta P.K clock i) •
    (ConditionalSmoothing.jointPath (OuterRootOriginalData.data hV P.delta_pos hlo hup)
      (ClockCollocation.u P.delta P.K clock i)
      (z.1.1,ClockPublicSetup.splitValues z.1.2 z.2.1 0)).2

theorem center_measurable (i : Index P) :
    Measurable (center P clock hV hlo hup i) := by
  have hb : Measurable (fun z : Base P d => (z.1.1,ClockPublicSetup.splitValues z.1.2 z.2.1 0)) := by
    simp only [ClockPublicSetup.splitValues,Matrix.cons_val_zero]
    fun_prop
  have hp : Measurable (fun z : Base P d =>
      ConditionalSmoothing.jointPath (OuterRootOriginalData.data hV P.delta_pos hlo hup)
        (ClockCollocation.u P.delta P.K clock i)
        (z.1.1,ClockPublicSetup.splitValues z.1.2 z.2.1 0)) :=
    (ConditionalSmoothing.continuous_jointPath
      (OuterRootOriginalData.data hV P.delta_pos hlo hup)).measurable.comp
        (show Measurable (fun z : Base P d =>
          (ClockCollocation.u P.delta P.K clock i,(z.1.1,ClockPublicSetup.splitValues z.1.2 z.2.1 0))) from
          measurable_const.prodMk hb)
  exact measurable_fst.fst.add
    (hp.snd.const_smul (ClockCollocation.rF P.delta * ClockCollocation.u P.delta P.K clock i))

/-- The jointly measurable formula is the original conditional source path,
with the same actual split draw and original center. -/
theorem center_eq_source (i : Index P) (z : Base P d) :
    center P clock hV hlo hup i z =
      z.1.1 + (ClockCollocation.rF P.delta * ClockCollocation.u P.delta P.K clock i) •
        SamplingCenterLp.path (OuterRootOriginalData.data hV P.delta_pos hlo hup) z.1.1
          (ClockCollocation.u P.delta P.K clock i) (ClockPublicSetup.splitValues z.1.2 z.2.1 0) := by
  unfold center
  have hu := ClockCollocation.u_mem P.delta_pos P.K clock i
  rw [ConditionalSmoothing.jointPath_snd_eq_source _ _ _ ⟨hu.1,hu.2.trans clock.2.2⟩]

/-- Initialization reads only the actual public split draw and center-init array.
The entire original tape, including raw assembly and every final seed, remains. -/
def prepare (z : (Point d × Point d) × Tape d (Host P hR hc hsmall clock label)) :
    History P d × Tape d (Host P hR hc hsmall clock label) :=
  let w := ClockRetainedFinalSplice.wholeTapeEquiv P hR hc hsmall clock d label z.2
  (((z.1,(w.1,w.2.1)),(fun _ _ => 0,w.2.2.1)),z.2)

theorem prepare_measurable : Measurable (prepare (d := d) P hR hc hsmall clock label) := by
  let : MeasurableSpace (ClockRetainedFinalSplice.MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    ClockRetainedWholeTapeLaw.mainFinalSpace P hR hc hsmall clock label
  have hw := (ClockRetainedWholeTapeLaw.wholeTapeMeasurableEquiv P hR hc hsmall clock label
    (d := d)).measurable.comp
      (measurable_snd : Measurable (Prod.snd : (Point d × Point d) × Tape d (Host P hR hc hsmall clock label) → _))
  exact ((measurable_fst.prodMk (hw.fst.prodMk hw.snd.fst)).prodMk (measurable_const.prodMk hw.snd.snd.fst)).prodMk measurable_snd

def observation (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
    (z : History P d × Prefix d (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))) :
    Base P d × (∀ i,FreshChildBatchCoupling.Raw d (data P hR hc hsmall clock label hK hC hy s hs) i) :=
  (z.1.1,fun i => (z.1.2.2 i,
    (batchParts (batchCut P hR hc hsmall clock label hK hC hy s hs) z.2).2 i))

local instance cursorPrefixSpace (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    MeasurableSpace (Prefix d (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))) := prefixSpace d _

theorem observation_measurable (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    Measurable (observation (d := d) P hR hc hsmall clock label hK hC hy s hs) := by
  have hb := (measurable_batchParts (d := d) (batchCut P hR hc hsmall clock label hK hC hy s hs)).comp
    (measurable_snd : Measurable (Prod.snd : History P d × _ → _))
  exact measurable_fst.fst.prodMk (Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst.snd.snd).prodMk
      ((measurable_pi_apply i).comp hb.snd))

def conditional (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    Kernel (History P d × Prefix d (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)))
      (Index P → Point d) :=
  (FreshChildBatchCoupling.referenceBatch (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl
    (data P hR hc hsmall clock label hK hC hy s hs)
    (lower P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs)
    (fun i => center P clock hV hlo hup i) (center_measurable P clock hV hlo hup)).comap
      (observation P hR hc hsmall clock label hK hC hy s hs)
      (observation_measurable P hR hc hsmall clock label hK hC hy s hs)

instance conditional_markov (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    IsMarkovKernel (conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs) := by
  unfold conditional
  infer_instance



def adjoin (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    Kernel (History P d × Tape d (Host P hR hc hsmall clock label))
      ((History P d × Tape d (Host P hR hc hsmall clock label)) × (Index P → Point d)) :=
  CausalTailHistory.onTape (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
    (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)) (conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs)

instance adjoin_markov (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    IsMarkovKernel (adjoin P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs) := by unfold adjoin; infer_instance

theorem adjoin_original (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) :
    (adjoin P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs).fst=Kernel.id :=
  CausalTailHistory.onTape_original (Probability.CanonicalNativeTapeLaw.primitiveLaws d) _ _

/-- The next comparison uses the returned main reference array and the
literal untouched source residual array. -/
def comparisonUpdate (gz : (Index P → Point d) × (Index P → Point d)) : Index P → Point d :=
  ResidualGaussianRecombination.recombine (A P clock) (rhoC P) (a P) gz

theorem comparisonUpdate_measurable : Measurable (comparisonUpdate (d := d) P clock) :=
  ResidualGaussianRecombination.recombine_measurable _ _ _

/-- All reference/residual comparison coordinates form a full fresh Gaussian
vector after the literal covariance recombination. -/
theorem comparisonUpdate_preserving :
    MeasurePreserving (comparisonUpdate (d := d) P clock)
      ((Measure.pi fun _ : Index P => stdGaussian (Point d)).prod
        (Measure.pi fun _ : Index P => stdGaussian (Point d)))
      (Measure.pi fun _ : Index P => stdGaussian (Point d)) := by
  apply ResidualGaussianRecombination.recombine_preserving (A P clock) (rhoC_pos P) (a_pos P)
  intro i
  exact ClockCollocation.sum_abs_matrix_le_quarter P.delta P.delta_pos P.K clock
    (0 : Point d) (0 : Point d) i

def record (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) (k : Fin (P.K+4))
    (z : (History P d × Tape d (Host P hR hc hsmall clock label)) × (Index P → Point d)) :
    History P d × Tape d (Host P hR hc hsmall clock label) :=
  ((z.1.1.1,(Function.update z.1.1.2.1 k z.2,
    comparisonUpdate P clock (z.2,fun i =>
      ((split (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)) z.1.2).2.1 i).1))),z.1.2)

theorem record_measurable (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) (k : Fin (P.K+4)) :
    Measurable (record (d := d) P hR hc hsmall clock label hK hC hy s hs k) := by
  have hsplit := (measurePreserving_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
    (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))).measurable.comp
      (measurable_fst.snd : Measurable
        (fun z : (History P d × Tape d (Host P hR hc hsmall clock label)) × (Index P → Point d) => z.1.2))
  have hres : Measurable (fun z : (History P d × Tape d (Host P hR hc hsmall clock label)) × (Index P → Point d) =>
      fun i : Index P => ((split (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)) z.1.2).2.1 i).1) :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp hsplit.snd.fst).fst
  have hu : Measurable (fun z : (History P d × Tape d (Host P hR hc hsmall clock label)) × (Index P → Point d) =>
      Function.update z.1.1.2.1 k z.2) := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i=k
    · subst i; simpa only [Function.update_self] using measurable_snd
    · have hm : Measurable (fun z : (History P d × Tape d (Host P hR hc hsmall clock label)) × (Index P → Point d) =>
          z.1.1.2.1 i) := by fun_prop
      simpa only [Function.update_of_ne hi] using hm
  exact (measurable_fst.fst.fst.prodMk (hu.prodMk
    ((comparisonUpdate_measurable P clock).comp (measurable_snd.prodMk hres)))).prodMk measurable_fst.snd

def step (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) (k : Fin (P.K+4)) :
    Kernel (History P d × Tape d (Host P hR hc hsmall clock label)) (History P d × Tape d (Host P hR hc hsmall clock label)) :=
  (adjoin P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs).map (record P hR hc hsmall clock label hK hC hy s hs k)

instance step_markov (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) (k : Fin (P.K+4)) :
    IsMarkovKernel (step P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k) := by
  unfold step
  exact Kernel.IsMarkovKernel.map _ (record_measurable P hR hc hsmall clock label hK hC hy s hs k)

def original (z : History P d × Tape d (Host P hR hc hsmall clock label)) : (Point d × Point d) × Tape d (Host P hR hc hsmall clock label) :=
  (z.1.1.1,z.2)

theorem original_measurable : Measurable (original (d := d) P hR hc hsmall clock label) :=
  measurable_fst.fst.fst.prodMk measurable_snd

theorem step_original (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) (k : Fin (P.K+4)) :
    (step P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k).map (original P hR hc hsmall clock label) =
      Kernel.deterministic (original P hR hc hsmall clock label) (original_measurable P hR hc hsmall clock label) := by
  rw [step,← Kernel.map_comp_right _ (record_measurable P hR hc hsmall clock label hK hC hy s hs k) (original_measurable P hR hc hsmall clock label)]
  change (adjoin P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs).map ((original P hR hc hsmall clock label) ∘ Prod.fst) = _
  rw [Kernel.map_comp_right _ measurable_fst (original_measurable P hR hc hsmall clock label),
    ← Kernel.fst_eq,adjoin_original,Kernel.id_map]

theorem stage_positive (k : ℕ) (hk : k<P.K+4) :
    0<(stage P hR hc hsmall clock label k hk.le).1.remaining := by rw [stage_remaining]; omega

/-- Actual finite chronology; no child is demanded after the final main layer. -/
def iteration : (k : ℕ) → (hk : k≤P.K+4) →
    Kernel (History P d × Tape d (Host P hR hc hsmall clock label)) (History P d × Tape d (Host P hR hc hsmall clock label))
  | 0,_ => Kernel.id
  | k+1,hk =>
    (step P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (stage P hR hc hsmall clock label k (by omega)).1
      (stage_positive P hR hc hsmall clock label k (by omega)) ⟨k,by omega⟩) ∘ₖ iteration k (by omega)

instance iteration_markov (k : ℕ) (hk : k≤P.K+4) :
    IsMarkovKernel (iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k hk) := by
  induction k with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ k ih =>
    have := ih (by omega)
    dsimp only [iteration]
    infer_instance

theorem iteration_original (k : ℕ) (hk : k≤P.K+4) :
    (iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k hk).map (original P hR hc hsmall clock label) =
      Kernel.deterministic (original P hR hc hsmall clock label) (original_measurable P hR hc hsmall clock label) := by
  induction k with
  | zero => exact Kernel.id_map (original_measurable P hR hc hsmall clock label)
  | succ k ih =>
    rw [iteration,Kernel.map_comp,step_original,Kernel.deterministic_comp_eq_map]
    exact ih (by omega)

/-- Concrete retained Clock main-loop coupling. All lower joints come from the
prescribed recursive source law, jointly in the actual conditional-flow center. -/
def kernel : Kernel ((Point d × Point d) × Tape d (Host P hR hc hsmall clock label))
    (History P d × Tape d (Host P hR hc hsmall clock label)) :=
  iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (P.K+4) le_rfl ∘ₖ
    Kernel.deterministic (prepare P hR hc hsmall clock label) (prepare_measurable P hR hc hsmall clock label)

instance kernel_markov : IsMarkovKernel (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean) := by unfold kernel; infer_instance

/-- Exact original input and complete original canonical tape projection. -/
theorem kernel_original : (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean).map (original P hR hc hsmall clock label)=Kernel.id := by
  rw [kernel,Kernel.map_comp,iteration_original,Kernel.deterministic_comp_eq_map,
    Kernel.deterministic_map (prepare_measurable P hR hc hsmall clock label) (original_measurable P hR hc hsmall clock label)]
  change Kernel.deterministic id _=Kernel.id
  rfl

end AcceleratedLogConcave.Root.ClockChronologicalCoupling
