import AcceleratedLogConcave.Oracle.PrivateCausalAdvance
import AcceleratedLogConcave.Oracle.PrivateInitialComparison
import AcceleratedLogConcave.Oracle.PrivateRecursiveBatchCoupling
import AcceleratedLogConcave.Oracle.PrivateConditionalFlowConsumer
import AcceleratedLogConcave.Numerics.SmoothConditional

/-! Finite chronological reference augmentation on the original private tape.
The returned vectors are recorded in their executed layer slots. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.PrivateChronologicalCoupling
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceExecutableTables
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance

local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

abbrev History (d N n : ℕ) :=
  ((Point d × Point d) × Point d) × ((Fin N → Fin n → Point d) × (Fin n → Point d))

section Syntax
variable {m n : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)

abbrev Host : Program (samplingSize main final) .point :=
  (SamplingExecutable.build S e r Ds main final N).program

abbrev Loop {Γ : Ctx} (remaining : ℕ) (old direct : Fin n → Ref Γ .point)
    (saved : RefMap (PrivateSamplingExecutionSchedule.Entry n) Γ) :
    Prog (samplingSize main final) Γ .point :=
  iterateThen (fun i => (main i).size) (fun i => (main i).program)
    (samplingConfig main final N).mainSlots (fun i => (main i).enumeration)
    (samplingConfig main final N).layerOrigin (samplingConfig main final N).mainDesignated
    (samplingConfig main final N).mainResidual (samplingConfig main final N).mainAuxiliary
    (PrivateSamplingExecutionSchedule.finisher main final N) remaining old direct saved

structure Cursor where
  remaining : ℕ
  ctx : Ctx
  old : Fin n → Ref ctx .point
  direct : Fin n → Ref ctx .point
  saved : RefMap (PrivateSamplingExecutionSchedule.Entry n) ctx
  cut : TailCut (Loop main final N remaining old direct saved) (Host S e r Ds main final N)

/-- The actual four setup instructions and three initialization batches are
consumed. This constructor also exists when the main loop has zero layers. -/
def entry : Cursor S e r Ds main final N where
  remaining := N
  ctx := replyCtx n (replyCtx n (PrivateSamplingExecutionSchedule.Entry n))
  old := batchRef
  direct i := RefMap.shiftMany n (RefMap.shiftMany n (batchRef i))
  saved q := RefMap.shiftMany n (RefMap.shiftMany n q)
  cut := by
    change TailCut _ (PrivateSamplingProgram.code (samplingConfig main final N))
    unfold PrivateSamplingProgram.code PrivateSamplingProgram.body initializeCenters
    exact .step _ _ _ (.step _ _ _ (.step _ _ _ (.step _ _ _
      (.batch _ _ _ (.batch _ _ _ (.batch _ _ _ .here))))))

def focus (s : Cursor S e r Ds main final N) (hs : 0 < s.remaining) :
    GeneralMainFocus.Focus (fun i => (main i).size) (fun i => (main i).program)
      (samplingConfig main final N).mainSlots (fun i => (main i).enumeration)
      (samplingConfig main final N).layerOrigin (samplingConfig main final N).mainDesignated
      (samplingConfig main final N).mainResidual (samplingConfig main final N).mainAuxiliary
      (PrivateSamplingExecutionSchedule.finisher main final N) (Host S e r Ds main final N) where
  remainingAfter := s.remaining-1
  ctx := s.ctx
  old := s.old
  direct := s.direct
  saved := s.saved
  cut := by rw [Nat.sub_add_cancel hs]; exact s.cut

def advance (s : Cursor S e r Ds main final N) (hs : 0 < s.remaining) :
    Cursor S e r Ds main final N where
  remaining := s.remaining-1
  ctx := nextCtx n s.ctx
  old := batchRef
  direct i := preserveDirect (s.direct i)
  saved q := preserveDirect (s.saved q)
  cut := afterLayer (fun i => (main i).size) (fun i => (main i).program)
    (samplingConfig main final N).mainSlots (fun i => (main i).enumeration)
    (samplingConfig main final N).layerOrigin (samplingConfig main final N).mainDesignated
    (samplingConfig main final N).mainResidual (samplingConfig main final N).mainAuxiliary
    (PrivateSamplingExecutionSchedule.finisher main final N)
    (s.remaining-1) s.old s.direct s.saved (focus S e r Ds main final N s hs).cut

/-- Every stage follows the same actual full program. The final cursor has
zero remaining layers and points at the unchanged paid finish. -/
def stage : (k : ℕ) → (hk : k ≤ N) →
    {s : Cursor S e r Ds main final N // s.remaining = N-k}
  | 0, _ => ⟨entry S e r Ds main final N,by simp [entry]⟩
  | k+1, hk =>
      let s := stage k (by omega)
      ⟨advance S e r Ds main final N s.1 (by rw [s.2]; omega),by
        change s.1.remaining-1 = N-(k+1)
        rw [s.2]
        omega⟩

theorem stage_remaining (k : ℕ) (hk : k ≤ N) :
    (stage S e r Ds main final N k hk).1.remaining = N-k := (stage S e r Ds main final N k hk).2

def terminalCursor : Cursor S e r Ds main final N :=
  (stage S e r Ds main final N N le_rfl).1

@[simp] theorem terminal_remaining :
    (terminalCursor S e r Ds main final N).remaining = 0 := by
  exact (stage_remaining S e r Ds main final N N le_rfl).trans (Nat.sub_self N)

/-- The reached cut targets the original paid finish with the actual stored
references produced by the finite loop, for every N including zero. -/
def terminalCut : TailCut
    (PrivateSamplingExecutionSchedule.finisher main final N
      (terminalCursor S e r Ds main final N).old
      (terminalCursor S e r Ds main final N).direct
      (terminalCursor S e r Ds main final N).saved) (Host S e r Ds main final N) := by
  have h := (terminalCursor S e r Ds main final N).cut
  rw [terminal_remaining] at h
  exact h

def terminalFocus : FinishFocus (PrivateSamplingExecutionSchedule.finisher main final N)
    (Host S e r Ds main final N) :=
  ⟨(terminalCursor S e r Ds main final N).ctx,(terminalCursor S e r Ds main final N).old,
    (terminalCursor S e r Ds main final N).direct,(terminalCursor S e r Ds main final N).saved,
    terminalCut S e r Ds main final N⟩

end Syntax

section JointCenter
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  {r : ℝ} (hr : 0 < r)

def flowData : SamplingCenterLp.Data (Fin d) :=
  ⟨F,hF,ell,hell,hlo,hup,r,hr,samplingEnd S.τ,S.samplingEnd_pos.le,S.samplingEnd_lt_one⟩

/-- The actual source center, jointly in the external center and setup draw.
The frozen first coordinate of the joint ODE supplies joint measurability. -/
def jointPhi (i : Fin n) (z : Point d × Point d) : Point d :=
  z.1 + (r*S.mesh.location m (e i)) •
    (ConditionalSmoothing.jointPath (flowData S hF hell hlo hup hr)
      (S.mesh.location m (e i)) z).2

theorem jointPhi_continuous (i : Fin n) :
    Continuous (jointPhi S e hF hell hlo hup hr i) := by
  have hp : Continuous (fun z : Point d × Point d =>
      ConditionalSmoothing.jointPath (flowData S hF hell hlo hup hr)
        (S.mesh.location m (e i)) z) :=
    (ConditionalSmoothing.continuous_jointPath (flowData S hF hell hlo hup hr)).comp
      (continuous_const.prodMk continuous_id)
  exact continuous_fst.add (hp.snd.const_smul (r*S.mesh.location m (e i)))

theorem jointPhi_eq_nodePhi (i : Fin n) (x ζ : Point d) :
    jointPhi S e hF hell hlo hup hr i (x,ζ) =
      PrivateConditionalFlowConsumer.nodePhi S e hF hell hlo hup x hr i ζ := by
  have ht := S.mesh.location_mem_interval m (e i)
  rw [jointPhi,ConditionalSmoothing.jointPath_snd_eq_source _ x ζ ⟨ht.1.le,ht.2.le⟩]
  rfl
end JointCenter

section ConstructedStep
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)

/-- Actual occurrence data at a cursor reached by finite execution. No
comparison law or parent accuracy conclusion is included in this record. -/
def data (s : Cursor S e r Ds main final N) (_hs : 0<s.remaining) :
    FreshChildBatchCoupling.Data n (samplingSize main final) s.ctx where
  child := main
  slot i := (samplingConfig main final N).mainSlots ∘
    childSlot (fun i => (main i).size) (fun i => (main i).program) i
  old := s.old
  designated := (samplingConfig main final N).mainDesignated (s.remaining-1)
  auxiliary := (samplingConfig main final N).mainAuxiliary (s.remaining-1)
  rho _ := samplingNoise S r Ds
  radius i := S.radius r (e i)
  Ds := Ds
  rho_nonneg _ := (RecursiveExecutableDomain.sampling_noise_pos S r Ds hr hDs).le
  radius_pos i := S.radius_pos r hr (e i)
  Ds_pos := hDs
  shift_budget := hmass
  small i := RecursiveExecutableDomain.sampling_noise_separation S r Ds hr hDs (e i)

def next (s : Cursor S e r Ds main final N) :
    Prog (samplingSize main final) (replyCtx n s.ctx) .point :=
  .batch [] (fun j => residualDraw ((samplingConfig main final N).mainResidual (s.remaining-1) j))
    (.batch [] (noisyRow
      (fun j l => (samplingConfig main final N).mainSlots
        (aSlot (fun i => (main i).size) (fun i => (main i).program) j l))
      (fun j l => (samplingConfig main final N).mainSlots
        (residualSlot (fun i => (main i).size) (fun i => (main i).program) j l)) s.direct)
      (Loop main final N (s.remaining-1) batchRef
        (fun j => preserveDirect (s.direct j)) (fun q => preserveDirect (s.saved q))))

def batchCut (s : Cursor S e r Ds main final N) (hs : 0<s.remaining) :
    TailCut (.batch ((samplingConfig main final N).layerOrigin (s.remaining-1))
      (FreshChildBatchCoupling.program (data S e r Ds main final N hr hDs hmass s hs))
      (next S e r Ds main final N s)) (Host S e r Ds main final N) :=
  (focus S e r Ds main final N s hs).cut

local instance cursorPrefixSpace (s : Cursor S e r Ds main final N) (hs : 0<s.remaining) :
    MeasurableSpace (Prefix d (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))) :=
  prefixSpace d _

def observation (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (z : History d N n × Prefix d (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))) :
    (Point d × Point d) ×
      (∀ i, FreshChildBatchCoupling.Raw d (data S e r Ds main final N hr hDs hmass s hs) i) :=
  (z.1.1.1,fun i => (z.1.2.2 i,
    (batchParts (batchCut S e r Ds main final N hr hDs hmass s hs) z.2).2 i))

theorem observation_measurable (s : Cursor S e r Ds main final N) (hs : 0<s.remaining) :
    Measurable (observation (d := d) S e r Ds main final N hr hDs hmass s hs) := by
  have hb := (measurable_batchParts (d := d)
    (batchCut S e r Ds main final N hr hDs hmass s hs)).comp
      (measurable_snd : Measurable (Prod.snd : History d N n × _ → _))
  exact measurable_fst.fst.fst.prodMk (Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst.snd.snd).prodMk
      ((measurable_pi_apply i).comp hb.snd))

variable (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)

def conditional (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs)) :
    Kernel (History d N n × Prefix d (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)))
      (Fin n → Point d) :=
  (FreshChildBatchCoupling.referenceBatch L hL
    (data S e r Ds main final N hr hDs hmass s hs) J
    (jointPhi S e hF hell hlo hup hr)
    (fun i => (jointPhi_continuous S e hF hell hlo hup hr i).measurable)).comap
      (observation S e r Ds main final N hr hDs hmass s hs)
      (observation_measurable S e r Ds main final N hr hDs hmass s hs)

instance conditional_markov (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs)) :
    IsMarkovKernel (conditional S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J) := by
  unfold conditional
  infer_instance

def adjoin (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs)) :
    Kernel (History d N n × Tape d (Host S e r Ds main final N))
      ((History d N n × Tape d (Host S e r Ds main final N)) × (Fin n → Point d)) :=
  CausalTailHistory.onTape L (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))
    (conditional S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J)

instance adjoin_markov (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs)) :
    IsMarkovKernel (adjoin S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J) := by
  unfold adjoin
  infer_instance

theorem adjoin_original (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs)) :
    (adjoin S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J).fst = Kernel.id :=
  CausalTailHistory.onTape_original L _ _

/-- The record update reads the current source residual after the child
batch. All original coordinates, including the designated parent, are copied. -/
def record (s : Cursor S e r Ds main final N) (hs : 0<s.remaining) (k : Fin N)
    (z : (History d N n × Tape d (Host S e r Ds main final N)) × (Fin n → Point d)) :
    History d N n × Tape d (Host S e r Ds main final N) :=
  ((z.1.1.1,(Function.update z.1.1.2.1 k z.2,
    nextComparison S e r Ds z.2 (fun i =>
      ((split (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)) z.1.2).2.1 i).1))),z.1.2)

include L in
theorem record_measurable (s : Cursor S e r Ds main final N) (hs : 0<s.remaining) (k : Fin N) :
    Measurable (record (d := d) S e r Ds main final N hr hDs hmass s hs k) := by
  have hsplit := (measurePreserving_split L
    (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))).measurable.comp
      (measurable_fst.snd : Measurable
        (fun z : (History d N n × Tape d (Host S e r Ds main final N)) ×
          (Fin n → Point d) => z.1.2))
  have hres : Measurable (fun z : (History d N n × Tape d (Host S e r Ds main final N)) ×
      (Fin n → Point d) => fun i : Fin n =>
        ((split (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)) z.1.2).2.1 i).1) :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp hsplit.snd.fst).fst
  have hu : Measurable (fun z : (History d N n × Tape d (Host S e r Ds main final N)) ×
      (Fin n → Point d) => Function.update z.1.1.2.1 k z.2) := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i=k
    · subst i; simpa only [Function.update_self] using measurable_snd
    · have hm : Measurable (fun z : (History d N n × Tape d (Host S e r Ds main final N)) ×
          (Fin n → Point d) => z.1.1.2.1 i) := by fun_prop
      simpa only [Function.update_of_ne hi] using hm
  exact (measurable_fst.fst.fst.prodMk (hu.prodMk
    ((nextComparison_measurable S e r Ds).comp (measurable_snd.prodMk hres)))).prodMk
      measurable_fst.snd

def step (s : Cursor S e r Ds main final N) (hs : 0<s.remaining) (k : Fin N)
    (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs)) :
    Kernel (History d N n × Tape d (Host S e r Ds main final N))
      (History d N n × Tape d (Host S e r Ds main final N)) :=
  (adjoin S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J).map
    (record S e r Ds main final N hr hDs hmass s hs k)

instance step_markov (s : Cursor S e r Ds main final N) (hs : 0<s.remaining) (k : Fin N)
    (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs)) :
    IsMarkovKernel (step S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs k J) := by
  unfold step
  exact Kernel.IsMarkovKernel.map _ (record_measurable S e r Ds main final N hr hDs hmass L s hs k)

def original (z : History d N n × Tape d (Host S e r Ds main final N)) :
    (Point d × Point d) × Tape d (Host S e r Ds main final N) :=
  ((z.1.1.1.1,z.1.1.2),z.2)

theorem original_measurable : Measurable (original (d := d) S e r Ds main final N) :=
  (measurable_fst.fst.fst.fst.prodMk measurable_fst.fst.snd).prodMk measurable_snd

theorem step_original (s : Cursor S e r Ds main final N) (hs : 0<s.remaining) (k : Fin N)
    (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs)) :
    (step S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs k J).map
      (original S e r Ds main final N) =
        Kernel.deterministic (original S e r Ds main final N)
          (original_measurable S e r Ds main final N) := by
  rw [step,← Kernel.map_comp_right _
    (record_measurable S e r Ds main final N hr hDs hmass L s hs k)
    (original_measurable S e r Ds main final N)]
  change (adjoin S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J).map
    ((original S e r Ds main final N) ∘ Prod.fst) = _
  rw [Kernel.map_comp_right _ measurable_fst (original_measurable S e r Ds main final N),
    ← Kernel.fst_eq,adjoin_original,Kernel.id_map]

/-- The only probabilistic induction input is a lower standalone retained
coupling. Its Gaussian reference marginal follows from the exact recursive
reference identity at the original potential and actual lower parameters. -/
def recursiveLower (G : MeanGeometry m) (hm : 0<m) (t : ℝ) (ht : 0<t)
    (q : Fin n → ℝ) (theta : Fin n → Point d → Conditional.SourceParameters (Point d) ell)
    (joint : ∀ i, Kernel (Point d) ((Point d × Tape d (main i).program) × Point d))
    (hmarkov : ∀ i, IsMarkovKernel (joint i))
    (hsource : ∀ i, (joint i).fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw L (main i).program))
    (hretained : ∀ i x, (joint i x).map (fun z => (z.1.1,z.2)) =
      stdGaussian (Point d) ⊗ₘ
        (Conditional.RecursiveReference.referenceFamily hF hell hlo hup G hm t ht (q i)).kernel.comap
          (fun v => (theta i x,v)) measurable_prodMk_left)
    (s : Cursor S e r Ds main final N) (hs : 0<s.remaining) :
    FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs) :=
  FreshChildBatchCoupling.Lower.ofRecursiveReference L
    (data S e r Ds main final N hr hDs hmass s hs) hF hell hlo hup G hm t ht
      q theta joint hmarkov hsource hretained

end ConstructedStep

section PrefixUpdate
variable {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty} {p : Prog c Γ τ} {q : Prog c Δ σ}
  {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  (L : PrimitiveLaws d) (cut : TailCut q p)
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut

def changeHistory (f : A × Prefix d cut → B) (z : A × Tape d p) : B × Tape d p :=
  (f (z.1,(split cut z.2).1),z.2)

def changePrefix (f : A × Prefix d cut → B) (z : A × Prefix d cut) : B × Prefix d cut :=
  (f z,z.2)

include L in
theorem changeHistory_measurable (f : A × Prefix d cut → B) (hf : Measurable f) :
    Measurable (changeHistory cut f) :=
  (hf.comp (CausalTailHistory.measurable_unpack L cut).fst).prodMk measurable_snd

theorem changePrefix_measurable (f : A × Prefix d cut → B) (hf : Measurable f) :
    Measurable (changePrefix cut f) := hf.prodMk measurable_snd

/-- Updating only the consumed augmented past preserves the complete actual
unread suffix as a single fresh factor. -/
theorem changeHistory_split (f : A × Prefix d cut → B) (hf : Measurable f)
    (ρ : Measure (A × Tape d p)) (μ : Measure (A × Prefix d cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw L q)) :
    (ρ.map (changeHistory cut f)).map (CausalTailHistory.unpack cut) =
      (μ.map (changePrefix cut f)).prod (tapeLaw L q) := by
  let : IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q
  have hm := (changePrefix_measurable cut f hf).prodMap
    (measurable_id : Measurable (id : Tape d q → Tape d q))
  have h := congrArg (fun ν => ν.map (Prod.map (changePrefix cut f) id)) hsplit
  rw [Measure.map_map hm (CausalTailHistory.measurable_unpack L cut),
    ← Measure.map_prod_map _ _ (changePrefix_measurable cut f hf) measurable_id,
    Measure.map_id] at h
  rw [Measure.map_map (CausalTailHistory.measurable_unpack L cut)
    (changeHistory_measurable L cut f hf)]
  exact h
end PrefixUpdate

section GenericHistory
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (N : ℕ)

def updateHistory (k : Fin N)
    (z : (History d N n × (Fin n → Point d)) × (Fin n → Point d)) : History d N n :=
  (z.1.1.1,(Function.update z.1.1.2.1 k z.1.2,nextComparison S e r Ds z.1.2 z.2))

theorem updateHistory_measurable (k : Fin N) :
    Measurable (updateHistory (d := d) S e r Ds N k) := by
  have hv : Measurable (fun z : (History d N n × (Fin n → Point d)) × (Fin n → Point d) =>
      z.1.1.2.1) := measurable_fst.fst.snd.fst
  have hg : Measurable (fun z : (History d N n × (Fin n → Point d)) × (Fin n → Point d) =>
      z.1.2) := measurable_fst.snd
  have hu := (measurable_update' (X := fun _ : Fin N => Fin n → Point d) (a := k)).comp (hv.prodMk hg)
  have hn := (nextComparison_measurable (d := d) S e r Ds).comp (hg.prodMk measurable_snd)
  exact measurable_fst.fst.fst.prodMk (hu.prodMk hn)


end GenericHistory

section StepSuffix
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)

def layerCut := afterBatch (afterBatch (afterBatch
  (batchCut S e r Ds main final N hr hDs hmass s hs)))

local instance : MeasurableSpace
    (Prefix d (layerCut S e r Ds main final N hr hDs hmass s hs)) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)))) := prefixSpace d _

def residualPrefix (h : Prefix d (layerCut S e r Ds main final N hr hDs hmass s hs)) :
    Fin n → Point d :=
  let rows := batchParts (afterBatch (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))) h
  let noise := batchParts (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)) rows.1
  fun i => (noise.2 i).1

theorem residualPrefix_measurable :
    Measurable (residualPrefix (d := d) S e r Ds main final N hr hDs hmass s hs) := by
  have hrows := measurable_batchParts (d := d)
    (afterBatch (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)))
  have hn := (measurable_batchParts (d := d)
    (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))).comp hrows.fst
  exact Measurable.of_eval fun i => ((measurable_pi_apply i).comp hn.snd).fst

def recordPast (k : Fin N)
    (z : (History d N n × (Fin n → Point d)) ×
      Prefix d (layerCut S e r Ds main final N hr hDs hmass s hs)) : History d N n :=
  updateHistory S e r Ds N k
    (z.1,residualPrefix S e r Ds main final N hr hDs hmass s hs z.2)

theorem recordPast_measurable (k : Fin N) :
    Measurable (recordPast (d := d) S e r Ds main final N hr hDs hmass s hs k) := by
  exact (updateHistory_measurable S e r Ds N k).comp (measurable_fst.prodMk
    ((residualPrefix_measurable S e r Ds main final N hr hDs hmass s hs).comp measurable_snd))

theorem changeHistory_record (k : Fin N) :
    changeHistory (layerCut S e r Ds main final N hr hDs hmass s hs)
      (recordPast (d := d) S e r Ds main final N hr hDs hmass s hs k) ∘
        regroupOriginal = record S e r Ds main final N hr hDs hmass s hs k := by
  funext z
  simp only [Function.comp_def,changeHistory,recordPast,regroupOriginal,record,
    updateHistory,residualPrefix,layerCut,split_afterBatch,batchParts_append]

variable (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs))

local instance : MeasurableSpace
    (Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs)) := prefixSpace d _

def returnedPrefixLaw
    (μ : Measure (History d N n × Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs))) :
    Measure ((History d N n × (Fin n → Point d)) ×
      Prefix d (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))) :=
  (((advancedLaw L (batchCut S e r Ds main final N hr hDs hmass s hs) μ) ⊗ₘ
    conditional S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J).map
      (regroupPrefix (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))))

instance returnedPrefixLaw_sFinite
    (μ : Measure (History d N n × Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs)))
    [SFinite μ] :
    SFinite (returnedPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ) := by
  unfold returnedPrefixLaw
  infer_instance

def nextPrefixLaw (k : Fin N)
    (μ : Measure (History d N n × Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs))) :
    Measure (History d N n × Prefix d (layerCut S e r Ds main final N hr hDs hmass s hs)) :=
  (advancedLaw L (afterBatch (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)))
    (advancedLaw L (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))
      (returnedPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ))).map
            (changePrefix (layerCut S e r Ds main final N hr hDs hmass s hs)
              (recordPast S e r Ds main final N hr hDs hmass s hs k))

instance nextPrefixLaw_sFinite (k : Fin N)
    (μ : Measure (History d N n × Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs)))
    [SFinite μ] :
    SFinite (nextPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J k μ) := by
  have hret : SFinite (returnedPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ) :=
    returnedPrefixLaw_sFinite S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ
  have hres : SFinite (advancedLaw L (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))
      (returnedPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ)) :=
    advancedLaw_sFinite L _ _
  have hrows : SFinite (advancedLaw L (afterBatch (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)))
      (advancedLaw L (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))
        (returnedPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ))) :=
    advancedLaw_sFinite L _ _
  unfold nextPrefixLaw
  infer_instance

/-- A concrete executed step preserves the complete next unread suffix.
Only the entering actual cut factorization is assumed; old augmented history,
the consumed prefix, and the parent momentum may correlate arbitrarily. -/
theorem step_whole_suffix (k : Fin N)
    (ρ : Measure (History d N n × Tape d (Host S e r Ds main final N)))
    (μ : Measure (History d N n × Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs)))
    [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (batchCut S e r Ds main final N hr hDs hmass s hs)) =
      μ.prod (tapeLaw L (.batch ((samplingConfig main final N).layerOrigin (s.remaining-1))
        (FreshChildBatchCoupling.program (data S e r Ds main final N hr hDs hmass s hs))
        (next S e r Ds main final N s)))) :
    (step S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs k J ∘ₘ ρ).map
      (CausalTailHistory.unpack (layerCut S e r Ds main final N hr hDs hmass s hs)) =
        (nextPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J k μ).prod
          (tapeLaw L (Loop main final N (s.remaining-1) batchRef
            (fun j => preserveDirect (s.direct j)) (fun q => preserveDirect (s.saved q)))) := by
  have hc := CausalTailHistory.whole_suffix_fresh_of_split L
    (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)) ρ
    (advancedLaw L (batchCut S e r Ds main final N hr hDs hmass s hs) μ)
    (advanced_split_of_split L (batchCut S e r Ds main final N hr hDs hmass s hs) ρ μ hsplit)
    (conditional S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J)
  have hg := regroup_cut_law L (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))
    _ _ hc
  have hn := consume_two_batches L (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))
    _ _ hg
  have hret : SFinite (returnedPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ) :=
    returnedPrefixLaw_sFinite S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ
  have hres : SFinite (advancedLaw L (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))
      (returnedPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ)) :=
    advancedLaw_sFinite L _ _
  have hrows : SFinite (advancedLaw L (afterBatch (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)))
      (advancedLaw L (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))
        (returnedPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ))) :=
    advancedLaw_sFinite L _ _
  have hh := changeHistory_split L (layerCut S e r Ds main final N hr hDs hmass s hs)
    (recordPast S e r Ds main final N hr hDs hmass s hs k)
    (recordPast_measurable S e r Ds main final N hr hDs hmass s hs k) _
      (advancedLaw L (afterBatch (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)))
        (advancedLaw L (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))
          (returnedPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J μ))) hn
  rw [Measure.map_map
    (changeHistory_measurable L _ _ (recordPast_measurable S e r Ds main final N hr hDs hmass s hs k))
      regroupOriginal_measurable,changeHistory_record] at hh
  rw [step,← Measure.map_comp _ _ (record_measurable S e r Ds main final N hr hDs hmass L s hs k)]
  exact hh

/-- The same advance stated at the actual entering and reached cursors.
Destructing the positive remaining count discharges the target transport;
no equality with a separately regenerated focus is assumed. -/
theorem step_cursor_whole_suffix (k : Fin N)
    (ρ : Measure (History d N n × Tape d (Host S e r Ds main final N))) :
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    let : MeasurableSpace (Prefix d (advance S e r Ds main final N s hs).cut) := prefixSpace d _
    ∀ (μ : Measure (History d N n × Prefix d s.cut)) [SFinite μ],
    ρ.map (CausalTailHistory.unpack s.cut) =
      μ.prod (tapeLaw L (Loop main final N s.remaining s.old s.direct s.saved)) →
    ∃ (ν : Measure (History d N n × Prefix d (advance S e r Ds main final N s hs).cut)),
      SFinite ν ∧
      (step S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs k J ∘ₘ ρ).map
        (CausalTailHistory.unpack (advance S e r Ds main final N s hs).cut) =
          ν.prod (tapeLaw L (Loop main final N (s.remaining-1) batchRef
            (fun j => preserveDirect (s.direct j)) (fun q => preserveDirect (s.saved q)))) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      dsimp only
      intro μ _ hsplit
      let s : Cursor S e r Ds main final N := ⟨remaining+1,ctx,old,direct,saved,cut⟩
      refine ⟨nextPrefixLaw S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J k μ,
        nextPrefixLaw_sFinite S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J k μ,?_⟩
      exact step_whole_suffix S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J k ρ μ hsplit
end StepSuffix

section Finite
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)

theorem stage_positive (k : ℕ) (hk : k<N) :
    0 < (stage S e r Ds main final N k hk.le).1.remaining := by
  rw [stage_remaining]
  omega

variable
  (J : ∀ (k : ℕ) (hk : k<N), FreshChildBatchCoupling.Lower L
    (data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk)))

/-- Exactly the first k actual main layers. A lower-child coupling is
requested only for an executed index k<N; the zero-layer case is identity. -/
def iteration : (k : ℕ) → (hk : k≤N) →
    Kernel (History d N n × Tape d (Host S e r Ds main final N))
      (History d N n × Tape d (Host S e r Ds main final N))
  | 0, _ => Kernel.id
  | k+1, hk =>
      (step S e r Ds main final N hr hDs hmass L hL hF hell hlo hup
        (stage S e r Ds main final N k (by omega)).1
        (stage_positive S e r Ds main final N k (by omega))
        ⟨k,by omega⟩ (J k (by omega))) ∘ₖ
          iteration k (by omega)

instance iteration_markov (k : ℕ) (hk : k≤N) :
    IsMarkovKernel (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk) := by
  induction k with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ k ih =>
      have := ih (by omega)
      dsimp only [iteration]
      infer_instance

/-- Every finite stage preserves the joint external center, original parent
momentum, and entire original mixed tape, without a law premise. -/
theorem iteration_original (k : ℕ) (hk : k≤N) :
    (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk).map
      (original S e r Ds main final N) =
        Kernel.deterministic (original S e r Ds main final N)
          (original_measurable S e r Ds main final N) := by
  induction k with
  | zero => exact Kernel.id_map (original_measurable S e r Ds main final N)
  | succ k ih =>
      rw [iteration,Kernel.map_comp,step_original,Kernel.deterministic_comp_eq_map]
      exact ih (by omega)

theorem iteration_preserves_original (k : ℕ) (hk : k≤N)
    (μ : Measure (History d N n × Tape d (Host S e r Ds main final N))) :
    (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk ∘ₘ μ).map
      (original S e r Ds main final N) = μ.map (original S e r Ds main final N) := by
  rw [Measure.map_comp _ _ (original_measurable S e r Ds main final N),
    iteration_original,Measure.deterministic_comp_eq_map]

def initializeState (z : Point d × (Point d × Tape d (Host S e r Ds main final N))) :
    History d N n × Tape d (Host S e r Ds main final N) :=
  let ω := z.2.2
  ((((z.1,ω.2.1),z.2.1),((fun _ => 0),fun i => (ω.2.2.2.2.2.1 i).1)),ω)

theorem initializeState_measurable : Measurable (initializeState (d := d) S e r Ds main final N) := by
  unfold initializeState
  fun_prop

/-- Initialization draws the full original mixed standalone seed once. Its
actual setup position and initializeStater occurrences supply the initial history. -/
def initial : Kernel (Point d) (History d N n × Tape d (Host S e r Ds main final N)) :=
  (Kernel.id ×ₖ Kernel.const (Point d)
    (FreshChildRetainedCoupling.sourceLaw L (Host S e r Ds main final N))).map
      (initializeState S e r Ds main final N)

instance initial_markov : IsMarkovKernel (initial S e r Ds main final N L) := by
  unfold initial
  exact Kernel.IsMarkovKernel.map _ (initializeState_measurable S e r Ds main final N)

local instance : MeasurableSpace (Prefix d (entry S e r Ds main final N).cut) := prefixSpace d _

def initialPast (z : (Point d × Point d) × Prefix d (entry S e r Ds main final N).cut) :
    History d N n :=
  let h := z.2
  (((z.1.1,h.2.1),z.1.2),((fun _ => 0),fun i => (h.2.2.2.2.2.1 i).1))

theorem initialPast_measurable : Measurable (initialPast (d := d) S e r Ds main final N) := by
  unfold initialPast
  fun_prop

def initialPrefixLaw (x : Point d) :
    Measure (History d N n × Prefix d (entry S e r Ds main final N).cut) :=
  (((Measure.dirac x).prod L.pointDraw).prod
    (prefixLaw L (entry S e r Ds main final N).cut)).map
      (changePrefix (entry S e r Ds main final N).cut (initialPast S e r Ds main final N))

instance initialPrefixLaw_probability (x : Point d) :
    IsProbabilityMeasure (initialPrefixLaw S e r Ds main final N L x) := by
  let _ : IsProbabilityMeasure L.pointDraw := L.point_probability
  let _ : IsProbabilityMeasure (prefixLaw L (entry S e r Ds main final N).cut) :=
    prefixLaw_probability L _
  unfold initialPrefixLaw
  infer_instance

/-- The literal initial history depends only on the four setup instructions
and three initialization batches, including when N=0. -/
theorem initial_eq_history_update (x : Point d) :
    initial S e r Ds main final N L x =
      ((((Measure.dirac x).prod L.pointDraw).prod (tapeLaw L (Host S e r Ds main final N))).map
        (changeHistory (entry S e r Ds main final N).cut (initialPast S e r Ds main final N))) := by
  let _ : IsProbabilityMeasure (tapeLaw L (Host S e r Ds main final N)) := tapeLaw_probability L _
  let _ : IsProbabilityMeasure L.pointDraw := L.point_probability
  rw [initial,Kernel.map_apply _ (initializeState_measurable S e r Ds main final N),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,FreshChildRetainedCoupling.sourceLaw,
    ← Measure.prodAssoc_prod,
    Measure.map_map (initializeState_measurable S e r Ds main final N) MeasurableEquiv.prodAssoc.measurable]
  rfl

theorem initial_whole_suffix (x : Point d) :
    (initial S e r Ds main final N L x).map
      (CausalTailHistory.unpack (entry S e r Ds main final N).cut) =
        (initialPrefixLaw S e r Ds main final N L x).prod
          (tapeLaw L (Loop main final N N
            batchRef (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
            (fun q => RefMap.shiftMany n (RefMap.shiftMany n q)))) := by
  let _ : IsProbabilityMeasure L.pointDraw := L.point_probability
  let _ : IsProbabilityMeasure (prefixLaw L (entry S e r Ds main final N).cut) := prefixLaw_probability L _
  let _ : IsProbabilityMeasure (tapeLaw L (Loop main final N N
      batchRef (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
      (fun q => RefMap.shiftMany n (RefMap.shiftMany n q)))) := tapeLaw_probability L _
  let _ : IsProbabilityMeasure (tapeLaw L (Host S e r Ds main final N)) := tapeLaw_probability L _
  let _ : IsProbabilityMeasure (tapeLaw L (Loop main final N (entry S e r Ds main final N).remaining
    (entry S e r Ds main final N).old (entry S e r Ds main final N).direct (entry S e r Ds main final N).saved)) :=
      tapeLaw_probability L _
  have hp := ((measurePreserving_prodAssoc ((Measure.dirac x).prod L.pointDraw)
    (prefixLaw L (entry S e r Ds main final N).cut) _).symm).comp
      ((MeasurePreserving.id ((Measure.dirac x).prod L.pointDraw)).prod
        (measurePreserving_split L (entry S e r Ds main final N).cut))
  rw [initial_eq_history_update]
  exact changeHistory_split L (entry S e r Ds main final N).cut
    (initialPast S e r Ds main final N) (initialPast_measurable S e r Ds main final N)
    _ _ hp.map_eq

theorem initial_original (x : Point d) :
    ((initial S e r Ds main final N L) x).map (original S e r Ds main final N) =
      (FreshChildRetainedCoupling.sourceLaw L (Host S e r Ds main final N)).map
        (fun z => ((x,z.1),z.2)) := by
  rw [initial,Kernel.map_apply _ (initializeState_measurable S e r Ds main final N),
    Measure.map_map (original_measurable S e r Ds main final N)
      (initializeState_measurable S e r Ds main final N),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map ((original_measurable S e r Ds main final N).comp
      (initializeState_measurable S e r Ds main final N)) measurable_prodMk_left]
  rfl

/-- The constructed full finite chronological coupling, jointly measurable
in its external center. Only executed lower-child couplings are used. -/
def kernel : Kernel (Point d) (History d N n × Tape d (Host S e r Ds main final N)) :=
  iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J N le_rfl ∘ₖ
    initial S e r Ds main final N L

instance kernel_markov : IsMarkovKernel
    (kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J) := by
  unfold kernel
  infer_instance

theorem kernel_original (x : Point d) :
    (kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x).map
      (original S e r Ds main final N) =
        (FreshChildRetainedCoupling.sourceLaw L (Host S e r Ds main final N)).map
          (fun z => ((x,z.1),z.2)) := by
  rw [← Kernel.map_apply _ (original_measurable S e r Ds main final N),kernel,
    Kernel.map_comp,iteration_original,Kernel.deterministic_comp_eq_map,
    Kernel.map_apply _ (original_measurable S e r Ds main final N)]
  exact initial_original S e r Ds main final N L x

/-- The whole unread source suffix remains fresh at every reached stage of
the constructed finite kernel. This includes the paid finish at stage N. -/
theorem iteration_whole_suffix (k : ℕ) (hk : k≤N) (x : Point d) :
    let s := (stage S e r Ds main final N k hk).1
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∃ (μ : Measure (History d N n × Prefix d s.cut)), SFinite μ ∧
      (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk ∘ₘ
        initial S e r Ds main final N L x).map (CausalTailHistory.unpack s.cut) =
          μ.prod (tapeLaw L (Loop main final N s.remaining s.old s.direct s.saved)) := by
  induction k with
  | zero =>
      refine ⟨initialPrefixLaw S e r Ds main final N L x,?_,?_⟩
      · let _ := initialPrefixLaw_probability S e r Ds main final N L x
        infer_instance
      simpa only [iteration,stage,entry,Measure.id_comp] using initial_whole_suffix S e r Ds main final N L x
  | succ k ih =>
      obtain ⟨μ,hμ,hcut⟩ := ih (by omega)
      let s := (stage S e r Ds main final N k (by omega)).1
      have hs : 0<s.remaining := stage_positive S e r Ds main final N k (by omega)
      let _ : SFinite μ := hμ
      obtain ⟨ν,hν,hνcut⟩ := step_cursor_whole_suffix S e r Ds main final N hr hDs hmass
        s hs L hL hF hell hlo hup (J k (by omega)) ⟨k,by omega⟩
        (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k (by omega) ∘ₘ
          initial S e r Ds main final N L x) μ hcut
      refine ⟨ν,hν,?_⟩
      simpa only [iteration,stage,s,advance,← Measure.comp_assoc] using hνcut

theorem kernel_whole_suffix (x : Point d) :
    let s := terminalCursor S e r Ds main final N
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∃ (μ : Measure (History d N n × Prefix d s.cut)), SFinite μ ∧
      (kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x).map
        (CausalTailHistory.unpack s.cut) =
          μ.prod (tapeLaw L (Loop main final N s.remaining s.old s.direct s.saved)) := by
  simpa only [kernel,Kernel.comp_apply,terminalCursor] using
    iteration_whole_suffix S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J N le_rfl x

end Finite
end AcceleratedLogConcave.Oracle.PrivateChronologicalCoupling
