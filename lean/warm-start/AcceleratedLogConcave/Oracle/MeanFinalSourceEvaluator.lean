import AcceleratedLogConcave.Oracle.MeanFinalEvaluatorReadout
import AcceleratedLogConcave.Oracle.MeanFinalIntegratedError

/-! Canonical full source paid-final cut agrees with the existing executable
state/tape evaluator, on every original tape. No center accuracy is assumed. -/
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace AcceleratedLogConcave.Oracle.MeanFinalSourceEvaluator
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanLayer RecursiveMeanProgram
open RecursiveMeanContinuation SourceMeanExecutable TailOccurrenceCut TailCut
open MeanFinalEvaluatorReadout

private theorem split_trans_suffix {c d : ℕ} {Γ Δ Ξ : Ctx} {τ σ υ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} {r : Prog c Ξ υ}
    (inner : TailCut r q) (outer : TailCut q p) (ω : Tape d p) :
    (split (trans inner outer) ω).2 = (split inner (split outer ω).2).2 := by
  induction outer with
  | here => rfl
  | step o instr next cut ih => exact ih ω.2
  | batch o children next cut ih => exact ih ω.2

private theorem residual_value {c d : ℕ} {Γ : Ctx} (o : Origin)
    (G : Point d → Point d) (input : Inputs d c) (env : Env d Γ)
    (ω : Tape d (residualDraw (c := c) (Γ := Γ) o)) :
    (run (residualDraw o) G input env ω).value = ω.1 := rfl

variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
  (N : ℕ)
local notation "c" => (fun i => (main i).size)
local notation "p" => (fun i => (main i).program)
local notation "en" => (fun i => (main i).enumeration)
local notation "F" => SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling
local notation "host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling N
local notation "foc" => MeanFinalBatchCoupling.finishFocus M nodes anchors seeds main final sampling N
local notation "bc" => MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N

/-- Full actual final store, original references and entire paid suffix. -/
def sourceFocusedState (G : Point d → Point d)
    (input : Inputs d (size (a := a) main final sampling)) (ω : Tape d host) :
    FinalState (size (a := a) main final sampling) n d (SourceMeanExecutionRms.Ready n m h) .point F :=
  ⟨(foc).ctx,(foc).old,(foc).direct,(foc).saved,
    envAt G input (foc).cut Env.empty (split (foc).cut ω).1,(split (foc).cut ω).2⟩

/-- The source public rho entry identifies actual initialization rows. The
complete final state/tape then agrees with the existing body interpreter. -/
theorem sourceFocusedState_eq_state (r σ Ds δ t w : ℝ)
    (G : Point d → Point d) (x P : Point d) (ω : Tape d host) :
    sourceFocusedState M nodes anchors seeds main final sampling N G
      ⟨table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩ ω =
    SourceMeanExecutionRms.state M nodes anchors r σ Ds δ t w main final sampling N G x P
      (envAt G ⟨table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩ bc Env.empty (split bc ω).1)
      (split bc ω).2 := by
  let input : Inputs d (size (a := a) main final sampling) :=
    ⟨table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩
  let dirs : Fin n → Ref (replyCtx n (replyCtx n (SourceMeanExecutionRms.Ready n m h))) .point :=
    fun i => RefMap.shiftMany n (RefMap.shiftMany n (MeanExecutablePrefix.direct i))
  let saved : RefMap (SourceMeanExecutionRms.Ready n m h)
      (replyCtx n (replyCtx n (SourceMeanExecutionRms.Ready n m h))) :=
    fun ref => RefMap.shiftMany n (RefMap.shiftMany n ref)
  let f := atFinish c p (mainSlot (a := a) main final sampling) en layerOrigin mainDesignated residualOrigin
    (mainAuxiliary main) F N batchRef dirs saved
  let bi : TailCut (iterateThen c p (mainSlot (a := a) main final sampling) en layerOrigin mainDesignated residualOrigin
      (mainAuxiliary main) F N batchRef dirs saved)
      (body (a := a) (h := h) M nodes main final sampling N) := by
    unfold body NonterminalMeanBlock.code initializeCenters
    exact .batch _ _ _ (.batch _ _ _ .here)
  let hb : TailCut (F f.old f.direct f.saved) (body (a := a) (h := h) M nodes main final sampling N) :=
    trans f.cut bi
  have hcut : (foc).cut = trans hb bc := by rfl
  let bodyTape := (split bc ω).2
  let bodyEnv : Env d (SourceMeanExecutionRms.Ready n m h) :=
    envAt G input bc Env.empty (split bc ω).1
  let init : Env d (replyCtx n (replyCtx n (SourceMeanExecutionRms.Ready n m h))) :=
    SourceMeanExecutionRms.initialEnv M nodes r Ds main final sampling N bodyEnv bodyTape
  have hinit : @envAt _ _ _ _ _ G input _ _ _ bi bodyEnv (split bi bodyTape).1 = @init := by
    funext ty ref
    change Env.prepend (fun i => (run
      (initialRow (rhoSlot (a := a) main final sampling) MeanExecutablePrefix.direct i) G input
      (Env.prepend (fun i => (bodyTape.1 i).1) bodyEnv) (bodyTape.2.1 i)).value)
      (Env.prepend (fun i => (bodyTape.1 i).1) bodyEnv) ref = _
    have hrow (i : Fin n) := run_initialRow (rhoSlot (a := a) main final sampling)
      (fun j => (MeanExecutablePrefix.direct j : Ref (SourceMeanExecutionRms.Ready n m h) .point)) i
      G input bodyEnv (fun i => (bodyTape.1 i).1) (bodyTape.2.1 i)
    simp only [hrow,pointResult]
    change Env.prepend (fun i => storedPoint bodyEnv (MeanExecutablePrefix.direct i) +
      input.coefficient (rhoSlot (a := a) main final sampling) • (show Point d from (bodyTape.1 i).1))
      (Env.prepend (fun i => (bodyTape.1 i).1) bodyEnv) ref = _
    have ht : input.coefficient (rhoSlot (a := a) main final sampling) =
        RecursiveMeanPublicTable.centerNoise r M.R Ds :=
      table_rho M nodes anchors r σ Ds δ t w main final sampling
    rw [ht]
    rfl
  let ea : Env d f.ctx := envAt G input (trans hb bc) Env.empty (split (trans hb bc) ω).1
  let eb : Env d f.ctx := envAt G input f.cut init (split f.cut bodyTape.2.2).1
  have he : @ea = @eb := by
    funext ty ref
    dsimp only [ea,eb]
    rw [MeanFinalAssemblyReadout.envAt_trans_split]
    change envAt G input (trans f.cut bi) bodyEnv (split (trans f.cut bi) bodyTape).1 ref = _
    rw [MeanFinalAssemblyReadout.envAt_trans_split,hinit]
    rfl
  have ht : (split (trans hb bc) ω).2 = (split f.cut bodyTape.2.2).2 := by
    rw [split_trans_suffix,split_trans_suffix]
    rfl
  have hh := congrArg₂ (fun (e : Env d f.ctx) (tape : Tape d (F f.old f.direct f.saved)) =>
    (⟨f.ctx,f.old,f.direct,f.saved,e,tape⟩ : FinalState _ n d _ .point F)) he ht
  change sourceFocusedState M nodes anchors seeds main final sampling N G input ω = _
  rw [sourceFocusedState,hcut]
  change (⟨f.ctx,f.old,f.direct,f.saved,ea,(split (trans hb bc) ω).2⟩ : FinalState _ n d _ .point F) = _
  rw [hh]
  exact focusedState_eq_finalState c p (mainSlot (a := a) main final sampling) en layerOrigin mainDesignated residualOrigin
    (mainAuxiliary main) F G input N batchRef dirs saved init bodyTape.2.2

/-- The actual transformed lower-source tape is a readout of the complete
stored final state. Its residual coordinates are unchanged. -/
def finalTapeOfState (r Ds : ℝ)
    (st : FinalState (size (a := a) main final sampling) n d
      (SourceMeanExecutionRms.Ready n m h) .point F) (i : Fin m) : Tape d (final i).program :=
  let restored := restoreTape (finalSlot (a := a) main final sampling i)
    (compileWith (final i).program (final i).enumeration (finalAuxiliary final i))
    (fun q => nomatch q) (st.old (nodes.symm (.center M i)))
    (st.saved (MeanExecutablePrefix.designated i)) (st.tape.1 i)
  let v := unpackCompiledTape (final i).program (final i).enumeration (finalAuxiliary final i) restored
  transformedSourceTape (final i).program (final i).enumeration
    (CovarianceSetup.childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (r*M.R) (final i).shiftVector) v.1 v.2

/-- Literal final child tape read at the canonical full-source finish cut. -/
def sourceFinalTape (r Ds : ℝ) (G : Point d → Point d)
    (input : Inputs d (size (a := a) main final sampling)) (ω : Tape d host) (i : Fin m) :
    Tape d (final i).program :=
  finalTapeOfState M nodes main final sampling r Ds
    (sourceFocusedState M nodes anchors seeds main final sampling N G input ω) i

theorem sourceFinalTape_eq_finalTape (r σ Ds δ t w : ℝ)
    (G : Point d → Point d) (x P : Point d) (ω : Tape d host) (i : Fin m) :
    sourceFinalTape M nodes anchors seeds main final sampling N r Ds G
      ⟨table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩ ω i =
    SourceMeanExecutionRms.finalTape M nodes anchors r σ Ds δ t w main final sampling N G x P
      (envAt G ⟨table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩ bc Env.empty (split bc ω).1)
      (split bc ω).2 i := by
  unfold sourceFinalTape
  rw [sourceFocusedState_eq_state]
  rfl

/-- Actual stored Pi and the exact canonical paid-final tape, evaluated at an
arbitrary candidate center. In particular the candidate may be a benchmark. -/
def sourceFinalEvaluator (r Ds : ℝ) (G : Point d → Point d)
    (input : Inputs d (size (a := a) main final sampling)) (ω : Tape d host)
    (i : Fin m) (z : Point d) : Point d :=
  let st := sourceFocusedState M nodes anchors seeds main final sampling N G input ω
  RetainedMeanFinalBatch.childPoint (run (final i).program G
    ⟨(final i).coefficient,z,storedPoint st.env (st.saved (MeanExecutablePrefix.designated i))⟩
    Env.empty (sourceFinalTape M nodes anchors seeds main final sampling N r Ds G input ω i))

/-- The canonical full-source callback is the existing executable finalEvaluator
for every candidate center, with the same stored Pi and complete residual tape. -/
theorem sourceFinalEvaluator_eq_finalEvaluator (r σ Ds δ t w : ℝ)
    (G : Point d → Point d) (x P : Point d) (ω : Tape d host) (i : Fin m) (z : Point d) :
    sourceFinalEvaluator M nodes anchors seeds main final sampling N r Ds G
      ⟨table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩ ω i z =
    SourceMeanExecutionRms.finalEvaluator M nodes anchors r σ Ds δ t w main final sampling N G x P
      (envAt G ⟨table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩ bc Env.empty (split bc ω).1)
      (split bc ω).2 i z := by
  dsimp only [sourceFinalEvaluator]
  rw [sourceFocusedState_eq_state,sourceFinalTape_eq_finalTape]
  rw [SourceMeanExecutionRms.state_saved]
  rfl

variable (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (final i).shiftVector ≤ Ds^2)
local notation "B" => MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hmass
local notation "path" => MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass
variable {A H : Type*} [MeasurableSpace A] [MeasurableSpace H]
  (G : Point d → Point d) (input : A → Inputs d (size (a := a) main final sampling))
  (coarse : A × Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass) → H)
  (comparison : Fin m → A × Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass) → Point d)
  (center : Fin m → H → Point d) (u : Fin m → H → Point d) (width : ℝ)

omit [MeasurableSpace A] [MeasurableSpace H] in
/-- The integrated payment's source error is the existing final callback read
at the canonical source cut. The supplied candidate remains the benchmark;
there is no assertion that it equals the true stored iterate. -/
theorem sourceError_eq_sourceFinalEvaluator (sample : A) (ω : Tape d host)
    (ref : Fin m → Point d) (i : Fin m) :
    DesignatedChildBatchBenchmarkError.sourceError B center
      (MeanFinalBatchCoupling.observation M nodes anchors seeds main final sampling N r Ds hr hDs hmass
        G input coarse comparison) i G (u i) width
      ((sample,(split (PrivateCausalLayer.afterBatch path) ω).1),ref) =
    sourceFinalEvaluator M nodes anchors seeds main final sampling N r Ds G (input sample) ω i
      (center i (coarse (sample,(split path ω).1)) +
        RecursiveMeanPublicTable.centerNoise r M.R Ds • comparison i (sample,(split path ω).1)) -
      (u i (coarse (sample,(split path ω).1)) + width • ref i) := by
  simp only [DesignatedChildBatchBenchmarkError.sourceError,MeanFinalBatchCoupling.observation,
    PrivateCausalLayer.split_afterBatch,PrivateCausalLayer.batchParts_append]
  rfl

end AcceleratedLogConcave.Oracle.MeanFinalSourceEvaluator
