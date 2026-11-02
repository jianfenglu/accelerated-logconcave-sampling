import AcceleratedLogConcave.Oracle.PrivateChronologicalCoupling
import AcceleratedLogConcave.Oracle.PrivateSamplingRetainedRms
import AcceleratedLogConcave.Oracle.MeanFinalEvaluatorReadout
import AcceleratedLogConcave.Oracle.ReplaySeedMeasurability

/-! Exact full-source private final state and callback readouts at the reached
chronological cut. These identities preserve the original designated seed and
all residual coordinates, for every finite horizon including zero. -/
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace AcceleratedLogConcave.Oracle.PrivateFinalEvaluatorReadout
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanLayer RecursiveMeanProgram
open RecursiveMeanContinuation TailOccurrenceCut TailCut PrivateCausalLayer PrivateCausalAdvance
open PrivateChronologicalCoupling ReplaySeedMeasurability
private theorem residual_value {C D : ℕ} {Γ : Ctx} (o : Origin)
    (G : Point D → Point D) (input : Inputs D C) (env : Env D Γ)
    (ω : Tape D (residualDraw (c := C) (Γ := Γ) o)) :
    (run (residualDraw o) G input env ω).value = ω.1 := rfl

private theorem envAt_trans {C D : ℕ} {Γ Δ Ξ : Ctx} {τ σ υ : Ty}
    {p : Prog C Γ τ} {q : Prog C Δ σ} {r : Prog C Ξ υ}
    (inner : TailCut r q) (outer : TailCut q p)
    (G : Point D → Point D) (input : Inputs D C) (env : Env D Γ) (ω : Tape D p) :
    @envAt _ _ _ _ _ G input _ _ _ (trans inner outer) env (split (trans inner outer) ω).1 =
      @envAt _ _ _ _ _ G input _ _ _ inner (envAt G input outer env (split outer ω).1)
        (split inner (split outer ω).2).1 := by
  funext ty ref
  exact MeanFinalAssemblyReadout.envAt_trans_split inner outer G input env ω ref

private theorem split_trans_suffix {C D : ℕ} {Γ Δ Ξ : Ctx} {τ σ υ : Ty}
    {p : Prog C Γ τ} {q : Prog C Δ σ} {r : Prog C Ξ υ}
    (inner : TailCut r q) (outer : TailCut q p) (ω : Tape D p) :
    (split (trans inner outer) ω).2 = (split inner (split outer ω).2).2 := by
  induction outer with
  | here => rfl
  | step o instr next path ih => exact ih ω.2
  | batch o children next path ih => exact ih ω.2

variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
local notation "cfg" => SourceExecutableTables.samplingConfig main final N
local notation "c" => (fun i => (main i).size)
local notation "p" => (fun i => (main i).program)
local notation "en" => (fun i => (main i).enumeration)
local notation "F" => PrivateSamplingExecutionSchedule.finisher main final N
local notation "host" => Host S e r Ds main final N

/-- Finish the unconsumed part of the exact source tape at any reached cursor. -/
def completedState (G : Point d → Point d) (input : Inputs d (SourceExecutableTables.samplingSize main final))
    (s : Cursor S e r Ds main final N) (ω : Tape d host) :
    FinalState (SourceExecutableTables.samplingSize main final) n d
      (PrivateSamplingExecutionSchedule.Entry n) .point F :=
  finalState c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual
    (cfg).mainAuxiliary F G input s.remaining s.old s.direct s.saved
    (envAt G input s.cut Env.empty (split s.cut ω).1) (split s.cut ω).2

/-- Consuming one actual child/residual/row layer changes no final result,
store, saved reference, or paid-final tape. -/
theorem completedState_advance (G : Point d → Point d)
    (input : Inputs d (SourceExecutableTables.samplingSize main final))
    (s : Cursor S e r Ds main final N) (hs : 0 < s.remaining) (ω : Tape d host) :
    completedState S e r Ds main final N G input (advance S e r Ds main final N s hs) ω =
      completedState S e r Ds main final N G input s ω := by
  rcases s with ⟨remaining,ctx,old,direct,saved,path⟩
  cases remaining with
  | zero => exact False.elim ((Nat.lt_irrefl 0) hs)
  | succ k =>
    change finalState c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual
      (cfg).mainAuxiliary F G input k batchRef (fun i => preserveDirect (direct i))
      (fun q => preserveDirect (saved q))
      (envAt G input (afterLayer c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated
        (cfg).mainResidual (cfg).mainAuxiliary F k old direct saved path) Env.empty
        (split (afterLayer c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated
          (cfg).mainResidual (cfg).mainAuxiliary F k old direct saved path) ω).1)
      (split (afterLayer c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated
        (cfg).mainResidual (cfg).mainAuxiliary F k old direct saved path) ω).2 =
      finalState c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual
        (cfg).mainAuxiliary F G input (k+1) old direct saved
        (envAt G input path Env.empty (split path ω).1) (split path ω).2
    dsimp only [Loop] at path
    simp only [afterLayer,afterBatch,envAt_trans,split_trans_suffix]
    
    dsimp only [envAt,split,finalState]
    simp only [residual_value,run_noisyRow,pointResult]

/-- Finite chronological consumption agrees with the same initial execution,
without identifying the true stored center with a benchmark. -/
theorem completedState_stage (G : Point d → Point d)
    (input : Inputs d (SourceExecutableTables.samplingSize main final))
    (ω : Tape d host) (k : ℕ) (hk : k ≤ N) :
    completedState S e r Ds main final N G input (stage S e r Ds main final N k hk).1 ω =
      completedState S e r Ds main final N G input (entry S e r Ds main final N) ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change completedState S e r Ds main final N G input
      (advance S e r Ds main final N (stage S e r Ds main final N k (by omega)).1 _) ω = _
    rw [completedState_advance]
    exact ih (by omega)

/-- The reached initial cursor uses exactly the setup and two initializer
batches in the existing full-tape interpreter. -/
theorem completedState_entry_eq_state (G : Point d → Point d)
    (input : Inputs d (SourceExecutableTables.samplingSize main final)) (ω : Tape d host) :
    completedState S e r Ds main final N G input (entry S e r Ds main final N) ω =
      PrivateSamplingTapeProjections.state (SourceExecutableTables.samplingConfig main final N) G input ω := by
  let Y : Point d := ω.2.1
  let base : Env d [.point,.scalar,.point,.point] :=
    Env.cons (d := d) (τ := .point) (input.coefficient (cfg).invEnd • Y)
      (Env.cons (d := d) (τ := .scalar) (input.coefficient (cfg).invEnd)
        (Env.cons (d := d) (τ := .point) Y (Env.cons (d := d) (τ := .point) input.center Env.empty)))
  let directs : Env d (PrivateSamplingExecutionSchedule.Entry n) :=
    Env.prepend (fun i => (run (affineRow [] (.there (.there (.there .here)))
      [((cfg).directWeight i,.there (.there .here))]) G input base (ω.2.2.2.2.1 i)).value) base
  have hd : @directs = @PrivateSamplingProgram.setupEnv _ _ _ _ _ _ _ cfg input Y := by
    funext ty ref
    dsimp only [directs]
    simp only [run_affineRow,pointResult,storedPoint,base,Env.cons_here,Env.cons_there,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rfl
  let Z : Fin n → Point d := fun i => (ω.2.2.2.2.2.1 i).1
  change finalState c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual
    (cfg).mainAuxiliary F G input N batchRef
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
    (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))
    (Env.prepend (fun i => (run (initialRow (cfg).noise batchRef i) G input
      (Env.prepend Z directs) (ω.2.2.2.2.2.2.1 i)).value) (Env.prepend Z directs))
    ω.2.2.2.2.2.2.2 = _
  rw [hd]
  simp only [run_initialRow,pointResult]
  rfl


/-- Complete stored state at the actual reached paid-final cut. -/
def terminalState (G : Point d → Point d)
    (input : Inputs d (SourceExecutableTables.samplingSize main final)) (ω : Tape d host) :
    FinalState (SourceExecutableTables.samplingSize main final) n d
      (PrivateSamplingExecutionSchedule.Entry n) .point F :=
  let s := terminalCursor S e r Ds main final N
  let path := terminalCut S e r Ds main final N
  ⟨s.ctx,s.old,s.direct,s.saved,envAt G input path Env.empty (split path ω).1,(split path ω).2⟩

private theorem terminalState_eq_completedState (G : Point d → Point d)
    (input : Inputs d (SourceExecutableTables.samplingSize main final)) (ω : Tape d host) :
    terminalState S e r Ds main final N G input ω =
      completedState S e r Ds main final N G input (terminalCursor S e r Ds main final N) ω := by
  have h (s : Cursor S e r Ds main final N) (hs : s.remaining = 0) :
      let path : TailCut (F s.old s.direct s.saved) host := by
        have hp := s.cut
        rw [hs] at hp
        exact hp
      (⟨s.ctx,s.old,s.direct,s.saved,envAt G input path Env.empty (split path ω).1,
        (split path ω).2⟩ : FinalState _ n d _ .point F) =
      completedState S e r Ds main final N G input s ω := by
    rcases s with ⟨remaining,ctx,old,direct,saved,path⟩
    dsimp only at hs
    subst remaining
    rfl
  exact h _ (terminal_remaining S e r Ds main final N)

/-- The complete final state/tape in the old executable interpreter is the
state at the actual chronological terminal cursor, including N=0. -/
theorem terminalState_eq_state (G : Point d → Point d)
    (input : Inputs d (SourceExecutableTables.samplingSize main final)) (ω : Tape d host) :
    terminalState S e r Ds main final N G input ω =
      PrivateSamplingTapeProjections.state (SourceExecutableTables.samplingConfig main final N) G input ω := by
  rw [terminalState_eq_completedState]
  exact (completedState_stage S e r Ds main final N G input ω N le_rfl).trans
    (completedState_entry_eq_state S e r Ds main final N G input ω)

/-- Actual transformed standalone seed extracted from the fresh paid-final
occurrence on the same original full source tape. -/
def terminalSeed (ω : Tape d host) (i : Fin n) : Point d × Tape d (final i).program :=
  transformedSeed (final i).program (final i).enumeration
    (CovarianceSetup.childRoot (SourceExecutableTables.samplingNoise S r Ds)
      (S.radius r (e i)) (final i).shiftVector)
    (freshChildTapeEquiv (final i).program (final i).enumeration ((cfg).finalSlots i)
      ((terminalCursor S e r Ds main final N).old i) ((cfg).finalDesignated i) ((cfg).finalAuxiliary i)
      ((split (terminalCut S e r Ds main final N) ω).2.1 i))

/-- The existing final evaluator uses exactly this original designated momentum
and this complete transformed source tape. No equality of entering centers is
used; the tape includes every original residual/uniform coordinate. -/
theorem final_seed_eq_terminalSeed (x : Point d) (G : Point d → Point d) (P : Point d)
    (ω : Tape d host) (i : Fin n) :
    ((PrivateSamplingTapeProjections.finalData cfg G
        (PrivateSamplingExecutionSchedule.inp S e r Ds main final x P) ω i).1,
      PrivateSamplingRetainedRms.finalSourceTape S e r Ds main final N x G P ω i) =
        terminalSeed S e r Ds main final N ω i := by
  have hs := congrArg (fun st : FinalState (SourceExecutableTables.samplingSize main final) n d
      (PrivateSamplingExecutionSchedule.Entry n) .point F =>
    transformedSeed (final i).program (final i).enumeration
      (CovarianceSetup.childRoot (SourceExecutableTables.samplingNoise S r Ds)
        (S.radius r (e i)) (final i).shiftVector)
      (freshChildTapeEquiv (final i).program (final i).enumeration ((cfg).finalSlots i)
        (st.old i) ((cfg).finalDesignated i) ((cfg).finalAuxiliary i) (st.tape.1 i)))
    (terminalState_eq_state S e r Ds main final N G
      (PrivateSamplingExecutionSchedule.inp S e r Ds main final x P) ω)
  exact hs.symm

/-- Arbitrary-center callback identity. The benchmark can vary while the
original designated draw and complete source tape remain exactly the same. -/
theorem finalEvaluator_eq_terminalSeed (x : Point d) (G : Point d → Point d) (P : Point d)
    (ω : Tape d host) (i : Fin n) (z : Point d) :
    PrivateSamplingRetainedRms.finalEvaluator S e r Ds main final N x G P ω i z =
      (run (final i).program G
        ⟨(final i).coefficient,z,(terminalSeed S e r Ds main final N ω i).1⟩ Env.empty
        (terminalSeed S e r Ds main final N ω i).2).value := by
  exact congrArg (fun seed : Point d × Tape d (final i).program =>
    (run (final i).program G ⟨(final i).coefficient,z,seed.1⟩ Env.empty seed.2).value)
    (final_seed_eq_terminalSeed S e r Ds main final N x G P ω i)

end AcceleratedLogConcave.Oracle.PrivateFinalEvaluatorReadout
