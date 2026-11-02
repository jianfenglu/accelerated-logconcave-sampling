import AcceleratedLogConcave.Root.ClockMainRms
import AcceleratedLogConcave.Root.ClockFinalAssemblyReadout
import AcceleratedLogConcave.Root.ClockFinalEvaluator

/-! Exact actual reached store at the Clock chronological final cut. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Root.ClockMainTerminalState
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut
open Oracle.PrivateCausalLayer Oracle.PrivateCausalAdvance
open ClockChronologicalCoupling ClockNoisyLayer
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

variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}
local notation "c" => ClockNoisyLayer.c P hR hc hsmall clock
local notation "p" => ClockNoisyLayer.p P hR hc hsmall clock
local notation "en" => ClockNoisyLayer.e P hR hc hsmall clock
local notation "slots" => ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock
local notation "outer" => (fun _ : ℕ => ([] : Origin))
local notation "des" => ClockRepeatedLayers.designated P (P.K+4)
local notation "res" => ClockRepeatedLayers.residual P (P.K+4)
local notation "aux" => ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4)
local notation "finish" => ClockRetainedFinalSplice.finish P hR hc hsmall clock label
local notation "host" => Host P hR hc hsmall clock label
local notation "size" => ClockRetainedFinalSplice.size P hR hc hsmall clock
local notation "table" => ClockRetainedFinalSplice.table P hR hc hsmall clock
local notation "entryCtx" => ClockRetainedFinalSplice.entryCtx P

def completedState (G : Point d→Point d) (input : Inputs d size)
    (s : Cursor P hR hc hsmall clock label) (sample : Tape d host) :
    FinalState size (N P) d entryCtx .point finish :=
  finalState c p slots en outer des res aux finish G input s.remaining s.old s.direct s.saved
    (envAt G input s.cut Env.empty (split s.cut sample).1) (split s.cut sample).2

theorem completedState_advance (G : Point d→Point d) (input : Inputs d size)
    (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) (sample : Tape d host) :
    completedState P hR hc hsmall clock label G input (advance P hR hc hsmall clock label s hs) sample =
      completedState P hR hc hsmall clock label G input s sample := by
  rcases s with ⟨remaining,ctx,old,direct,saved,path⟩
  cases remaining with
  | zero => change 0<0 at hs; omega
  | succ k =>
    change finalState c p slots en outer des res aux finish G input k batchRef
      (fun i => preserveDirect (direct i)) (fun q => preserveDirect (saved q))
      (envAt G input (afterLayer c p slots en outer des res aux finish k old direct saved path) Env.empty
        (split (afterLayer c p slots en outer des res aux finish k old direct saved path) sample).1)
      (split (afterLayer c p slots en outer des res aux finish k old direct saved path) sample).2 =
      finalState c p slots en outer des res aux finish G input (k+1) old direct saved
        (envAt G input path Env.empty (split path sample).1) (split path sample).2
    dsimp only [Loop] at path
    simp only [afterLayer,afterBatch,envAt_trans,split_trans_suffix]
    dsimp only [envAt,split,finalState]
    simp only [residual_value,run_noisyRow,pointResult]

theorem completedState_stage (G : Point d→Point d) (input : Inputs d size)
    (sample : Tape d host) (k : ℕ) (hk : k≤P.K+4) :
    completedState P hR hc hsmall clock label G input (stage P hR hc hsmall clock label k hk).1 sample =
      completedState P hR hc hsmall clock label G input (entry P hR hc hsmall clock label) sample := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change completedState P hR hc hsmall clock label G input
      (advance P hR hc hsmall clock label (stage P hR hc hsmall clock label k (by omega)).1 _) sample = _
    rw [completedState_advance]
    exact ih (by omega)

/-- Every setup value is the value in the same literal original source prefix. -/
theorem entry_env (G : Point d→Point d) (xF momentum : Point d) (sample : Tape d host)
    {τ : Ty} (q : Ref entryCtx τ) :
    @envAt size d entryCtx .point
      (Loop P hR hc hsmall clock label (P.K+4) (ClockRetainedFinalSplice.oldRef P)
        (ClockRetainedFinalSplice.directRef P) (fun r=>r))
      G (⟨table,xF,momentum⟩ : Inputs d size) [] .point host
      (entry P hR hc hsmall clock label).cut Env.empty
      (split (entry P hR hc hsmall clock label).cut sample).1 τ q =
    @ClockMainStateReadout.entryEnv P hR hc hsmall clock label d xF momentum sample τ q := by
  let E0 : Point d := sample.2.2.1
  have hs : (fun j => (run (ClockRetainedFinalSplice.splitRow P hR hc hsmall clock j) G
      (⟨table,xF,momentum⟩ : Inputs d size) (ClockPublicSetup.rawEnv xF momentum E0)
      (sample.2.2.2.1 j)).value) = ClockPublicSetup.splitValues momentum E0 :=
    funext fun j => congrArg (fun z : Result d .point => z.value)
      (ClockRetainedFinalSplice.run_splitRow P hR hc hsmall clock j G xF momentum E0 _)
  have hd : (fun i => (run (ClockRetainedFinalSplice.publicDirectRow P hR hc hsmall clock i) G
      (⟨table,xF,momentum⟩ : Inputs d size) (ClockPublicSetup.splitEnv xF momentum E0)
      (sample.2.2.2.2.1 i)).value) = b P clock xF (ClockPublicSetup.splitValues momentum E0 0) :=
    funext fun i => congrArg (fun z : Result d .point => z.value)
      (ClockRetainedFinalSplice.run_publicDirectRow P hR hc hsmall clock i G xF momentum E0 _)
  let Z : Index P→Point d := fun i => (sample.2.2.2.2.2.1 i).1
  let Z0 : Index P→Point d := fun i => (sample.2.2.2.2.2.2.2.1 i).1
  have ha : (fun i => (run (MeanGaussianSetup.row
      (ClockRetainedFinalSplice.assemblySlot P hR hc hsmall clock)
      (ClockPublicSetup.saved P ClockPublicSetup.hRef) i) G (⟨table,xF,momentum⟩ : Inputs d size)
      (Env.prepend Z (ClockPublicSetup.readyEnv P clock xF momentum E0))
      (sample.2.2.2.2.2.2.1 i)).value) =
      ClockRetainedFinalSplice.activeValues P clock (ClockPublicSetup.splitValues momentum E0 1) Z := by
    funext i
    rw [MeanExecutablePrefix.run_assemblyRow]
    simp only [pointResult]
    rw [(ClockPublicSetup.ready_saved P clock xF momentum E0 ClockPublicSetup.hRef).trans
      (ClockPublicSetup.split_h xF momentum E0)]
    exact MeanExecutablePrefix.assemblyValues_eq_active
      (ClockRetainedFinalSplice.coefficient P clock) (ClockRetainedFinalSplice.coefficient_admissible P clock)
      (ClockRetainedFinalSplice.assemblySlot P hR hc hsmall clock) (⟨table,xF,momentum⟩ : Inputs d size)
      (ClockRetainedFinalSplice.table_assembly P hR hc hsmall clock) _ _ i
  have htable : table (ClockRetainedFinalSplice.oldSlot P hR hc hsmall clock
      (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock)) = rhoC P :=
    (ClockRetainedFinalSplice.table_old P hR hc hsmall clock _).trans
      (ClockRepeatedLayers.table_rho P hR hc hsmall clock)
  have hdir (i : Index P) : storedPoint (ClockRetainedFinalSplice.assembledEnv P clock xF momentum E0 Z)
      (ClockRetainedFinalSplice.assemblySaved P (ClockPublicSetup.directRef P i)) =
      b P clock xF (ClockPublicSetup.splitValues momentum E0 0) i := by
    simp only [ClockRetainedFinalSplice.assembledEnv,ClockRetainedFinalSplice.assemblySaved,storedPoint,prepend_shiftMany]
    exact ClockPublicSetup.ready_direct P clock xF momentum E0 i
  have hi : (fun i => (run (initialRow
      (ClockRetainedFinalSplice.oldSlot P hR hc hsmall clock (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock))
      (fun i => ClockRetainedFinalSplice.assemblySaved P (ClockPublicSetup.directRef P i)) i)
      G (⟨table,xF,momentum⟩ : Inputs d size)
      (Env.prepend Z0 (ClockRetainedFinalSplice.assembledEnv P clock xF momentum E0 Z))
      (sample.2.2.2.2.2.2.2.2.1 i)).value) = ClockRepeatedLayers.initialCenters P clock xF momentum E0 Z0 := by
    funext i
    rw [run_initialRow]
    simp only [pointResult,hdir,htable]
    rfl
  dsimp only [entry,id,envAt,split,evalInstr]
  dsimp only [ClockPublicSetup.rawEnv,E0] at hs
  simp only [hs]
  dsimp only [ClockPublicSetup.splitEnv,ClockPublicSetup.rawEnv,E0] at hd
  simp only [hd]
  simp only [residual_value]
  dsimp only [ClockPublicSetup.readyEnv,ClockPublicSetup.splitEnv,ClockPublicSetup.rawEnv,E0,Z] at ha
  simp only [ha]
  dsimp only [ClockRetainedFinalSplice.assembledEnv,ClockPublicSetup.readyEnv,ClockPublicSetup.splitEnv,ClockPublicSetup.rawEnv,E0,Z,Z0] at hi
  simp only [hi]
  rfl


theorem completedState_entry_eq_state (G : Point d→Point d) (xF momentum : Point d) (sample : Tape d host) :
    completedState P hR hc hsmall clock label G (⟨table,xF,momentum⟩ : Inputs d size)
      (entry P hR hc hsmall clock label) sample =
    ClockMainStateReadout.state P hR hc hsmall clock label G xF momentum sample := by
  have he : @Eq (Env d entryCtx)
      (@envAt _ _ _ _ _ G (⟨table,xF,momentum⟩ : Inputs d size) _ _ _
        (entry P hR hc hsmall clock label).cut Env.empty
        (split (entry P hR hc hsmall clock label).cut sample).1)
      (@ClockMainStateReadout.entryEnv P hR hc hsmall clock label d xF momentum sample) := by
    funext τ q
    exact entry_env P hR hc hsmall clock label G xF momentum sample q
  exact congrArg (fun env : Env d entryCtx => finalState c p slots en outer des res aux finish G
    (⟨table,xF,momentum⟩ : Inputs d size) (P.K+4) (ClockRetainedFinalSplice.oldRef P)
    (ClockRetainedFinalSplice.directRef P) (fun r=>r) env
    (split (entry P hR hc hsmall clock label).cut sample).2) he

def terminalState (G : Point d→Point d) (input : Inputs d size) (sample : Tape d host) :
    FinalState size (N P) d entryCtx .point finish :=
  let s := terminalCursor P hR hc hsmall clock label
  let cut := terminalCut P hR hc hsmall clock label
  ⟨s.ctx,s.old,s.direct,s.saved,envAt G input cut Env.empty (split cut sample).1,(split cut sample).2⟩

private theorem terminalState_eq_completedState (G : Point d→Point d) (input : Inputs d size) (sample : Tape d host) :
    terminalState P hR hc hsmall clock label G input sample =
    completedState P hR hc hsmall clock label G input (terminalCursor P hR hc hsmall clock label) sample := by
  have h (s : Cursor P hR hc hsmall clock label) (hs : s.remaining=0) :
      let cut : TailCut (finish s.old s.direct s.saved) host := by
        have hp := s.cut
        rw [hs] at hp
        exact hp
      (⟨s.ctx,s.old,s.direct,s.saved,envAt G input cut Env.empty (split cut sample).1,
        (split cut sample).2⟩ : FinalState size (N P) d entryCtx .point finish) =
      completedState P hR hc hsmall clock label G input s sample := by
    rcases s with ⟨remaining,ctx,old,direct,saved,path⟩
    dsimp only at hs
    subst remaining
    rfl
  exact h _ (terminal_remaining P hR hc hsmall clock label)

/-- Full reached store and untouched final tape agree with the actual source state. -/
theorem terminalState_eq_state (G : Point d→Point d) (xF momentum : Point d) (sample : Tape d host) :
    terminalState P hR hc hsmall clock label G (⟨table,xF,momentum⟩ : Inputs d size) sample =
    ClockMainStateReadout.state P hR hc hsmall clock label G xF momentum sample := by
  rw [terminalState_eq_completedState]
  exact (completedState_stage P hR hc hsmall clock label G (⟨table,xF,momentum⟩ : Inputs d size)
    sample (P.K+4) le_rfl).trans (completedState_entry_eq_state P hR hc hsmall clock label G xF momentum sample)

/-- Every actual final child reads precisely the main state controlled by RMS. -/
theorem actualCenter_eq_state (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
    (G : Point d→Point d) (i : Index P) (z : History P d × Tape d host) :
    ClockFinalEvaluator.actualCenter P hR hc hsmall clock label hK hC hy G i z =
      storedPoint (ClockMainStateReadout.state P hR hc hsmall clock label G z.1.1.1.1 z.1.1.1.2 z.2).env
        ((ClockMainStateReadout.state P hR hc hsmall clock label G z.1.1.1.1 z.1.1.1.2 z.2).old i) := by
  exact congrArg (fun st : FinalState size (N P) d entryCtx .point finish => storedPoint st.env (st.old i))
    (terminalState_eq_state P hR hc hsmall clock label G z.1.1.1.1 z.1.1.1.2 z.2)
end AcceleratedLogConcave.Root.ClockMainTerminalState
