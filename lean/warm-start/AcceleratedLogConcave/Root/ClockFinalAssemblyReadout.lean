import AcceleratedLogConcave.Root.ClockFinalBatchCoupling
import AcceleratedLogConcave.Oracle.MeanFinalAssemblyReadout

/-! Same-tape saved-reference routing at the actual retained Clock final cut.
The designated inputs and split parent are read from the literal original
assembly, after every executed main layer. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Root.ClockFinalAssemblyReadout
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut
open Oracle.PrivateCausalLayer Oracle.PrivateCausalAdvance
open ClockChronologicalCoupling ClockNoisyLayer
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}
  (G : Point d→Point d) (input : Inputs d (ClockRetainedFinalSplice.size P hR hc hsmall clock))
local notation "host" => Host P hR hc hsmall clock label

private theorem prepend_value {n d : ℕ} {Γ : Ctx} (Z : Fin n → Point d) (env : Env d Γ) (i : Fin n) :
    Env.prepend Z env (batchRef i) = Z i := prepend_batchRef Z env i

private theorem afterLayer_saved {n C d : ℕ} {Ξ Γ Δ : Ctx} {τ : Ty}
    (c : Fin n → ℕ) (p : ∀ i,Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (en : ∀ i,GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i,Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx},(Fin n → Ref Δ .point) → (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
    {whole : Prog C Γ τ} (remaining : ℕ) (old direct : Fin n → Ref Δ .point) (saved : RefMap Ξ Δ)
    (cut : TailCut (iterateThen c p slots en outer designated residual auxiliary finish (remaining+1) old direct saved) whole)
    (G : Point d→Point d) (input : Inputs d C) (env : Env d Γ) (sample : Tape d whole) (q : Ref Ξ .point) :
    storedPoint (envAt G input (afterLayer c p slots en outer designated residual auxiliary finish remaining old direct saved cut)
      env (split (afterLayer c p slots en outer designated residual auxiliary finish remaining old direct saved cut) sample).1)
      (preserveDirect (saved q)) = storedPoint (envAt G input cut env (split cut sample).1) (saved q) := by
  change envAt G input (afterLayer c p slots en outer designated residual auxiliary finish remaining old direct saved cut)
    env (split (afterLayer c p slots en outer designated residual auxiliary finish remaining old direct saved cut) sample).1
    (preserveDirect (saved q)) = envAt G input cut env (split cut sample).1 (saved q)
  unfold afterLayer afterBatch
  rw [MeanFinalAssemblyReadout.envAt_trans_split]
  simp only [envAt,split,preserveDirect,prepend_shiftMany]
  rw [MeanFinalAssemblyReadout.envAt_trans_split]
  simp only [envAt,split,prepend_shiftMany]
  rw [MeanFinalAssemblyReadout.envAt_trans_split]
  simp only [envAt,split,prepend_shiftMany]

private theorem advance_saved (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
    (sample : Tape d host) (q : Ref (ClockRetainedFinalSplice.entryCtx P) .point) :
    storedPoint (envAt G input (advance P hR hc hsmall clock label s hs).cut Env.empty
      (split (advance P hR hc hsmall clock label s hs).cut sample).1)
      ((advance P hR hc hsmall clock label s hs).saved q) =
    storedPoint (envAt G input s.cut Env.empty (split s.cut sample).1) (s.saved q) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      exact afterLayer_saved (c P hR hc hsmall clock) (p P hR hc hsmall clock)
        (ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock) (e P hR hc hsmall clock) (fun _ => [])
        (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
        (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
        (ClockRetainedFinalSplice.finish P hR hc hsmall clock label) remaining old direct saved cut G input Env.empty sample q

/-- Every saved source reference survives the exact reached main chronology. -/
theorem stage_saved (k : ℕ) (hk : k≤P.K+4) (sample : Tape d host)
    (q : Ref (ClockRetainedFinalSplice.entryCtx P) .point) :
    storedPoint (envAt G input (stage P hR hc hsmall clock label k hk).1.cut Env.empty
      (split (stage P hR hc hsmall clock label k hk).1.cut sample).1)
      ((stage P hR hc hsmall clock label k hk).1.saved q) =
    storedPoint (envAt G input (entry P hR hc hsmall clock label).cut Env.empty
      (split (entry P hR hc hsmall clock label).cut sample).1) q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (advance_saved P hR hc hsmall clock label G input
      (stage P hR hc hsmall clock label k (by omega)).1 (by rw [stage_remaining]; omega)
      sample q).trans (ih (by omega))

private def zeroCut (s : Cursor P hR hc hsmall clock label) (hs : s.remaining=0) :
    TailCut (ClockRetainedFinalSplice.finish P hR hc hsmall clock label s.old s.direct s.saved) host := by
  have h := s.cut
  rw [hs] at h
  exact h

private theorem zeroCut_saved (s : Cursor P hR hc hsmall clock label) (hs : s.remaining=0)
    (sample : Tape d host) (q : Ref (ClockRetainedFinalSplice.entryCtx P) .point) :
    storedPoint (envAt G input (zeroCut P hR hc hsmall clock label s hs) Env.empty
      (split (zeroCut P hR hc hsmall clock label s hs) sample).1) (s.saved q) =
    storedPoint (envAt G input s.cut Env.empty (split s.cut sample).1) (s.saved q) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => rfl
    | succ remaining => change remaining+1=0 at hs; omega

/-- The final designated batch reads precisely the same initial saved values. -/
theorem terminal_saved (sample : Tape d host)
    (q : Ref (ClockRetainedFinalSplice.entryCtx P) .point) :
    storedPoint (envAt G input (terminalCut P hR hc hsmall clock label) Env.empty
      (split (terminalCut P hR hc hsmall clock label) sample).1)
      ((terminalCursor P hR hc hsmall clock label).saved q) =
    storedPoint (envAt G input (entry P hR hc hsmall clock label).cut Env.empty
      (split (entry P hR hc hsmall clock label).cut sample).1) q := by
  have h : storedPoint (envAt G input (terminalCursor P hR hc hsmall clock label).cut Env.empty
      (split (terminalCursor P hR hc hsmall clock label).cut sample).1)
      ((terminalCursor P hR hc hsmall clock label).saved q) = _ :=
    stage_saved P hR hc hsmall clock label G input (P.K+4) le_rfl sample q
  exact (zeroCut_saved P hR hc hsmall clock label G input
    (terminalCursor P hR hc hsmall clock label) (terminal_remaining P hR hc hsmall clock label) sample q).trans h

/-- The literal original split draw. -/
def splitDraw (sample : Tape d host) : Point d := sample.2.2.1
/-- Every raw coordinate of the original designated assembly. -/
def assemblyRaw (sample : Tape d host) : Index P → Point d :=
  fun i => (sample.2.2.2.2.2.1 i).1

/-- The initial designated values are the positive-root assembly on the same tape. -/
theorem entry_designated_assembled (xF momentum : Point d) (sample : Tape d host) (i : Index P) :
    storedPoint (envAt G
      (⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,xF,momentum⟩ : Inputs d _)
      (entry P hR hc hsmall clock label).cut Env.empty
      (split (entry P hR hc hsmall clock label).cut sample).1)
      (ClockRetainedFinalSplice.designatedRef P i) =
    ClockRetainedFinalSplice.activeValues P clock
      (ClockPublicSetup.splitValues momentum (splitDraw P hR hc hsmall clock label sample) 1)
      (assemblyRaw P hR hc hsmall clock label sample) i := by
  dsimp only [entry,id,envAt,split,ClockRetainedFinalSplice.designatedRef,
    ClockRetainedFinalSplice.entrySaved,storedPoint]
  erw [prepend_shiftMany,prepend_shiftMany,prepend_value]
  simp only [evalInstr]
  erw [MeanExecutablePrefix.run_assemblyRow]
  simp only [pointResult]
  rw [MeanExecutablePrefix.assemblyValues_eq_active
    (ClockRetainedFinalSplice.coefficient P clock)
    (ClockRetainedFinalSplice.coefficient_admissible P clock)]
  · congr 1
    simp only [ClockPublicSetup.saved,storedPoint,prepend_shiftMany,ClockPublicSetup.hRef]
    exact congrArg (fun z : Result d .point => z.value)
      (ClockRetainedFinalSplice.run_splitRow P hR hc hsmall clock 1 G xF momentum
        (splitDraw P hR hc hsmall clock label sample) (sample.2.2.2.1 1))
  · exact ClockRetainedFinalSplice.table_assembly P hR hc hsmall clock

/-- The stored correction parent is the same original orthogonal split H0. -/
theorem entry_parent_split (xF momentum : Point d) (sample : Tape d host) :
    storedPoint (envAt G
      (⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,xF,momentum⟩ : Inputs d _)
      (entry P hR hc hsmall clock label).cut Env.empty
      (split (entry P hR hc hsmall clock label).cut sample).1)
      (ClockRetainedFinalSplice.parentRef P) =
    ClockPublicSetup.splitValues momentum (splitDraw P hR hc hsmall clock label sample) 1 := by
  dsimp only [entry,id,envAt,split,ClockRetainedFinalSplice.parentRef,
    ClockRetainedFinalSplice.entrySaved,ClockRetainedFinalSplice.assemblySaved,
    ClockPublicSetup.saved,storedPoint]
  erw [prepend_shiftMany,prepend_shiftMany,prepend_shiftMany,prepend_shiftMany,prepend_shiftMany]
  simp only [evalInstr]
  exact congrArg (fun z : Result d .point => z.value)
    (ClockRetainedFinalSplice.run_splitRow P hR hc hsmall clock 1 G xF momentum
      (splitDraw P hR hc hsmall clock label sample) (sample.2.2.2.1 1))

/-- Actual final Pi, with every initial raw assembly coordinate retained. -/
theorem terminal_designated_assembled (xF momentum : Point d) (sample : Tape d host) (i : Index P) :
    storedPoint (envAt G
      (⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,xF,momentum⟩ : Inputs d _)
      (terminalCut P hR hc hsmall clock label) Env.empty
      (split (terminalCut P hR hc hsmall clock label) sample).1)
      ((terminalCursor P hR hc hsmall clock label).saved (ClockRetainedFinalSplice.designatedRef P i)) =
    ClockRetainedFinalSplice.activeValues P clock
      (ClockPublicSetup.splitValues momentum (splitDraw P hR hc hsmall clock label sample) 1)
      (assemblyRaw P hR hc hsmall clock label sample) i :=
  (terminal_saved P hR hc hsmall clock label G _ sample _).trans
    (entry_designated_assembled P hR hc hsmall clock label G xF momentum sample i)

/-- The literal final correction retains H0 from the same original split. -/
theorem terminal_parent_split (xF momentum : Point d) (sample : Tape d host) :
    storedPoint (envAt G
      (⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,xF,momentum⟩ : Inputs d _)
      (terminalCut P hR hc hsmall clock label) Env.empty
      (split (terminalCut P hR hc hsmall clock label) sample).1)
      ((terminalCursor P hR hc hsmall clock label).saved (ClockRetainedFinalSplice.parentRef P)) =
    ClockPublicSetup.splitValues momentum (splitDraw P hR hc hsmall clock label sample) 1 :=
  (terminal_saved P hR hc hsmall clock label G _ sample _).trans
    (entry_parent_split P hR hc hsmall clock label G xF momentum sample)

end AcceleratedLogConcave.Root.ClockFinalAssemblyReadout
