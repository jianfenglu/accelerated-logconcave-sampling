import AcceleratedLogConcave.Root.ClockMainReadout
import AcceleratedLogConcave.Root.ClockInitialComparison

/-! Exact stored main state of the literal initialized source loop, on its
complete original tape, equals the existing finite numerical iteration. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Root.ClockMainStateReadout
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut
open ClockNoisyLayer ClockChronologicalCoupling
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}
local notation "c" => ClockNoisyLayer.c P hR hc hsmall clock
local notation "p" => ClockNoisyLayer.p P hR hc hsmall clock
local notation "en" => ClockNoisyLayer.e P hR hc hsmall clock
local notation "finish" => ClockRetainedFinalSplice.finish P hR hc hsmall clock label
local notation "slots" => ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock
local notation "table" => ClockRetainedFinalSplice.table P hR hc hsmall clock
local notation "entry" => ClockChronologicalCoupling.entry P hR hc hsmall clock label
local notation "Host" => ClockChronologicalCoupling.Host P hR hc hsmall clock label

def coordinates (sample : Tape d Host) :=
  ClockInitialComparison.coordinates P hR hc hsmall clock label (split (entry).cut sample).1

def direct (xF momentum : Point d) (i : Index P) (sample : Tape d Host) : Point d :=
  b P clock xF (ClockPublicSetup.splitValues momentum (coordinates P hR hc hsmall clock label sample).1 0) i

def initial (xF momentum : Point d) (i : Index P) (sample : Tape d Host) : Point d :=
  ClockRepeatedLayers.initialCenters P clock xF momentum
    (coordinates P hR hc hsmall clock label sample).1
    (coordinates P hR hc hsmall clock label sample).2.2 i

def entryEnv (xF momentum : Point d) (sample : Tape d Host) : Env d (ClockRetainedFinalSplice.entryCtx P) :=
  ClockRetainedFinalSplice.entryEnv P clock xF momentum
    (coordinates P hR hc hsmall clock label sample).1
    (coordinates P hR hc hsmall clock label sample).2.1
    (coordinates P hR hc hsmall clock label sample).2.2

theorem entry_old (xF momentum : Point d) (sample : Tape d Host) (i : Index P) :
    storedPoint (entryEnv P hR hc hsmall clock label xF momentum sample)
      (ClockRetainedFinalSplice.oldRef P i) = initial P hR hc hsmall clock label xF momentum i sample :=
  prepend_batchRef _ _ _

theorem entry_direct (xF momentum : Point d) (sample : Tape d Host) (i : Index P) :
    storedPoint (entryEnv P hR hc hsmall clock label xF momentum sample)
      (ClockRetainedFinalSplice.directRef P i) = direct P hR hc hsmall clock label xF momentum i sample := by
  simp only [entryEnv,ClockRetainedFinalSplice.entryEnv,ClockRetainedFinalSplice.directRef,
    ClockRetainedFinalSplice.entrySaved,ClockRetainedFinalSplice.assembledEnv,
    ClockRetainedFinalSplice.assemblySaved,storedPoint,prepend_shiftMany]
  exact ClockPublicSetup.ready_direct P clock xF momentum _ i

/-- Actual public table, including the old block's embedding. -/
theorem main_table : table ∘ slots = layerTable c p (A P clock) (C P clock)
    (T P hR hc hsmall clock) (coeff P hR hc hsmall clock) := by
  funext i
  exact (ClockRetainedFinalSplice.table_old P hR hc hsmall clock _).trans
    (congrFun (ClockRepeatedLayers.table_slots P hR hc hsmall clock) i)

/-- The reached original store, not a separately defined numerical sampler. -/
def state (G : Point d → Point d) (xF momentum : Point d) (sample : Tape d Host) :=
  ClockRetainedFinalSplice.reached P hR hc hsmall clock label G xF momentum
    (entryEnv P hR hc hsmall clock label xF momentum sample) (split (entry).cut sample).2

theorem state_eq_iterate (G : Point d → Point d) (xF momentum : Point d)
    (U : Index P → Tape d Host → Point d) (i : Index P) (sample : Tape d Host) :
    storedPoint (state P hR hc hsmall clock label G xF momentum sample).env
      ((state P hR hc hsmall clock label G xF momentum sample).old i) =
    Numerics.SharedLayerRms.iterate
      (direct P hR hc hsmall clock label xF momentum) (A P clock) (C P clock)
      (ClockMainReadout.evaluator P hR hc hsmall clock label G U)
      (MeanExecutionSchedule.residualNoise c p finish (P.K+4)
        (ClockChronologicalExecution.raw P hR hc hsmall clock label))
      (initial P hR hc hsmall clock label xF momentum) (P.K+4) i sample := by
  have ht := MeanExecutionSchedule.finalState_raw_old c p finish en
    (T P hR hc hsmall clock) (coeff P hR hc hsmall clock) G slots
    (fun _ => []) (ClockRepeatedLayers.designated P (P.K+4))
    (ClockRepeatedLayers.residual P (P.K+4))
    (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4))
    (A P clock) (C P clock) ⟨table,xF,momentum⟩ (main_table P hR hc hsmall clock)
    (P.K+4) (ClockRetainedFinalSplice.oldRef P) (ClockRetainedFinalSplice.directRef P)
    (fun r => r) (entryEnv P hR hc hsmall clock label xF momentum sample)
    (ClockChronologicalExecution.raw P hR hc hsmall clock label sample) i
  have hround : (ClockRetainedFinalSplice.loopTapeEquiv P hR hc hsmall clock d label).symm
      (ClockChronologicalExecution.raw P hR hc hsmall clock label sample) = (split (entry).cut sample).2 :=
    ClockRetainedFinalSplice.loop_tape_roundtrip P hR hc hsmall clock label _
  unfold ClockRetainedFinalSplice.loopTapeEquiv at hround
  rw [hround] at ht
  simp only [entry_direct,entry_old] at ht
  have hf := congrFun (congrFun (MeanExecutionSchedule.fold_eq_iterate c p finish en
    (T P hR hc hsmall clock) (coeff P hR hc hsmall clock) G (A P clock) (C P clock)
    (P.K+4) (ClockChronologicalExecution.raw P hR hc hsmall clock label)
    (direct P hR hc hsmall clock label xF momentum)
    (initial P hR hc hsmall clock label xF momentum) U) i) sample
  exact ht.trans hf
end AcceleratedLogConcave.Root.ClockMainStateReadout
