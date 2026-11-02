import AcceleratedLogConcave.Root.ClockChronologicalCoupling
import AcceleratedLogConcave.Oracle.MeanExecutionSchedule

/-! Same-tape routing of the actual finite retained Clock main loop. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockChronologicalExecution
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open Oracle.TailOccurrenceCut Oracle.PrivateCausalLayer Oracle.PrivateCausalAdvance
open TailCut Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockChronologicalCoupling ClockNoisyLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}
local notation "c" => ClockNoisyLayer.c P hR hc hsmall clock
local notation "p" => ClockNoisyLayer.p P hR hc hsmall clock
local notation "en" => ClockNoisyLayer.e P hR hc hsmall clock
local notation "finish" => ClockRetainedFinalSplice.finish P hR hc hsmall clock label
/-- The complete original suffix at a reached cursor, in the already defined
raw schedule coordinates. Uniform/residual source coordinates remain present. -/
def cursorRaw (s : Cursor P hR hc hsmall clock label)
    (sample : Tape d (Host P hR hc hsmall clock label)) :=
  rawTapeEquiv c p (ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock) en
    (fun _ => []) (ClockRepeatedLayers.designated P (P.K+4)) (ClockRepeatedLayers.residual P (P.K+4))
    (ClockRepeatedLayers.auxiliary P hR hc hsmall clock (P.K+4)) finish d s.remaining s.old s.direct s.saved (split s.cut sample).2

private theorem cursor_inputAt_advance (s : Cursor P hR hc hsmall clock label)
    (hs : 0<s.remaining) (j : ℕ) (sample : Tape d (Host P hR hc hsmall clock label)) :
    MeanExecutionSchedule.inputAt c p finish s.remaining
      (cursorRaw P hR hc hsmall clock label s sample) (j+1) =
    MeanExecutionSchedule.inputAt c p finish (advance P hR hc hsmall clock label s hs).remaining
      (cursorRaw P hR hc hsmall clock label (advance P hR hc hsmall clock label s hs) sample) j := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      dsimp only [cursorRaw,advance,focus,Loop,afterLayer]
      simp only [split_afterBatch]
      rfl

def raw (sample : Tape d (Host P hR hc hsmall clock label)) :=
  cursorRaw P hR hc hsmall clock label (entry P hR hc hsmall clock label) sample

/-- Chronological index zero is the first executed source layer. This exact
suffix identity does not reverse the syntax's remaining-layer origin labels. -/
theorem stage_inputAt (k : ℕ) (hk : k≤(P.K+4)) (j : ℕ)
    (sample : Tape d (Host P hR hc hsmall clock label)) :
    MeanExecutionSchedule.inputAt c p finish (P.K+4)
      (raw P hR hc hsmall clock label sample) (k+j) =
    MeanExecutionSchedule.inputAt c p finish
      (stage P hR hc hsmall clock label k hk).1.remaining
      (cursorRaw P hR hc hsmall clock label (stage P hR hc hsmall clock label k hk).1 sample) j := by
  induction k generalizing j with
  | zero => simp only [Nat.zero_add]; rfl
  | succ k ih =>
    rw [show k+1+j = k+(j+1) by omega,ih (by omega) (j+1)]
    exact cursor_inputAt_advance P hR hc hsmall clock label _ _ j sample

variable (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)

private theorem cursor_residual (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
    (i : Index P) (sample : Tape d (Host P hR hc hsmall clock label)) :
    (show Point d from ((split (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)) sample).2.1 i).1) =
    match MeanExecutionSchedule.inputAt c p finish s.remaining
      (cursorRaw P hR hc hsmall clock label s sample) 0 with
    | some v => v.2 i
    | none => 0 := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      simp only [batchCut,focus,cursorRaw,Loop,split_afterBatch]
      rfl

/-- The residual used by the actual chronological record is exactly the
existing raw-schedule residual occurrence at elapsed k. -/
theorem stage_residual (k : ℕ) (hk : k<(P.K+4)) (i : Index P)
    (sample : Tape d (Host P hR hc hsmall clock label)) :
    (show Point d from ((split (afterBatch (batchCut P hR hc hsmall clock label hK hC hy
      (stage P hR hc hsmall clock label k hk.le).1
      (stage_positive P hR hc hsmall clock label k hk))) sample).2.1 i).1) =
    MeanExecutionSchedule.residualNoise c p finish (P.K+4)
      (fun sample => raw P hR hc hsmall clock label sample) k i sample := by
  have h := stage_inputAt (d := d) P hR hc hsmall clock label k hk.le 0 sample
  simp only [Nat.add_zero] at h
  have hresidual := cursor_residual P hR hc hsmall clock label hK hC hy
    (stage P hR hc hsmall clock label k hk.le).1
    (stage_positive P hR hc hsmall clock label k hk) i sample
  unfold MeanExecutionSchedule.residualNoise
  cases hcur : MeanExecutionSchedule.inputAt (ClockNoisyLayer.c P hR hc hsmall clock) (ClockNoisyLayer.p P hR hc hsmall clock)
      finish
      (stage P hR hc hsmall clock label k hk.le).1.remaining
      (cursorRaw P hR hc hsmall clock label (stage P hR hc hsmall clock label k hk.le).1 sample) 0 <;>
    simp only [hcur] at h hresidual <;> simp only [h] <;> exact hresidual

end AcceleratedLogConcave.Root.ClockChronologicalExecution
