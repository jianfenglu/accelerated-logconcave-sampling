import AcceleratedLogConcave.Oracle.MeanChronologicalCoupling
import AcceleratedLogConcave.Oracle.SourceMeanBuildRms

/-! Same-tape operational identities for the finite chronological coupling.
The stored comparison and returned references are related to the existing
SharedLayerRms benchmark; no state equation or accuracy conclusion is assumed. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanChronologicalExecution
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceExecutableTables CovarianceSetup
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling

local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut

section Routing
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
  (sampling : ExecutableData) (N : ℕ)
local notation "c" => (fun i => (main i).size)
local notation "p" => (fun i => (main i).program)
local notation "en" => (fun i => (main i).enumeration)
local notation "finish" => SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling

/-- Exact complete body tail after the literal prefix; no coordinates regenerated. -/
def bodyTape (sample : Tape d (Host M nodes anchors seeds main final sampling N)) :
    Tape d (SourceMeanExecutable.body (a := a) (h := h) M nodes main final sampling N) :=
  (split (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) sample).2

/-- The complete original suffix at a reached cursor, in the already defined
raw schedule coordinates. Uniform/residual source coordinates remain present. -/
def cursorRaw (s : Cursor M nodes anchors seeds main final sampling N)
    (sample : Tape d (Host M nodes anchors seeds main final sampling N)) :=
  rawTapeEquiv c p (SourceMeanExecutable.mainSlot (a := a) main final sampling) en
    SourceMeanExecutable.layerOrigin SourceMeanExecutable.mainDesignated SourceMeanExecutable.residualOrigin
    (SourceMeanExecutable.mainAuxiliary main) finish d s.remaining s.old s.direct s.saved (split s.cut sample).2

private theorem cursor_inputAt_advance (s : Cursor M nodes anchors seeds main final sampling N)
    (hs : 0<s.remaining) (j : ℕ) (sample : Tape d (Host M nodes anchors seeds main final sampling N)) :
    MeanExecutionSchedule.inputAt c p finish s.remaining
      (cursorRaw M nodes anchors seeds main final sampling N s sample) (j+1) =
    MeanExecutionSchedule.inputAt c p finish (advance M nodes anchors seeds main final sampling N s hs).remaining
      (cursorRaw M nodes anchors seeds main final sampling N (advance M nodes anchors seeds main final sampling N s hs) sample) j := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      dsimp only [cursorRaw,advance,focus,Loop,afterLayer]
      simp only [split_afterBatch]
      rfl

/-- Chronological index zero is the first executed source layer. This exact
suffix identity does not reverse the syntax's remaining-layer origin labels. -/
theorem stage_inputAt (k : ℕ) (hk : k≤N) (j : ℕ)
    (sample : Tape d (Host M nodes anchors seeds main final sampling N)) :
    MeanExecutionSchedule.inputAt c p finish N
      (SourceMeanExecutionRms.raw M nodes main final sampling N
        (bodyTape M nodes anchors seeds main final sampling N sample)) (k+j) =
    MeanExecutionSchedule.inputAt c p finish
      (stage M nodes anchors seeds main final sampling N k hk).1.remaining
      (cursorRaw M nodes anchors seeds main final sampling N (stage M nodes anchors seeds main final sampling N k hk).1 sample) j := by
  induction k generalizing j with
  | zero => simp only [Nat.zero_add]; rfl
  | succ k ih =>
    rw [show k+1+j = k+(j+1) by omega,ih (by omega) (j+1)]
    exact cursor_inputAt_advance M nodes anchors seeds main final sampling N _ _ j sample

variable (r Ds : ℝ)
variable (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)

private theorem cursor_residual (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (i : Fin n) (sample : Tape d (Host M nodes anchors seeds main final sampling N)) :
    (show Point d from ((split (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) sample).2.1 i).1) =
    match MeanExecutionSchedule.inputAt c p finish s.remaining
      (cursorRaw M nodes anchors seeds main final sampling N s sample) 0 with
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
theorem stage_residual (k : ℕ) (hk : k<N) (i : Fin n)
    (sample : Tape d (Host M nodes anchors seeds main final sampling N)) :
    (show Point d from ((split (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      (stage M nodes anchors seeds main final sampling N k hk.le).1
      (stage_positive M nodes anchors seeds main final sampling N k hk))) sample).2.1 i).1) =
    MeanExecutionSchedule.residualNoise c p finish N
      (fun sample => SourceMeanExecutionRms.raw M nodes main final sampling N
        (bodyTape M nodes anchors seeds main final sampling N sample)) k i sample := by
  have h := stage_inputAt (d := d) M nodes anchors seeds main final sampling N k hk.le 0 sample
  simp only [Nat.add_zero] at h
  have hc := cursor_residual M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    (stage M nodes anchors seeds main final sampling N k hk.le).1
    (stage_positive M nodes anchors seeds main final sampling N k hk) i sample
  unfold MeanExecutionSchedule.residualNoise
  cases hcur : MeanExecutionSchedule.inputAt (fun i => (main i).size) (fun i => (main i).program)
      finish
      (stage M nodes anchors seeds main final sampling N k hk.le).1.remaining
      (cursorRaw M nodes anchors seeds main final sampling N (stage M nodes anchors seeds main final sampling N k hk.le).1 sample) 0 <;>
    simp only [hcur] at h hc <;> simp only [h] <;> exact hc

end Routing
end AcceleratedLogConcave.Oracle.MeanChronologicalExecution
