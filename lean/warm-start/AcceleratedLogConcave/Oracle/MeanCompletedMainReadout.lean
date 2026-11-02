import AcceleratedLogConcave.Oracle.MeanChronologicalExecution
import AcceleratedLogConcave.Oracle.ReplaySeedMeasurability

/-! Exact lower source seed of every actually executed private main child.
No residual, uniform, designated input, or original continuation is replaced. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace AcceleratedLogConcave.Oracle.MeanCompletedMainReadout
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer CovarianceSetup
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceExecutableTables
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open MeanChronologicalCoupling MeanChronologicalExecution ReplaySeedMeasurability
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalResidualSpace {c : ℕ} (p : Program c .point) :
    MeasurableSpace (ResidualTape p) := residualSpace p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
  (sampling : ExecutableData) (N : ℕ)
  (r Ds : ℝ) (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, shiftSq (main i).shiftVector ≤ Ds^2)
local notation "c" => (fun i => (main i).size)
local notation "p" => (fun i => (main i).program)
local notation "en" => (fun i => (main i).enumeration)
local notation "finish" => SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling
local notation "T" => (fun i => childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
  (M.radius r (nodes i)) (main i).shiftVector)

def cursorSeed (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (i : Fin n) (sample : Tape d (Host M nodes anchors seeds main final sampling N)) : Point d × Tape d (main i).program :=
  let B := data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs
  transformedSeed (main i).program (main i).enumeration (T i)
    (freshChildTapeEquiv (main i).program (main i).enumeration (B.slot i) (B.old i)
      (B.designated i) (B.auxiliary i)
      ((split (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) sample).2.1 i))

theorem cursorSeed_measurable (L : PrimitiveLaws d) (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) (i : Fin n) :
    Measurable (cursorSeed (d := d) M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs i) := by
  let B := data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs
  have ht := (measurable_transformedSeed (d := d) (main i).program (main i).enumeration (T i)).comp
    (measurable_freshChildSeed (main i).program (main i).enumeration (B.slot i) (B.old i)
      (B.designated i) (B.auxiliary i))
  exact ht.comp ((measurable_pi_apply i).comp
    (measurePreserving_split L (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)).measurable.snd.fst)

private theorem cursor_value (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (G : Point d → Point d) (U : Fin n → Tape d (Host M nodes anchors seeds main final sampling N) → Point d)
    (i : Fin n) (sample : Tape d (Host M nodes anchors seeds main final sampling N)) (y : Point d) :
    (match MeanExecutionSchedule.inputAt c p finish s.remaining
      (cursorRaw M nodes anchors seeds main final sampling N s sample) 0 with
      | some v => MeanExecutionSchedule.sourceValue c p en T (fun i => (main i).coefficient) G v i y
      | none => U i sample) =
    (run (main i).program G ⟨(main i).coefficient,y,
      (cursorSeed M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs i sample).1⟩ Env.empty
      (cursorSeed M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs i sample).2).value := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => exact False.elim (Nat.not_lt_zero _ hs)
    | succ remaining => rfl

/-- The actual chronological evaluator executes precisely the source program
on this transformed full seed. No post-horizon case is hypothesized. -/
theorem evaluator_eq_run (k : ℕ) (hk : k<N)
    (G : Point d → Point d) (U : Fin n → Tape d (Host M nodes anchors seeds main final sampling N) → Point d)
    (i : Fin n) (sample : Tape d (Host M nodes anchors seeds main final sampling N)) (y : Point d) :
    SourceMeanExecutionRms.evaluator M nodes r Ds main final sampling N G
      (bodyTape M nodes anchors seeds main final sampling N) U k i sample y =
      (run (main i).program G ⟨(main i).coefficient,y,
        (cursorSeed M nodes anchors seeds main final sampling N r Ds hr hDs hmass
          (stage M nodes anchors seeds main final sampling N k hk.le).1
          (stage_positive M nodes anchors seeds main final sampling N k hk) i sample).1⟩ Env.empty
        (cursorSeed M nodes anchors seeds main final sampling N r Ds hr hDs hmass
          (stage M nodes anchors seeds main final sampling N k hk.le).1
          (stage_positive M nodes anchors seeds main final sampling N k hk) i sample).2).value := by
  unfold SourceMeanExecutionRms.evaluator MeanExecutionSchedule.evaluator
  have hh := stage_inputAt M nodes anchors seeds main final sampling N k hk.le 0 sample
  simp only [Nat.add_zero] at hh
  rw [hh]
  have hv := cursor_value M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    (stage M nodes anchors seeds main final sampling N k hk.le).1
    (stage_positive M nodes anchors seeds main final sampling N k hk) G U i sample y
  cases he : MeanExecutionSchedule.inputAt c p finish
      (stage M nodes anchors seeds main final sampling N k hk.le).1.remaining
      (cursorRaw M nodes anchors seeds main final sampling N (stage M nodes anchors seeds main final sampling N k hk.le).1 sample) 0 <;>
    simpa only [he] using hv

end AcceleratedLogConcave.Oracle.MeanCompletedMainReadout
