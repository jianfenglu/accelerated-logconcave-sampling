import AcceleratedLogConcave.Oracle.PrivateChronologicalExecution
import AcceleratedLogConcave.Oracle.ReplaySeedMeasurability

/-! Exact lower source seed of every actually executed private main child.
No residual, uniform, designated input, or original continuation is replaced. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace AcceleratedLogConcave.Oracle.PrivateCompletedMainReadout
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer CovarianceSetup
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceExecutableTables
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateChronologicalCoupling PrivateChronologicalExecution ReplaySeedMeasurability
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalResidualSpace {c : ℕ} (p : Program c .point) :
    MeasurableSpace (ResidualTape p) := residualSpace p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, shiftSq (main i).shiftVector ≤ Ds^2)
local notation "cfg" => samplingConfig main final N
local notation "c" => (fun i => (main i).size)
local notation "p" => (fun i => (main i).program)
local notation "en" => (fun i => (main i).enumeration)
local notation "finish" => PrivateSamplingExecutionSchedule.finisher main final N
local notation "T" => (fun i => childRoot (samplingNoise S r Ds) (S.radius r (e i)) (main i).shiftVector)

def cursorSeed (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (i : Fin n) (sample : Tape d (Host S e r Ds main final N)) : Point d × Tape d (main i).program :=
  let B := data S e r Ds main final N hr hDs hmass s hs
  transformedSeed (main i).program (main i).enumeration (T i)
    (freshChildTapeEquiv (main i).program (main i).enumeration (B.slot i) (B.old i)
      (B.designated i) (B.auxiliary i)
      ((split (batchCut S e r Ds main final N hr hDs hmass s hs) sample).2.1 i))

theorem cursorSeed_measurable (L : PrimitiveLaws d) (s : Cursor S e r Ds main final N) (hs : 0<s.remaining) (i : Fin n) :
    Measurable (cursorSeed (d := d) S e r Ds main final N hr hDs hmass s hs i) := by
  let B := data S e r Ds main final N hr hDs hmass s hs
  have ht := (measurable_transformedSeed (d := d) (main i).program (main i).enumeration (T i)).comp
    (measurable_freshChildSeed (main i).program (main i).enumeration (B.slot i) (B.old i)
      (B.designated i) (B.auxiliary i))
  exact ht.comp ((measurable_pi_apply i).comp
    (measurePreserving_split L (batchCut S e r Ds main final N hr hDs hmass s hs)).measurable.snd.fst)

private theorem cursor_value (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (G : Point d → Point d) (U : Fin n → Tape d (Host S e r Ds main final N) → Point d)
    (i : Fin n) (sample : Tape d (Host S e r Ds main final N)) (y : Point d) :
    (match MeanExecutionSchedule.inputAt c p finish s.remaining
      (cursorRaw S e r Ds main final N s sample) 0 with
      | some v => MeanExecutionSchedule.sourceValue c p en T (fun i => (main i).coefficient) G v i y
      | none => U i sample) =
    (run (main i).program G ⟨(main i).coefficient,y,
      (cursorSeed S e r Ds main final N hr hDs hmass s hs i sample).1⟩ Env.empty
      (cursorSeed S e r Ds main final N hr hDs hmass s hs i sample).2).value := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => exact False.elim (Nat.not_lt_zero _ hs)
    | succ remaining => rfl

/-- The actual chronological evaluator executes precisely the source program
on this transformed full seed. No post-horizon case is hypothesized. -/
theorem evaluator_eq_run (k : ℕ) (hk : k<N)
    (G : Point d → Point d) (U : Fin n → Tape d (Host S e r Ds main final N) → Point d)
    (i : Fin n) (sample : Tape d (Host S e r Ds main final N)) (y : Point d) :
    PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G U k i sample y =
      (run (main i).program G ⟨(main i).coefficient,y,
        (cursorSeed S e r Ds main final N hr hDs hmass
          (stage S e r Ds main final N k hk.le).1
          (stage_positive S e r Ds main final N k hk) i sample).1⟩ Env.empty
        (cursorSeed S e r Ds main final N hr hDs hmass
          (stage S e r Ds main final N k hk.le).1
          (stage_positive S e r Ds main final N k hk) i sample).2).value := by
  unfold PrivateSamplingExecutionSchedule.evaluator MeanExecutionSchedule.evaluator
  have hh := stage_inputAt S e r Ds main final N k hk.le 0 sample
  simp only [Nat.add_zero] at hh
  rw [hh]
  have hv := cursor_value S e r Ds main final N hr hDs hmass
    (stage S e r Ds main final N k hk.le).1
    (stage_positive S e r Ds main final N k hk) G U i sample y
  cases he : MeanExecutionSchedule.inputAt c p finish
      (stage S e r Ds main final N k hk.le).1.remaining
      (cursorRaw S e r Ds main final N (stage S e r Ds main final N k hk.le).1 sample) 0 <;>
    simpa only [he] using hv

end AcceleratedLogConcave.Oracle.PrivateCompletedMainReadout
