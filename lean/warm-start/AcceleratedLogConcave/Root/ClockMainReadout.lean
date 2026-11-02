import AcceleratedLogConcave.Root.ClockChronologicalExecution
import AcceleratedLogConcave.Oracle.ReplaySeedMeasurability

/-! Literal transformed full source seed at every executed Clock main child. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace AcceleratedLogConcave.Root.ClockMainReadout
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation Oracle.ReplaySeedMeasurability
open Oracle.TailOccurrenceCut Oracle.PrivateCausalLayer Oracle.PrivateCausalAdvance
open TailCut Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockChronologicalCoupling ClockChronologicalExecution ClockNoisyLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalResidualSpace {c : ℕ} (p : Program c .point) :
    MeasurableSpace (ResidualTape p) := residualSpace p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y) {d : ℕ}
local notation "c" => ClockNoisyLayer.c P hR hc hsmall clock
local notation "p" => ClockNoisyLayer.p P hR hc hsmall clock
local notation "en" => ClockNoisyLayer.e P hR hc hsmall clock
local notation "finish" => ClockRetainedFinalSplice.finish P hR hc hsmall clock label

def evaluator (G : Point d → Point d)
    (U : Index P → Tape d (Host P hR hc hsmall clock label) → Point d) :=
  MeanExecutionSchedule.evaluator c p finish en (T P hR hc hsmall clock) (coeff P hR hc hsmall clock)
    G (P.K+4) (raw P hR hc hsmall clock label) U

def cursorSeed (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
    (i : Index P) (sample : Tape d (Host P hR hc hsmall clock label)) : Point d × Tape d (child P hR hc hsmall clock i).program :=
  let B := data P hR hc hsmall clock label hK hC hy s hs
  transformedSeed (child P hR hc hsmall clock i).program (child P hR hc hsmall clock i).enumeration (T P hR hc hsmall clock i)
    (freshChildTapeEquiv (child P hR hc hsmall clock i).program (child P hR hc hsmall clock i).enumeration (B.slot i) (B.old i)
      (B.designated i) (B.auxiliary i)
      ((split (batchCut P hR hc hsmall clock label hK hC hy s hs) sample).2.1 i))

theorem cursorSeed_measurable (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining) (i : Index P) :
    Measurable (cursorSeed (d := d) P hR hc hsmall clock label hK hC hy s hs i) := by
  let B := data P hR hc hsmall clock label hK hC hy s hs
  have ht := (measurable_transformedSeed (d := d) (child P hR hc hsmall clock i).program (child P hR hc hsmall clock i).enumeration (T P hR hc hsmall clock i)).comp
    (measurable_freshChildSeed (child P hR hc hsmall clock i).program (child P hR hc hsmall clock i).enumeration (B.slot i) (B.old i)
      (B.designated i) (B.auxiliary i))
  exact ht.comp ((measurable_pi_apply i).comp
    (measurePreserving_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (batchCut P hR hc hsmall clock label hK hC hy s hs)).measurable.snd.fst)

private theorem cursor_value (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
    (G : Point d → Point d) (U : Index P → Tape d (Host P hR hc hsmall clock label) → Point d)
    (i : Index P) (sample : Tape d (Host P hR hc hsmall clock label)) (y : Point d) :
    (match MeanExecutionSchedule.inputAt c p finish s.remaining
      (cursorRaw P hR hc hsmall clock label s sample) 0 with
      | some v => MeanExecutionSchedule.sourceValue c p en (T P hR hc hsmall clock) (coeff P hR hc hsmall clock) G v i y
      | none => U i sample) =
    (run (child P hR hc hsmall clock i).program G ⟨(child P hR hc hsmall clock i).coefficient,y,
      (cursorSeed P hR hc hsmall clock label hK hC hy s hs i sample).1⟩ Env.empty
      (cursorSeed P hR hc hsmall clock label hK hC hy s hs i sample).2).value := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => exact False.elim (Nat.not_lt_zero _ hs)
    | succ remaining => rfl

/-- The actual chronological evaluator executes precisely the source program
on this transformed full seed. No post-horizon case is hypothesized. -/
theorem evaluator_eq_run (k : ℕ) (hk : k<(P.K+4))
    (G : Point d → Point d) (U : Index P → Tape d (Host P hR hc hsmall clock label) → Point d)
    (i : Index P) (sample : Tape d (Host P hR hc hsmall clock label)) (y : Point d) :
    evaluator P hR hc hsmall clock label G U k i sample y =
      (run (child P hR hc hsmall clock i).program G ⟨(child P hR hc hsmall clock i).coefficient,y,
        (cursorSeed P hR hc hsmall clock label hK hC hy
          (stage P hR hc hsmall clock label k hk.le).1
          (stage_positive P hR hc hsmall clock label k hk) i sample).1⟩ Env.empty
        (cursorSeed P hR hc hsmall clock label hK hC hy
          (stage P hR hc hsmall clock label k hk.le).1
          (stage_positive P hR hc hsmall clock label k hk) i sample).2).value := by
  unfold evaluator MeanExecutionSchedule.evaluator
  have hh := stage_inputAt P hR hc hsmall clock label k hk.le 0 sample
  simp only [Nat.add_zero] at hh
  rw [hh]
  have hv := cursor_value P hR hc hsmall clock label hK hC hy
    (stage P hR hc hsmall clock label k hk.le).1
    (stage_positive P hR hc hsmall clock label k hk) G U i sample y
  cases he : MeanExecutionSchedule.inputAt c p finish
      (stage P hR hc hsmall clock label k hk.le).1.remaining
      (cursorRaw P hR hc hsmall clock label (stage P hR hc hsmall clock label k hk.le).1 sample) 0 <;>
    simpa only [he] using hv



include hK hC hy in
/-- Measurability of the actual callback at a measurable candidate, without
requiring any post-horizon fallback measurability. -/
theorem evaluator_measurable {Ω : Type*} [MeasurableSpace Ω]
    (G : Point d → Point d) (hG : Measurable G)
    (U : Index P → Tape d (Host P hR hc hsmall clock label) → Point d)
    (k : ℕ) (hk : k<P.K+4) (i : Index P)
    (sample : Ω → Tape d (Host P hR hc hsmall clock label)) (hsample : Measurable sample)
    (candidate : Ω → Point d) (hcandidate : Measurable candidate) :
    Measurable (fun z => evaluator P hR hc hsmall clock label G U k i (sample z) (candidate z)) := by
  have hseed := (cursorSeed_measurable P hR hc hsmall clock label hK hC hy
    (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk) i).comp hsample
  have he : (fun z => evaluator P hR hc hsmall clock label G U k i (sample z) (candidate z)) =
      (fun z => (run (child P hR hc hsmall clock i).program G
        ⟨(child P hR hc hsmall clock i).coefficient,candidate z,
          (cursorSeed P hR hc hsmall clock label hK hC hy (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk) i (sample z)).1⟩ Env.empty
        (cursorSeed P hR hc hsmall clock label hK hC hy (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk) i (sample z)).2).value) := by
    funext z
    exact evaluator_eq_run P hR hc hsmall clock label hK hC hy k hk G U i (sample z) (candidate z)
  rw [he]
  exact program_point_of_measurable (child P hR hc hsmall clock i).program G hG
    (fun _ => (child P hR hc hsmall clock i).coefficient) candidate
    (fun z => (cursorSeed P hR hc hsmall clock label hK hC hy (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk) i (sample z)).1)
    (fun z => (cursorSeed P hR hc hsmall clock label hK hC hy (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk) i (sample z)).2)
    measurable_const hcandidate hseed.fst hseed.snd

include hK hC hy in
/-- Every executed source main callback has the actual original-potential
stability constant. The literal Clock inventory pays the required root guard. -/
theorem evaluator_lipschitz {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
    (U : Index P → Tape d (Host P hR hc hsmall clock label) → Point d)
    (k : ℕ) (i : Index P) (sample : Tape d (Host P hR hc hsmall clock label)) :
    LipschitzWith ⟨2*P.delta,mul_nonneg (by norm_num) P.delta_pos.le⟩ (evaluator P hR hc hsmall clock label (gradient V) U k i sample) := by
  apply MeanExecutionSchedule.evaluator_lipschitz c p finish en (T P hR hc hsmall clock)
    (coeff P hR hc hsmall clock) (gradient V) (P.K+4) (raw P hR hc hsmall clock label) U
    ⟨2*P.delta,mul_nonneg (by norm_num) P.delta_pos.le⟩
  intro j
  exact CubicOuterMainStability.standalone_main_stable P hK hc hsmall hC hy hV hlo hup
    (ClockCollocation.count_pos P.delta_pos P.K) j clock (ClockMeanChildAccuracy.inventory P hC)

end AcceleratedLogConcave.Root.ClockMainReadout
