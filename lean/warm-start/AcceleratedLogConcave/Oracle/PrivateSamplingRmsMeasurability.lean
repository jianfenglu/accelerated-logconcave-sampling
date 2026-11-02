import AcceleratedLogConcave.Oracle.PrivateCompletedMainReadout
import AcceleratedLogConcave.Oracle.PrivateFinalEvaluatorReadout

/-! Measurability of actual private callbacks and finite synchronous iterates.
The actual oracle G is independent of the potential used to define benchmark
flows. Every callback retains its full literal original source seed. -/
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory
namespace AcceleratedLogConcave.Oracle.PrivateSamplingRmsMeasurability
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceExecutableTables
open CanonicalTapeLaw CanonicalTapeMeasurability TailOccurrenceCut TailCut
open PrivateChronologicalCoupling PrivateFinalEvaluatorReadout ReplaySeedMeasurability
open scoped BigOperators
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalResidualSpace {c : ℕ} (p : Program c .point) :
    MeasurableSpace (ResidualTape p) := residualSpace p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (path : TailCut q p) :
    MeasurableSpace (Prefix d path) := prefixSpace d path
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (L : PrimitiveLaws d) (G : Point d → Point d) (hG : Measurable G)
local notation "host" => Host S e r Ds main final N
local notation "cfg" => samplingConfig main final N
variable {Ω : Type*} [MeasurableSpace Ω]
  (tape : Ω → Tape d (Host S e r Ds main final N)) (htape : Measurable tape)

include hr hDs hmass L hG htape in
/-- Actual main callback at any measurably varying candidate center. The
post-horizon fallback U is irrelevant to an actually executed child. -/
theorem main_callback_measurable (U : Fin n → Tape d host → Point d)
    (k : ℕ) (hk : k<N) (i : Fin n) (z : Ω → Point d) (hz : Measurable z) :
    Measurable (fun ω => PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G U
      k i (tape ω) (z ω)) := by
  let seed := PrivateCompletedMainReadout.cursorSeed (d := d) S e r Ds main final N hr hDs hmass
    (stage S e r Ds main final N k hk.le).1
    (PrivateChronologicalCoupling.stage_positive S e r Ds main final N k hk) i
  have hs : Measurable (fun ω => seed (tape ω)) :=
    (PrivateCompletedMainReadout.cursorSeed_measurable S e r Ds main final N hr hDs hmass L _ _ i).comp htape
  have hv := program_point_of_measurable (main i).program G hG (fun _ : Ω => (main i).coefficient)
    z (fun ω => (seed (tape ω)).1) (fun ω => (seed (tape ω)).2)
    measurable_const hz hs.fst hs.snd
  have he : (fun ω => PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G U
      k i (tape ω) (z ω)) =
      (fun ω => (run (main i).program G ⟨(main i).coefficient,z ω,(seed (tape ω)).1⟩
        Env.empty (seed (tape ω)).2).value) := by
    funext ω
    exact PrivateCompletedMainReadout.evaluator_eq_run S e r Ds main final N hr hDs hmass k hk G U i (tape ω) (z ω)
  rw [he]
  exact hv

include L in
/-- All designated, auxiliary and residual coordinates at the actual reached
final cut are measurable, including the empty main horizon. -/
theorem terminalSeed_measurable (i : Fin n) :
    Measurable (terminalSeed (d := d) S e r Ds main final N · i) := by
  have hs := (measurePreserving_split L (terminalCut S e r Ds main final N)).measurable
  have hc := measurable_freshChildSeed (d := d) (final i).program (final i).enumeration ((cfg).finalSlots i)
    ((terminalCursor S e r Ds main final N).old i) ((cfg).finalDesignated i) ((cfg).finalAuxiliary i)
  exact (measurable_transformedSeed (d := d) (final i).program (final i).enumeration
    (CovarianceSetup.childRoot (samplingNoise S r Ds) (S.radius r (e i)) (final i).shiftVector)).comp
      (hc.comp ((measurable_pi_apply i).comp hs.snd.fst))

include L hG htape in
/-- The existing arbitrary-center final callback, on the original full tape. -/
theorem final_callback_measurable (x P : Point d) (i : Fin n)
    (z : Ω → Point d) (hz : Measurable z) :
    Measurable (fun ω => PrivateSamplingRetainedRms.finalEvaluator S e r Ds main final N x G P
      (tape ω) i (z ω)) := by
  have hs := (terminalSeed_measurable S e r Ds main final N L i).comp htape
  have hv := program_point_of_measurable (final i).program G hG (fun _ : Ω => (final i).coefficient)
    z (fun ω => (terminalSeed S e r Ds main final N (tape ω) i).1)
    (fun ω => (terminalSeed S e r Ds main final N (tape ω) i).2)
    measurable_const hz hs.fst hs.snd
  have he : (fun ω => PrivateSamplingRetainedRms.finalEvaluator S e r Ds main final N x G P
      (tape ω) i (z ω)) =
      (fun ω => (run (final i).program G
        ⟨(final i).coefficient,z ω,(terminalSeed S e r Ds main final N (tape ω) i).1⟩ Env.empty
        (terminalSeed S e r Ds main final N (tape ω) i).2).value) := by
    funext ω
    exact finalEvaluator_eq_terminalSeed S e r Ds main final N x G P (tape ω) i (z ω)
  rw [he]
  exact hv

include htape in
/-- Literal initialization reads only its actual setup position and initial
Gaussian instruction, with no oracle or law premise. -/
theorem initial_measurable (x : Point d) (i : Fin n) :
    Measurable (fun ω => PrivateSamplingExecutionSchedule.initial S e r Ds main final N x (tape ω) i) := by
  have hp : Measurable (fun ω => (show Point d from (tape ω).2.1)) := htape.snd.fst
  have hz : Measurable (fun ω => (show Point d from ((tape ω).2.2.2.2.2.1 i).1)) :=
    ((measurable_pi_apply i).comp htape.snd.snd.snd.snd.snd.fst).fst
  exact (measurable_const.add (hp.const_smul (r*S.mesh.location m (e i)))).add
    (hz.const_smul (samplingNoise S r Ds))

/-- Same numerical iterate used by the retained RMS consumer, on any measurable
sample carrying the actual full source tape. -/
def actualIterate (x : Point d) (U : Fin n → Tape d host → Point d) : ℕ → Fin n → Ω → Point d :=
  SharedLayerRms.iterate
    (fun j ω => x+(r*S.mesh.location m (e j)) • (show Point d from (tape ω).2.1))
    (samplingMatrix S e r) (CovarianceSetup.residualRoot (samplingMatrix S e r) (samplingNoise S r Ds) (r^2))
    (fun k i ω => PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G U k i (tape ω))
    (fun k i ω => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i (tape ω))
    (fun i ω => PrivateSamplingExecutionSchedule.initial S e r Ds main final N x (tape ω) i)

include hr hDs hmass L hG htape in
/-- Every actually executed synchronous iterate is measurable. Only finitely
many genuine callbacks are used, so no post-horizon fallback hypothesis enters. -/
theorem actual_iterate_measurable (x : Point d) (U : Fin n → Tape d host → Point d)
    (k : ℕ) (hk : k≤N) (i : Fin n) :
    Measurable (actualIterate S e r Ds main final N G tape x U k i) := by
  induction k generalizing i with
  | zero => exact initial_measurable S e r Ds main final N tape htape x i
  | succ k ih =>
    have hkN : k<N := by omega
    have hpos : Measurable (fun ω => (show Point d from (tape ω).2.1)) := htape.snd.fst
    have hb : Measurable (fun ω => x+(r*S.mesh.location m (e i)) • (show Point d from (tape ω).2.1)) :=
      measurable_const.add (hpos.const_smul (r*S.mesh.location m (e i)))
    have hc (j : Fin n) := main_callback_measurable S e r Ds main final N hr hDs hmass L G hG tape htape
      U k hkN j (actualIterate S e r Ds main final N G tape x U k j) (ih hkN.le j)
    have hz (j : Fin n) := (PrivateChronologicalExecution.residualNoise_measurable
      S e r Ds main final N hr hDs hmass L k hkN j).comp htape
    exact (hb.add (Finset.measurable_sum Finset.univ (fun j _ =>
      (hc j).const_smul (samplingMatrix S e r i j)))).add
      (Finset.measurable_sum Finset.univ (fun j _ => (hz j).const_smul
        (CovarianceSetup.residualRoot (samplingMatrix S e r) (samplingNoise S r Ds) (r^2) i j)))

include L hG htape in
/-- The true final entering center is read from the actual prefix interpreter,
so its measurability is derived rather than supplied by the numerical proof. -/
theorem final_center_measurable (x P : Point d) (i : Fin n) :
    Measurable (fun ω =>
      let st := PrivateSamplingTapeProjections.state (samplingConfig main final N) G
        (PrivateSamplingExecutionSchedule.inp S e r Ds main final x P) (tape ω)
      storedPoint st.env (st.old i)) := by
  let path := terminalCut S e r Ds main final N
  let input := PrivateSamplingExecutionSchedule.inp S e r Ds main final x P
  have hp := (measurePreserving_split L path).measurable.fst.comp htape
  have he : OperationalMeasurability.EnvPathMeasurable (fun ω : Ω =>
      envAt G input path Env.empty (split path (tape ω)).1) :=
    envAt_pathMeasurable G hG path (fun _ : Ω => input) (fun _ => Env.empty)
    (fun ω => (split path (tape ω)).1) (fun _ => measurable_const) measurable_const measurable_const
    OperationalMeasurability.envPathMeasurable_empty hp
  have hm : Measurable (fun ω => storedPoint
      (envAt G input path Env.empty (split path (tape ω)).1)
      ((terminalCursor S e r Ds main final N).old i)) :=
    he (τ := .point) ((terminalCursor S e r Ds main final N).old i)
  convert hm using 1
  funext ω
  exact (congrArg (fun st : RecursiveMeanContinuation.FinalState (samplingSize main final) n d
    (PrivateSamplingExecutionSchedule.Entry n) .point (PrivateSamplingExecutionSchedule.finisher main final N) =>
      storedPoint st.env (st.old i))
      (terminalState_eq_state S e r Ds main final N G input (tape ω))).symm

include hr hDs hmass L hG htape in
/-- Actual main fixed-tape difference at any measurable benchmark. -/
theorem main_difference_measurable (x : Point d) (U : Fin n → Tape d host → Point d)
    (k : ℕ) (hk : k<N) (i : Fin n) (Y : Ω → Point d) (hY : Measurable Y) :
    Measurable (fun ω =>
      PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G U k i (tape ω)
        (actualIterate S e r Ds main final N G tape x U k i ω) -
      PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G U k i (tape ω) (Y ω)) :=
  (main_callback_measurable S e r Ds main final N hr hDs hmass L G hG tape htape U k hk i _
    (actual_iterate_measurable S e r Ds main final N hr hDs hmass L G hG tape htape x U k hk.le i)).sub
    (main_callback_measurable S e r Ds main final N hr hDs hmass L G hG tape htape U k hk i Y hY)

include L hG htape in
/-- Actual final fixed-tape difference at any measurable benchmark. Both
callbacks keep the SAME designated draw and complete transformed final tape. -/
theorem final_difference_measurable (x P : Point d) (i : Fin n)
    (Y : Ω → Point d) (hY : Measurable Y) :
    Measurable (fun ω =>
      let st := PrivateSamplingTapeProjections.state (samplingConfig main final N) G
        (PrivateSamplingExecutionSchedule.inp S e r Ds main final x P) (tape ω)
      PrivateSamplingRetainedRms.finalEvaluator S e r Ds main final N x G P (tape ω) i
        (storedPoint st.env (st.old i)) -
      PrivateSamplingRetainedRms.finalEvaluator S e r Ds main final N x G P (tape ω) i (Y ω)) :=
  (final_callback_measurable S e r Ds main final N L G hG tape htape x P i _
    (final_center_measurable S e r Ds main final N L G hG tape htape x P i)).sub
    (final_callback_measurable S e r Ds main final N L G hG tape htape x P i Y hY)

end AcceleratedLogConcave.Oracle.PrivateSamplingRmsMeasurability
