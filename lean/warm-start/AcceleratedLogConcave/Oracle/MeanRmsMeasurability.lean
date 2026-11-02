import AcceleratedLogConcave.Oracle.MeanIncomingPrivateError
import AcceleratedLogConcave.Oracle.MeanFinalSourceEvaluator
import AcceleratedLogConcave.Oracle.MeanCompletedMainReadout
import AcceleratedLogConcave.Oracle.MeanChronologicalBenchmark
import AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorRms

/-! Measurability of the literal incoming cache and executed mean callbacks.
The oracle is arbitrary measurable G, independently of the analytic potential.
All source coordinates, including residual uniforms, are retained. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace AcceleratedLogConcave.Oracle.MeanRmsMeasurability
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability MeanChronologicalCoupling
open MeanChronologicalExecution SourceMeanExecutionRms OperationalMeasurability
open RecursiveMeanProgram RecursiveMeanContinuation ReplaySeedMeasurability
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance canonicalResidualSpace {c : ℕ} (p : Program c .point) :
    MeasurableSpace (ResidualTape p) := residualSpace p
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
  (sampling : ExecutableData) (N : ℕ) (r σ Ds δ t w : ℝ)
  (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  (L : PrimitiveLaws d) (G : Point d → Point d) (hG : Measurable G)
  {Ω : Type*} [MeasurableSpace Ω]
  (tape : Ω → Tape d (Host M nodes anchors seeds main final sampling N)) (htape : Measurable tape)
local notation "bodyT" => (bodyTape M nodes anchors seeds main final sampling N ∘ tape)

include hr hDs hmass L hG htape in
/-- Actual executed main callback at a measurably varying center. No condition
is needed on a post-horizon fallback which this child never reads. -/
theorem main_callback_measurable (U : Fin n → Ω → Point d)
    (k : ℕ) (hk : k<N) (i : Fin n) (z : Ω → Point d) (hz : Measurable z) :
    Measurable (fun ω => evaluator M nodes r Ds main final sampling N G bodyT U k i ω (z ω)) := by
  let seed := MeanCompletedMainReadout.cursorSeed (d := d) M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    (stage M nodes anchors seeds main final sampling N k hk.le).1
    (stage_positive M nodes anchors seeds main final sampling N k hk) i
  have hs : Measurable (fun ω => seed (tape ω)) := (MeanCompletedMainReadout.cursorSeed_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L _ _ i).comp htape
  have hv := program_point_of_measurable (main i).program G hG (fun _ : Ω => (main i).coefficient)
    z (fun ω => (seed (tape ω)).1) (fun ω => (seed (tape ω)).2)
    measurable_const hz hs.fst hs.snd
  have he : (fun ω => evaluator M nodes r Ds main final sampling N G bodyT U k i ω (z ω)) =
      (fun ω => (run (main i).program G ⟨(main i).coefficient,z ω,(seed (tape ω)).1⟩ Env.empty
        (seed (tape ω)).2).value) := by
    funext ω
    exact MeanCompletedMainReadout.evaluator_eq_run M nodes anchors seeds main final sampling N r Ds hr hDs hmass k hk G
      (fun i _ => U i ω) i (tape ω) (z ω)
  rw [he]
  exact hv

variable (privateShift : GaussianSlot sampling.program → ℝ)
  (x P : Ω → Point d) (hx : Measurable x) (hP : Measurable P)
include L hG htape hx hP in
theorem privateResult_measurable :
    Measurable (fun ω => SourceMeanBuildRms.privateResult M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift G (x ω) (P ω) (tape ω)) := by
  have hs := (MeanIncomingPrivateCoupling.consumed_preserving M nodes anchors seeds main final sampling N L).measurable
  have hcut := (measurePreserving_split L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)).measurable
  have hp := program_point_of_measurable sampling.program G hG (fun _ : Ω => sampling.coefficient)
    x P (fun ω => MeanIncomingPrivateCoupling.consumed M nodes anchors seeds main final sampling N
      (split (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) (tape ω)).1)
    measurable_const hx hP (hs.comp (hcut.fst.comp htape))
  convert hp using 1
  funext ω
  exact MeanIncomingPrivateError.privateResult_eq M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G (x ω) (P ω) (tape ω)

include L hG htape hx hP in
/-- The actual incoming cache is constructed from the executed private child,
original momentum, raw assembly and flow coordinates of this same full tape. -/
theorem actualEnv_path_measurable :
    EnvPathMeasurable (fun ω => SourceMeanBuildRms.actualEnv M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift G (x ω) (P ω) (tape ω)) := by
  apply SourceMeanPrivateAnchorStability.cache_path_measurable M nodes anchors seeds r σ Ds δ t w main final sampling
  · exact hx
  · exact hP
  · exact privateResult_measurable M nodes anchors seeds main final sampling N r σ Ds δ t w L G hG tape htape privateShift x P hx hP
  · intro i
    exact ((measurable_pi_apply i).comp htape.snd.snd.snd.snd.fst).fst
  · intro i
    exact ((measurable_pi_apply i).comp htape.snd.snd.snd.snd.snd.snd.fst).fst

local notation "cache" => (fun ω => SourceMeanBuildRms.actualEnv M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift G (x ω) (P ω) (tape ω))
local notation "Bmat" => (fun i j => M.matrix r σ (nodes i) (nodes j))
local notation "rho" => RecursiveMeanPublicTable.centerNoise r M.R Ds
local notation "Cmat" => CovarianceSetup.residualRoot Bmat rho (rowBound (m := m) r σ δ t w)

include L hG htape hx hP in
theorem initial_measurable (i : Fin n) :
    Measurable (fun ω => initial M nodes r Ds main final sampling N (cache ω) (bodyT ω) i) := by
  have he : EnvPathMeasurable cache := actualEnv_path_measurable M nodes anchors seeds main final sampling N r σ Ds δ t w L G hG tape htape privateShift x P hx hP
  have hb := (measurePreserving_split L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)).measurable.snd.comp htape
  have hn : Measurable (fun ω => (show Point d from ((bodyT ω).1 i).1)) :=
    ((measurable_pi_apply i).comp hb.fst).fst
  exact (he (MeanExecutablePrefix.direct i)).add (hn.const_smul rho)

/-- The exact numerical iterate on the actually initialized cache and full
body tail, with arbitrary unused fallback beyond the finite horizon. -/
def actualIterate (U : Fin n → Ω → Point d) : ℕ → Fin n → Ω → Point d :=
  SharedLayerRms.iterate (fun i ω => storedPoint (cache ω) (MeanExecutablePrefix.direct i))
    Bmat Cmat (evaluator M nodes r Ds main final sampling N G bodyT U)
    (noise M nodes main final sampling N bodyT)
    (fun i ω => initial M nodes r Ds main final sampling N (cache ω) (bodyT ω) i)

include hr hDs hmass L hG htape hx hP in
theorem actual_iterate_measurable (U : Fin n → Ω → Point d) (k : ℕ) (hk : k≤N) (i : Fin n) :
    Measurable (actualIterate M nodes anchors seeds main final sampling N r σ Ds δ t w G tape privateShift x P U k i) := by
  induction k generalizing i with
  | zero => exact initial_measurable M nodes anchors seeds main final sampling N r σ Ds δ t w L G hG tape htape privateShift x P hx hP i
  | succ k ih =>
    have hkN : k<N := by omega
    have hb : EnvPathMeasurable cache := actualEnv_path_measurable M nodes anchors seeds main final sampling N r σ Ds δ t w L G hG tape htape privateShift x P hx hP
    have hc (j : Fin n) := main_callback_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L G hG tape htape U k hkN j
      (actualIterate M nodes anchors seeds main final sampling N r σ Ds δ t w G tape privateShift x P U k j) (ih hkN.le j)
    have hz (j : Fin n) := (MeanChronologicalBenchmark.residualNoise_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L k hkN j).comp htape
    exact ((hb (MeanExecutablePrefix.direct i)).add
      (Finset.measurable_sum Finset.univ (fun j _ => (hc j).const_smul (Bmat i j)))).add
      (Finset.measurable_sum Finset.univ (fun j _ => (hz j).const_smul (Cmat i j)))

include hr hDs hmass L hG htape hx hP in
/-- Same-tape actual-center versus benchmark-center callback difference. -/
theorem main_difference_measurable (U : Fin n → Ω → Point d)
    (k : ℕ) (hk : k<N) (i : Fin n) (Y : Ω → Point d) (hY : Measurable Y) :
    Measurable (fun ω => evaluator M nodes r Ds main final sampling N G bodyT U k i ω
      (actualIterate M nodes anchors seeds main final sampling N r σ Ds δ t w G tape privateShift x P U k i ω) -
      evaluator M nodes r Ds main final sampling N G bodyT U k i ω (Y ω)) :=
  (main_callback_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L G hG tape htape U k hk i _
    (actual_iterate_measurable M nodes anchors seeds main final sampling N r σ Ds δ t w hr hDs hmass L G hG tape htape privateShift x P hx hP U k hk.le i)).sub
      (main_callback_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L G hG tape htape U k hk i Y hY)

local notation "counts" => (fun i => (main i).size)
local notation "programs" => (fun i => (main i).program)
local notation "enums" => (fun i => (main i).enumeration)
local notation "finisher" => SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling
local notation "directions" => (fun i => RefMap.shiftMany n (RefMap.shiftMany n (MeanExecutablePrefix.direct i)))
local notation "savedRefs" => (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))

include L htape in
/-- The actual complete final lower tape is measurable. The finite interpreter
state is identified with its canonical atFinish cut; residual uniforms stay intact. -/
theorem final_tape_measurable (i : Fin m) :
    Measurable (fun ω => finalTape M nodes anchors r σ Ds δ t w main final sampling N G
      (x ω) (P ω) (cache ω) (bodyT ω) i) := by
  let f := atFinish counts programs (mainSlot (a := a) main final sampling) enums layerOrigin
    mainDesignated residualOrigin (mainAuxiliary main) finisher N batchRef directions savedRefs
  have hb := (measurePreserving_split L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)).measurable.snd.comp htape
  have hs := (measurePreserving_split L f.cut).measurable.snd.fst.comp hb.snd.snd
  have hc := (measurable_compiledSeed (d := d) (final i).program (final i).enumeration
    (finalAuxiliary final i)).comp
      ((measurable_restoreTape (finalSlot (a := a) main final sampling i)
        (compileWith (final i).program (final i).enumeration (finalAuxiliary final i))
        (fun q => nomatch q) (f.old (nodes.symm (.center M i)))
        (f.saved (MeanExecutablePrefix.designated i))).comp ((measurable_pi_apply i).comp hs))
  have ht := (measurable_transformedSeed (d := d) (final i).program (final i).enumeration
    (CovarianceSetup.childRoot rho (r*M.R) (final i).shiftVector)).snd.comp
      (show Measurable (fun ω : Ω => ((0 : Point d),
        compiledTapeEquivWith (final i).program (final i).enumeration (finalAuxiliary final i)
          (restoreTape (finalSlot (a := a) main final sampling i)
            (compileWith (final i).program (final i).enumeration (finalAuxiliary final i))
            (fun q => nomatch q) (f.old (nodes.symm (.center M i)))
            (f.saved (MeanExecutablePrefix.designated i))
            ((split f.cut (bodyT ω).2.2).2.1 i)))) from measurable_const.prodMk hc)
  convert ht using 1
  funext ω
  have he := congrArg (fun st => MeanFinalSourceEvaluator.finalTapeOfState M nodes main final sampling r Ds st i)
    (MeanFinalEvaluatorReadout.focusedState_eq_finalState counts programs
      (mainSlot (a := a) main final sampling) enums layerOrigin mainDesignated residualOrigin
      (mainAuxiliary main) finisher G
      ⟨table M nodes anchors r σ Ds δ t w main final sampling,x ω,P ω⟩ N batchRef directions savedRefs
      (initialEnv M nodes r Ds main final sampling N (cache ω) (bodyT ω)) (bodyT ω).2.2)
  exact he.symm

include L hG htape hx hP in
/-- Actual paid-final callback at any measurable candidate, retaining the
same incoming Pi and complete transformed lower tape. -/
theorem final_callback_measurable (i : Fin m) (z : Ω → Point d) (hz : Measurable z) :
    Measurable (fun ω => finalEvaluator M nodes anchors r σ Ds δ t w main final sampling N G
      (x ω) (P ω) (cache ω) (bodyT ω) i (z ω)) := by
  have he : EnvPathMeasurable cache := actualEnv_path_measurable M nodes anchors seeds main final sampling N
    r σ Ds δ t w L G hG tape htape privateShift x P hx hP
  have ht := final_tape_measurable M nodes anchors seeds main final sampling N r σ Ds δ t w L G
    tape htape privateShift x P i
  exact program_point_of_measurable (final i).program G hG (fun _ : Ω => (final i).coefficient)
    z (fun ω => storedPoint (cache ω) (MeanExecutablePrefix.designated i))
    (fun ω => finalTape M nodes anchors r σ Ds δ t w main final sampling N G
      (x ω) (P ω) (cache ω) (bodyT ω) i)
    measurable_const hz (he (MeanExecutablePrefix.designated i)) ht

include hr hDs hmass L hG htape hx hP in
/-- The true final entering center is the actual finite numerical iterate,
proved from the interpreter; it is never identified with a benchmark center. -/
theorem final_center_measurable (i : Fin n) :
    Measurable (fun ω =>
      let st := state M nodes anchors r σ Ds δ t w main final sampling N G
        (x ω) (P ω) (cache ω) (bodyT ω)
      storedPoint st.env (st.old i)) := by
  let U : Fin n → Ω → Point d := fun _ _ => 0
  have hi := actual_iterate_measurable M nodes anchors seeds main final sampling N r σ Ds δ t w
    hr hDs hmass L G hG tape htape privateShift x P hx hP U N le_rfl i
  have he := state_old_eq_iterate M nodes anchors r σ Ds δ t w main final sampling N G x P cache bodyT U
  convert hi using 1
  funext ω
  exact congrFun (congrFun he i) ω

include hr hDs hmass L hG htape hx hP in
/-- Actual paid-final difference at a measurable benchmark; both callbacks
use the identical stored Pi and full source tape. -/
theorem final_difference_measurable (i : Fin m) (Y : Ω → Point d) (hY : Measurable Y) :
    Measurable (fun ω =>
      let st := state M nodes anchors r σ Ds δ t w main final sampling N G
        (x ω) (P ω) (cache ω) (bodyT ω)
      finalEvaluator M nodes anchors r σ Ds δ t w main final sampling N G
        (x ω) (P ω) (cache ω) (bodyT ω) i (storedPoint st.env (st.old (nodes.symm (.center M i)))) -
      finalEvaluator M nodes anchors r σ Ds δ t w main final sampling N G
        (x ω) (P ω) (cache ω) (bodyT ω) i (Y ω)) :=
  (final_callback_measurable M nodes anchors seeds main final sampling N r σ Ds δ t w L G hG tape htape
    privateShift x P hx hP i _ (final_center_measurable M nodes anchors seeds main final sampling N
      r σ Ds δ t w hr hDs hmass L G hG tape htape privateShift x P hx hP (nodes.symm (.center M i)))).sub
    (final_callback_measurable M nodes anchors seeds main final sampling N r σ Ds δ t w L G hG tape htape
      privateShift x P hx hP i Y hY)

end AcceleratedLogConcave.Oracle.MeanRmsMeasurability
