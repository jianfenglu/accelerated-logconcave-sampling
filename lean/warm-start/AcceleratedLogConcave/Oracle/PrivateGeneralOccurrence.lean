import AcceleratedLogConcave.Oracle.GeneralMainFocus
import AcceleratedLogConcave.Oracle.FreshChildJointLaw
import AcceleratedLogConcave.Oracle.FreshChildCanonicalSeedLaw

/-! Source consumer for each FIXED k<N. Concrete source center,
conditional measurable prefix reference interface, canonical ORIGINAL seed law.
No actual-flow adapter, random stopping time, covariance or accuracy claim. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateGeneralOccurrence
open MeasureTheory Numerics Numerics.AffineGraph CovarianceSetup
open AffineLowering TapeLowering NoisyLayer SourceMeanLayer
open RecursiveMeanProgram RecursiveMeanContinuation PrivateSamplingProgram
open SourceExecutableTables PrivateSamplingExecutionSchedule
open TailOccurrenceCut TailOccurrenceCut.TailCut GeneralMainFocus
open CanonicalTapeLaw CanonicalTapeMeasurability ReplaySeedMeasurability FreshChildCanonicalSeedLaw
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (N k : ℕ) (hk : k<N)
local notation "cfg" => samplingConfig main final N
local notation "c" => (fun i : Fin n => ExecutableData.size (main i))
local notation "p" => (fun i : Fin n => ExecutableData.program (main i))
local notation "en" => (fun i : Fin n => ExecutableData.enumeration (main i))
local notation "F" => finisher main final N
local notation "host" => ExecutableData.program (SamplingExecutable.build S e r Ds main final N)
local notation "dir" => (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
local notation "saved" => (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))
local notation "loop" => iterateThen c p (PrivateSamplingProgram.Config.mainSlots cfg) en (PrivateSamplingProgram.Config.layerOrigin cfg)
  (PrivateSamplingProgram.Config.mainDesignated cfg) (PrivateSamplingProgram.Config.mainResidual cfg) (PrivateSamplingProgram.Config.mainAuxiliary cfg) F

/-- Four original setup steps, three initialization batches, then exactly k
complete original layers. No shorter program or relabelled loop is evaluated. -/
def privateFocus : Focus c p (PrivateSamplingProgram.Config.mainSlots cfg) en (PrivateSamplingProgram.Config.layerOrigin cfg) (PrivateSamplingProgram.Config.mainDesignated cfg)
    (PrivateSamplingProgram.Config.mainResidual cfg) (PrivateSamplingProgram.Config.mainAuxiliary cfg) F host := by
  let f := focus c p (PrivateSamplingProgram.Config.mainSlots cfg) en (PrivateSamplingProgram.Config.layerOrigin cfg) (PrivateSamplingProgram.Config.mainDesignated cfg)
    (PrivateSamplingProgram.Config.mainResidual cfg) (PrivateSamplingProgram.Config.mainAuxiliary cfg) F N k hk batchRef dir saved
  refine ⟨f.remainingAfter,f.ctx,f.old,f.direct,f.saved,?_⟩
  change TailCut _ (PrivateSamplingProgram.code cfg)
  unfold PrivateSamplingProgram.code PrivateSamplingProgram.body initializeCenters
  exact .step _ _ _ (.step _ _ _ (.step _ _ _ (.step _ _ _
    (.batch _ _ _ (.batch _ _ _ (.batch _ _ _ f.cut))))))

local notation "foc" => privateFocus S e r Ds main final N k hk
local notation "cut" => (GeneralMainFocus.Focus.cut foc)
local notation "H" => Prefix d cut

theorem private_remaining : (GeneralMainFocus.Focus.remainingAfter foc) = N-1-k :=
  remaining_eq c p (PrivateSamplingProgram.Config.mainSlots cfg) en (PrivateSamplingProgram.Config.layerOrigin cfg) (PrivateSamplingProgram.Config.mainDesignated cfg)
    (PrivateSamplingProgram.Config.mainResidual cfg) (PrivateSamplingProgram.Config.mainAuxiliary cfg) F N k hk batchRef dir saved

/-- Complete CURRENT residual/row batches and every later layer plus finish. -/
def next : Prog (samplingSize main final) (replyCtx n (GeneralMainFocus.Focus.ctx foc)) .point :=
  .batch [] (fun j => residualDraw ((PrivateSamplingProgram.Config.mainResidual cfg) (GeneralMainFocus.Focus.remainingAfter foc) j))
    (.batch [] (noisyRow (fun j l => (PrivateSamplingProgram.Config.mainSlots cfg) (aSlot c p j l))
      (fun j l => (PrivateSamplingProgram.Config.mainSlots cfg) (residualSlot c p j l)) (GeneralMainFocus.Focus.direct foc))
      (loop (GeneralMainFocus.Focus.remainingAfter foc) batchRef
        (fun j => preserveDirect ((GeneralMainFocus.Focus.direct foc) j)) (fun q => preserveDirect ((GeneralMainFocus.Focus.saved foc) q))))

def child (i : Fin n) : Prog (samplingSize main final) (GeneralMainFocus.Focus.ctx foc) .point :=
  freshChild (p i) (en i) ((PrivateSamplingProgram.Config.mainSlots cfg) ∘ childSlot c p i) ((GeneralMainFocus.Focus.old foc) i)
    ((PrivateSamplingProgram.Config.mainDesignated cfg) (GeneralMainFocus.Focus.remainingAfter foc) i) ((PrivateSamplingProgram.Config.mainAuxiliary cfg) (GeneralMainFocus.Focus.remainingAfter foc) i)

/-- Definitional focus-to-selected-batch bridge; no assumed focus equality. -/
def batchCut : TailCut (.batch ((PrivateSamplingProgram.Config.layerOrigin cfg) (GeneralMainFocus.Focus.remainingAfter foc))
    (child S e r Ds main final N k hk) (next S e r Ds main final N k hk)) host := cut

/-- The concrete entering-center readout on the exact prefix. -/
def center (G : Point d → Point d) (x P : Point d) (i : Fin n) (h : H) : Point d :=
  storedPoint (envAt G (inp S e r Ds main final x P) cut Env.empty h) ((GeneralMainFocus.Focus.old foc) i)

set_option backward.isDefEq.respectTransparency false in
theorem center_eq_actual (G : Point d → Point d) (x P : Point d) (i : Fin n)
    (ω : FullTape (d := d) S e r Ds main final N) :
    center S e r Ds main final N k hk G x P i (split cut ω).1 =
      actualCenterAt S e r Ds main final N G x P k i ω := by
  let f := focus c p (PrivateSamplingProgram.Config.mainSlots cfg) en (PrivateSamplingProgram.Config.layerOrigin cfg)
    (PrivateSamplingProgram.Config.mainDesignated cfg) (PrivateSamplingProgram.Config.mainResidual cfg)
    (PrivateSamplingProgram.Config.mainAuxiliary cfg) F N k hk batchRef dir saved
  unfold center privateFocus
  dsimp only [id, split, envAt]
  simp only [residualDraw, run, evalInstr, run_affineRow, Env.cons]
  simp only [run_initialRow, pointResult]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  change storedPoint (envAt G (inp S e r Ds main final x P) f.cut
    (Env.prepend
      (fun j => storedPoint (entry S e r Ds main final N x P ω) (batchRef j) +
        (inp S e r Ds main final x P).coefficient (PrivateSamplingProgram.Config.noise cfg) •
          (show Point d from ((bodyTape S e r Ds main final N ω).1 j).1))
      (Env.prepend (fun j => (show Point d from ((bodyTape S e r Ds main final N ω).1 j).1))
        (entry S e r Ds main final N x P ω)))
    (split f.cut (bodyTape S e r Ds main final N ω).2.2).1) (f.old i) = _
  simpa only [actualCenterAt, enteringState] using readout_eq_cursor c p (PrivateSamplingProgram.Config.mainSlots cfg) en (PrivateSamplingProgram.Config.layerOrigin cfg) (PrivateSamplingProgram.Config.mainDesignated cfg)
      (PrivateSamplingProgram.Config.mainResidual cfg) (PrivateSamplingProgram.Config.mainAuxiliary cfg) F G (inp S e r Ds main final x P)
      N k hk batchRef dir saved
      (Env.prepend
        (fun j => storedPoint (entry S e r Ds main final N x P ω) (batchRef j) +
          (inp S e r Ds main final x P).coefficient (PrivateSamplingProgram.Config.noise cfg) •
            (show Point d from ((bodyTape S e r Ds main final N ω).1 j).1))
        (Env.prepend (fun j => (show Point d from ((bodyTape S e r Ds main final N ω).1 j).1))
          (entry S e r Ds main final N x P ω))) (bodyTape S e r Ds main final N ω).2.2 i

/-- Y/U are explicitly maps on this actual prefix, not arbitrary full-tape
observations. Instantiating the true reference-flow formulas is a separate gate. -/
def W (G : Point d → Point d) (x P : Point d) (Y U : Fin n → H → Point d)
    (i : Fin n) (h : H) : Point d × (Point d × Point d) :=
  (center S e r Ds main final N k hk G x P i h, (Y i h,U i h))

def W_num (G : Point d → Point d) (x : Point d) (Y U : Fin n → H → Point d)
    (i : Fin n) (ω : FullTape (d := d) S e r Ds main final N) :=
  (SharedLayerRms.iterate
    (fun j (ω : FullTape (d := d) S e r Ds main final N) => x + (r*S.mesh.location m (e j)) • (show Point d from ω.2.1))
    (samplingMatrix S e r)
    (residualRoot (samplingMatrix S e r) (samplingNoise S r Ds) (r^2))
    (evaluator S e r Ds main final N G (fun j (ω : FullTape (d := d) S e r Ds main final N) => U j (split cut ω).1))
    (residualNoise S e r Ds main final N)
    (fun j (ω : FullTape (d := d) S e r Ds main final N) => initial S e r Ds main final N x ω j) k i ω,
   (Y i (split cut ω).1,U i (split cut ω).1))

theorem W_eq_W_num (G : Point d → Point d) (x P : Point d)
    (Y U : Fin n → H → Point d) (i : Fin n)
    (ω : FullTape (d := d) S e r Ds main final N) :
    W S e r Ds main final N k hk G x P Y U i (split cut ω).1 =
      W_num S e r Ds main final N k hk G x Y U i ω := by
  unfold W W_num
  rw [center_eq_actual S e r Ds main final N k hk G x P i ω]
  rw [enteringCenter_eq_iterate S e r Ds main final N G x P
    (fun j (ω : FullTape (d := d) S e r Ds main final N) => U j (split cut ω).1) k (Nat.le_of_lt hk)]

theorem W_measurable (G : Point d → Point d) (hG : Measurable G) (x P : Point d)
    (Y U : Fin n → H → Point d) (i : Fin n)
    (hY : @Measurable H _ (prefixSpace d cut) _ (Y i))
    (hU : @Measurable H _ (prefixSpace d cut) _ (U i)) :
    @Measurable H _ (prefixSpace d cut) _ (W S e r Ds main final N k hk G x P Y U i) :=
  (prefixReadout_measurable G hG cut (inp S e r Ds main final x P) Env.empty ((GeneralMainFocus.Focus.old foc) i)).prodMk
    (hY.prodMk hU)

/-- Same V, original R, exact fixed PRIVATE childRoot. -/
def transformedChildSeed (i : Fin n) :=
  transformedSeed (d := d) (p i) (en i)
    (childRoot (samplingNoise S r Ds) (S.radius r (e i)) (main i).shiftVector) ∘
    freshChildTapeEquiv (d := d) (p i) (en i) ((PrivateSamplingProgram.Config.mainSlots cfg) ∘ childSlot c p i)
      ((GeneralMainFocus.Focus.old foc) i) ((PrivateSamplingProgram.Config.mainDesignated cfg) (GeneralMainFocus.Focus.remainingAfter foc) i) ((PrivateSamplingProgram.Config.mainAuxiliary cfg) (GeneralMainFocus.Focus.remainingAfter foc) i)

set_option backward.isDefEq.respectTransparency false in
/-- Exact canonical product at each fixed k<N. The whole batch/continuation is
still present in batchCut; selected projection occurs only after factorization. -/
theorem W_num_canonical_joint (L : PrimitiveLaws d) (G : Point d → Point d)
    (hG : Measurable G) (x P : Point d) (Y U : Fin n → H → Point d) (i : Fin n)
    (hY : @Measurable H _ (prefixSpace d cut) _ (Y i))
    (hU : @Measurable H _ (prefixSpace d cut) _ (U i)) :
    let : MeasurableSpace (Tape d host) := tapeSpace d host
    let : MeasurableSpace H := prefixSpace d cut
    let : MeasurableSpace (ResidualTape (p i)) := residualSpace (p i)
    let : MeasurableSpace (Tape d (p i)) := tapeSpace d (p i)
    (tapeLaw L host).map (fun ω =>
      (W_num S e r Ds main final N k hk G x Y U i ω,
       transformedChildSeed S e r Ds main final N k hk i ((split cut ω).2.1 i))) =
    ((prefixLaw L cut).map (W S e r Ds main final N k hk G x P Y U i)).prod
      ((sourceSeedLaw L (p i) (tapeShape (p i)).gaussianBlocks).map
        (transformedSeed (d := d) (p i) (en i)
          (childRoot (samplingNoise S r Ds) (S.radius r (e i)) (main i).shiftVector))) := by
  dsimp only
  let : MeasurableSpace (ResidualTape (p i)) := residualSpace (p i)
  let : MeasurableSpace (Tape d (p i)) := tapeSpace d (p i)
  have hj := transformed_fresh_seed_joint c p en
    (fun j => (PrivateSamplingProgram.Config.mainSlots cfg) ∘ childSlot c p j) (GeneralMainFocus.Focus.old foc) ((PrivateSamplingProgram.Config.layerOrigin cfg) (GeneralMainFocus.Focus.remainingAfter foc))
    ((PrivateSamplingProgram.Config.mainDesignated cfg) (GeneralMainFocus.Focus.remainingAfter foc)) ((PrivateSamplingProgram.Config.mainAuxiliary cfg) (GeneralMainFocus.Focus.remainingAfter foc))
    (next S e r Ds main final N k hk) (batchCut S e r Ds main final N k hk) L i
    (childRoot (samplingNoise S r Ds) (S.radius r (e i)) (main i).shiftVector)
    (W S e r Ds main final N k hk G x P Y U i)
    (W_measurable S e r Ds main final N k hk G hG x P Y U i hY hU)
  dsimp only at hj
  rw [transformed_freshChild_law] at hj
  simpa only [transformedChildSeed, batchCut, W_eq_W_num S e r Ds main final N k hk G x P Y U i] using hj

end AcceleratedLogConcave.Oracle.PrivateGeneralOccurrence
