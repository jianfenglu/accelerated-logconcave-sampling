import AcceleratedLogConcave.Oracle.PrivateOccurrencePath
import AcceleratedLogConcave.Oracle.FreshChildJointLaw

/-! One concrete PRIVATE occurrence: k=0,
N=M+1. All statements use the concrete prefix wrapper, original full tape and
induced child marginal. Phi and u depend on the actual setup Gaussian only;
their measurability is explicit, not inferred for arbitrary full-tape targets. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateFirstOccurrenceConsumer
open MeasureTheory Numerics Numerics.AffineGraph CovarianceSetup
open AffineLowering TapeLowering NoisyLayer SourceMeanLayer
open RecursiveMeanProgram RecursiveMeanContinuation PrivateSamplingProgram
open SourceExecutableTables PrivateSamplingExecutionSchedule
open TailOccurrenceCut TailOccurrenceCut.TailCut
open CanonicalTapeLaw CanonicalTapeMeasurability ReplaySeedMeasurability

variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (M : ℕ)
local notation "cfg" => samplingConfig main final (M+1)
local notation "c" => (fun i : Fin n => ExecutableData.size (main i))
local notation "p" => (fun i : Fin n => ExecutableData.program (main i))
local notation "en" => (fun i : Fin n => ExecutableData.enumeration (main i))
local notation "rho" => samplingNoise S r Ds
local notation "F" => finisher main final (M+1)
local notation "Δ" => replyCtx n (replyCtx n (Entry n))
local notation "dir" => (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
local notation "saved" => (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))
local notation "host" => ExecutableData.program (SamplingExecutable.build S e r Ds main final (M+1))

def children (i : Fin n) : Prog (samplingSize main final) Δ .point :=
  freshChild (p i) (en i) ((PrivateSamplingProgram.Config.mainSlots cfg) ∘ childSlot c p i) (batchRef i)
    ((PrivateSamplingProgram.Config.mainDesignated cfg) M i) ((PrivateSamplingProgram.Config.mainAuxiliary cfg) M i)

/-- Includes the CURRENT residual draw/row batches, all M remaining layers,
and the unmodified paid final continuation. -/
def suffix : Prog (samplingSize main final) (replyCtx n Δ) .point :=
  .batch [] (fun i => residualDraw ((PrivateSamplingProgram.Config.mainResidual cfg) M i))
    (.batch [] (noisyRow (fun j k => (PrivateSamplingProgram.Config.mainSlots cfg) (aSlot c p j k))
      (fun j k => (PrivateSamplingProgram.Config.mainSlots cfg) (residualSlot c p j k)) dir)
      (iterateThen c p (PrivateSamplingProgram.Config.mainSlots cfg) en (PrivateSamplingProgram.Config.layerOrigin cfg) (PrivateSamplingProgram.Config.mainDesignated cfg)
        (PrivateSamplingProgram.Config.mainResidual cfg) (PrivateSamplingProgram.Config.mainAuxiliary cfg) F M batchRef
        (fun j => preserveDirect (dir j)) (fun q => preserveDirect (saved q))))

def firstCut : TailCut
    (.batch ((PrivateSamplingProgram.Config.layerOrigin cfg) M) (children main final M)
      (suffix main final M)) host := by
  change TailCut _ (PrivateSamplingProgram.code cfg)
  unfold PrivateSamplingProgram.code PrivateSamplingProgram.body initializeCenters
  exact .step _ _ _ (.step _ _ _ (.step _ _ _ (.step _ _ _
    (.batch _ _ _ (.batch _ _ _ (.batch _ _ _ .here))))))

local notation "cut" => firstCut S e r Ds main final M
local notation "H" => Prefix d cut

/-- Literal prefix projections. No current-child coordinate is read. -/
def zeta (h : H) : Point d := h.2.1
def eta (i : Fin n) (h : H) : Point d := (h.2.2.2.2.2.1 i).1

def prefixW (x : Point d) (Phi u : Fin n → Point d → Point d) (i : Fin n)
    (h : H) : Point d × (Point d × Point d) :=
  (x + (r*S.mesh.location m (e i)) • zeta S e r Ds main final M h +
      rho • eta S e r Ds main final M i h,
   (Phi i (zeta S e r Ds main final M h) + rho • eta S e r Ds main final M i h,
    u i (zeta S e r Ds main final M h)))

def W_num (G : Point d → Point d) (x : Point d)
    (Phi u : Fin n → Point d → Point d) (i : Fin n)
    (ω : FullTape (d := d) S e r Ds main final (M+1)) :=
  (SharedLayerRms.iterate
    (fun j (ω : FullTape (d := d) S e r Ds main final (M+1)) => x + (r*S.mesh.location m (e j)) • (show Point d from (Prod.fst (Prod.snd ω))))
    (samplingMatrix S e r) (residualRoot (samplingMatrix S e r) rho (r^2))
    (evaluator S e r Ds main final (M+1) G (fun j (ω : FullTape (d := d) S e r Ds main final (M+1)) => u j (Prod.fst (Prod.snd ω))))
    (residualNoise S e r Ds main final (M+1))
    (fun j (ω : FullTape (d := d) S e r Ds main final (M+1)) => initial S e r Ds main final (M+1) x ω j) 0 i ω,
   (Phi i (Prod.fst (Prod.snd ω)) + rho • (show Point d from
      ((bodyTape S e r Ds main final (M+1) ω).1 i).1), u i (Prod.fst (Prod.snd ω))))

/-- No final-state equality is used: zero iterations are the actual initial
state, and split is the exact seven-node source prefix reassociation. -/
theorem prefixW_eq_W_num (G : Point d → Point d) (x : Point d)
    (Phi u : Fin n → Point d → Point d) (i : Fin n)
    (ω : FullTape (d := d) S e r Ds main final (M+1)) :
    prefixW S e r Ds main final M x Phi u i (split cut ω).1 =
      W_num S e r Ds main final M G x Phi u i ω := by
  rfl

/-- The received repaired wrapper identifies the SAME center at k=0≤M+1.
This does not run the suffix and does not replace it by a shorter execution. -/
theorem actual_readout_eq_prefixW (G : Point d → Point d) (x P : Point d)
    (Phi u : Fin n → Point d → Point d) (i : Fin n)
    (ω : FullTape (d := d) S e r Ds main final (M+1)) :
    actualCenterAt S e r Ds main final (M+1) G x P 0 i ω =
      (prefixW S e r Ds main final M x Phi u i (split cut ω).1).1 := by
  rw [enteringCenter_eq_iterate S e r Ds main final (M+1) G x P
    (fun j (ω : FullTape (d := d) S e r Ds main final (M+1)) => u j (Prod.fst (Prod.snd ω))) 0 (Nat.zero_le _)]
  rfl

/-- Direct interpreter prefix check, independent of final-state equality.
All preceding row children are evaluated before reading batchRef. -/
theorem envAt_readout_eq_prefixW (G : Point d → Point d) (x P : Point d)
    (Phi u : Fin n → Point d → Point d) (i : Fin n) (h : H) :
    storedPoint (envAt G (inp S e r Ds main final x P) cut Env.empty h) (batchRef i) =
      (prefixW S e r Ds main final M x Phi u i h).1 := by
  dsimp only [firstCut, id, envAt]
  erw [prepend_batchRef]
  simp only [residualDraw, run, evalInstr, run_affineRow, Env.cons, pointResult, evalPure]
  erw [run_initialRow]
  simp only [pointResult]
  erw [prepend_batchRef]
  simp [storedPoint, Env.cons, prefixW, zeta, eta, samplingConfig,
    SourceExecutableTables.samplingScalarTable]
  rfl

/-- Explicit projection/finite-linear-map measurability, no independence premise.
For the actual flow benchmark, supply its separately proved measurable Phi/u. -/
theorem prefixW_measurable (x : Point d) (Phi u : Fin n → Point d → Point d)
    (i : Fin n) (hPhi : Measurable (Phi i)) (hu : Measurable (u i)) :
    @Measurable H (Point d × (Point d × Point d)) (prefixSpace d cut) _
      (prefixW S e r Ds main final M x Phi u i) := by
  let : MeasurableSpace H := prefixSpace d cut
  have hz : Measurable (zeta S e r Ds main final M : H → Point d) :=
    measurable_snd.fst
  let : ∀ j : Fin n, MeasurableSpace (Tape d ((residualDraw ((PrivateSamplingProgram.Config.initialOrigin cfg) j) : Prog (samplingSize main final) (replyCtx n [.point, .scalar, .point, .point]) .point))) :=
    fun j => tapeSpace d _
  have he : Measurable (eta S e r Ds main final M i : H → Point d) :=
    ((measurable_pi_apply i).comp measurable_snd.snd.snd.snd.snd.fst).fst
  exact ((hz.const_smul (r*S.mesh.location m (e i))).const_add x |>.add
    (he.const_smul rho)).prodMk
      (((hPhi.comp hz).add (he.const_smul rho)).prodMk (hu.comp hz))

/-- Exact original seed extraction: V, full Z array, ORIGINAL complete R. -/
def seed (i : Fin n) :=
  freshChildTapeEquiv (d := d) (p i) (en i) ((PrivateSamplingProgram.Config.mainSlots cfg) ∘ childSlot c p i)
    (batchRef i : Ref Δ .point) ((PrivateSamplingProgram.Config.mainDesignated cfg) M i) ((PrivateSamplingProgram.Config.mainAuxiliary cfg) M i)

/-- The exact PRIVATE deterministic childRoot, not an arbitrary replacement. -/
def rootSeed (i : Fin n) :=
  transformedSeed (d := d) (p i) (en i)
    (childRoot rho (S.radius r (e i)) (main i).shiftVector) ∘
      seed (d := d) main final M i

/-- Before any marginalization, retain the entire sibling array and suffix. -/
theorem full_first_cut (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d host) := tapeSpace d host
    let : MeasurableSpace H := prefixSpace d cut
    let : MeasurableSpace (Tape d (.batch ((PrivateSamplingProgram.Config.layerOrigin cfg) M)
      (children main final M) (suffix main final M))) :=
        tapeSpace d _
    @MeasurePreserving _ _ (tapeSpace d host)
      ((prefixSpace d cut).prod (tapeSpace d (.batch ((PrivateSamplingProgram.Config.layerOrigin cfg) M) (children main final M) (suffix main final M))))
      (split (d := d) cut) (tapeLaw L host)
      ((prefixLaw L cut).prod (tapeLaw L (.batch ((PrivateSamplingProgram.Config.layerOrigin cfg) M)
        (children main final M) (suffix main final M)))) :=
by
  dsimp only
  exact measurePreserving_split L cut

/-- One explicit k<N/selected-child consumer. Right marginal stays induced.
All siblings and the complete suffix are retained in split BEFORE projection. -/
theorem W_num_rootSeed_joint (L : PrimitiveLaws d) (G : Point d → Point d)
    (x : Point d) (Phi u : Fin n → Point d → Point d) (i : Fin n)
    (hPhi : Measurable (Phi i)) (hu : Measurable (u i)) :
    let : MeasurableSpace (Tape d host) := tapeSpace d host
    let : MeasurableSpace H := prefixSpace d cut
    let : MeasurableSpace (Tape d (children main final M i)) :=
      tapeSpace d (children main final M i)
    let : MeasurableSpace (Tape d (p i)) := tapeSpace d (p i)
    (tapeLaw L host).map (fun ω =>
      (W_num S e r Ds main final M G x Phi u i ω,
       rootSeed S e r Ds main final M i ((split cut ω).2.1 i))) =
    ((prefixLaw L cut).map (prefixW S e r Ds main final M x Phi u i)).prod
      ((tapeLaw L (children main final M i)).map
        (show Tape d (children main final M i) → Point d × Tape d (p i) from rootSeed S e r Ds main final M i)) := by
  dsimp only
  convert
    transformed_fresh_seed_joint c p en
      (fun j => (PrivateSamplingProgram.Config.mainSlots cfg) ∘ childSlot c p j) batchRef ((PrivateSamplingProgram.Config.layerOrigin cfg) M)
      ((PrivateSamplingProgram.Config.mainDesignated cfg) M) ((PrivateSamplingProgram.Config.mainAuxiliary cfg) M)
      (suffix main final M) cut L i
      (childRoot rho (S.radius r (e i)) (main i).shiftVector)
      (prefixW S e r Ds main final M x Phi u i)
      (prefixW_measurable S e r Ds main final M x Phi u i hPhi hu) using 1 <;> rfl

end AcceleratedLogConcave.Oracle.PrivateFirstOccurrenceConsumer
