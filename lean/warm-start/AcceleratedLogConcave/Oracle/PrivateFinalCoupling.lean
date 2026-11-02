import AcceleratedLogConcave.Oracle.PrivateCausalLayer
import AcceleratedLogConcave.Oracle.PrivateRecursiveBatchBudget

/-! The actual fresh final batch of the private sampler, after every main
layer (also zero layers). Reference augmentation stops before the two actual
residual/reserve draws and therefore preserves their whole joint suffix. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateFinalCoupling
open Numerics Numerics.AffineGraph SourceExecutableTables PrivateSamplingProgram
open AffineLowering TapeLowering NoisyLayer SourceMeanLayer
open RecursiveMeanProgram RecursiveMeanContinuation PrivateSamplingExecutionSchedule
open CanonicalTapeMeasurability CanonicalTapeLaw TailOccurrenceCut TailCut PrivateCausalLayer
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
local notation "cfg" => samplingConfig main final N
local notation "c" => (fun i : Fin n => (main i).size)
local notation "p" => (fun i : Fin n => (main i).program)
local notation "en" => (fun i : Fin n => (main i).enumeration)
local notation "F" => finisher main final N
local notation "host" => (SamplingExecutable.build S e r Ds main final N).program
local notation "dir" => (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
local notation "saved" => (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))

/-- Literal paid-finish cut after the complete private setup and all N layers. -/
def privateFinish : FinishFocus F host := by
  let f := atFinish c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated
    (cfg).mainResidual (cfg).mainAuxiliary F N batchRef dir saved
  refine ⟨f.ctx,f.old,f.direct,f.saved,?_⟩
  change TailCut _ (PrivateSamplingProgram.code cfg)
  unfold PrivateSamplingProgram.code PrivateSamplingProgram.body initializeCenters
  exact .step _ _ _ (.step _ _ _ (.step _ _ _ (.step _ _ _
    (.batch _ _ _ (.batch _ _ _ (.batch _ _ _ f.cut))))))

variable (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (final i).shiftVector ≤ Ds^2)

/-- Every final slot and origin is the actual private public-table occurrence.
Unlike main batches, this uses the final child array and finalWidth. -/
def data {Γ : Ctx} (old : Fin n → Ref Γ .point) :
    FreshChildBatchCoupling.Data n (samplingSize main final) Γ where
  child := final
  slot := (cfg).finalSlots
  old := old
  designated := (cfg).finalDesignated
  auxiliary := (cfg).finalAuxiliary
  rho _ := samplingNoise S r Ds
  radius i := S.radius r (e i)
  Ds := Ds
  rho_nonneg _ := (RecursiveExecutableDomain.sampling_noise_pos S r Ds hr hDs).le
  radius_pos i := S.radius_pos r hr (e i)
  Ds_pos := hDs
  shift_budget := hmass
  small i := RecursiveExecutableDomain.sampling_noise_separation S r Ds hr hDs (e i)

variable {Γ : Ctx} (old : Fin n → Ref Γ .point) (direct : Ref Γ .point)
local notation "B" => data S e r Ds main final N hr hDs hmass old

/-- Exactly the two fresh Gaussian steps and literal output row. -/
def suffix : Prog (samplingSize main final) (replyCtx n Γ) .point :=
  .step (cfg).finalResidual .gaussian
    (.step (cfg).finalReserve .gaussian
      (affineRow [] (.there (.there (RefMap.shiftMany n direct)))
        ((List.ofFn fun i => ((cfg).rowWeight i,.there (.there (batchRef i)))) ++
          [((cfg).beta,.there .here),((cfg).reserve,.here)])))

theorem finish_eq_batch :
    PrivateSamplingProgram.finish cfg old direct =
      .batch (cfg).finalOrigin (FreshChildBatchCoupling.program B) (suffix main final N direct) := rfl

local instance canonicalTapeSpace {cc : ℕ} {Ξ : Ctx} {τ : Ty} (program : Prog cc Ξ τ) :
    MeasurableSpace (Tape d program) := tapeSpace d program

variable {Ξ : Ctx} {parent : Prog (samplingSize main final) Ξ .point}
  (cut : TailCut (.batch (samplingConfig main final N).finalOrigin (FreshChildBatchCoupling.program (data S e r Ds main final N hr hDs hmass old))
    (suffix main final N direct)) parent)
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d (afterBatch cut)
variable {A H : Type*} [MeasurableSpace A] [MeasurableSpace H]
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass old))
  (coarse : A × Prefix d cut → H) (hcoarse : Measurable coarse)
  (center : Fin n → H → Point d) (hcenter : ∀ i, Measurable (center i))
  (comparison : Fin n → A × Prefix d cut → Point d)
  (hcomparison : ∀ i, Measurable (comparison i))

/-- Observe only augmented past and the consumed literal fresh final batch. -/
def observation (z : A × Prefix d (afterBatch cut)) : H × (∀ i, FreshChildBatchCoupling.Raw d (data S e r Ds main final N hr hDs hmass old) i) :=
  let parts : Prefix d cut × (∀ i, Tape d (FreshChildBatchCoupling.program (data S e r Ds main final N hr hDs hmass old) i)) :=
    batchParts (d := d) cut z.2
  (coarse (z.1,parts.1),fun i => (comparison i (z.1,parts.1),parts.2 i))

include hcoarse hcomparison in
theorem observation_measurable : Measurable
    (observation S e r Ds main final N hr hDs hmass old direct cut coarse comparison) := by
  have hp : Measurable (fun z : A × Prefix d (afterBatch cut) => batchParts cut z.2) :=
    (measurable_batchParts (d := d) cut).comp measurable_snd
  have hold := measurable_fst.prodMk hp.fst
  exact (hcoarse.comp hold).prodMk (Measurable.of_eval fun i =>
    ((hcomparison i).comp hold).prodMk ((measurable_pi_apply i).comp hp.snd))

/-- Use the actual lower parameterized disintegrations, rather than a supplied
final-output law. The two residual/reserve Gaussian steps are still unread. -/
def referenceConditional : Kernel (A × Prefix d (afterBatch cut)) (Fin n → Point d) :=
  (FreshChildBatchCoupling.referenceBatch L hL (data S e r Ds main final N hr hDs hmass old) J center hcenter).comap
    (observation S e r Ds main final N hr hDs hmass old direct cut coarse comparison)
    (observation_measurable S e r Ds main final N hr hDs hmass old direct cut
      coarse hcoarse comparison hcomparison)

instance referenceConditional_markov : IsMarkovKernel
    (referenceConditional S e r Ds main final N hr hDs hmass old direct cut
      L hL J coarse hcoarse center hcenter comparison hcomparison) := by
  unfold referenceConditional
  infer_instance

/-- Keep the complete parent and history while adjoining returned final references. -/
def kernel : Kernel (A × Tape d parent) ((A × Tape d parent) × (Fin n → Point d)) :=
  CausalTailHistory.onTape L (afterBatch cut)
    (referenceConditional S e r Ds main final N hr hDs hmass old direct cut
      L hL J coarse hcoarse center hcenter comparison hcomparison)

instance kernel_markov : IsMarkovKernel
    (kernel S e r Ds main final N hr hDs hmass old direct cut
      L hL J coarse hcoarse center hcenter comparison hcomparison) := by
  unfold kernel
  infer_instance

theorem original_preserved :
    (kernel S e r Ds main final N hr hDs hmass old direct cut
      L hL J coarse hcoarse center hcenter comparison hcomparison).fst = Kernel.id :=
  CausalTailHistory.onTape_original L (afterBatch cut) _

/-- The complete literal residual/reserve/output suffix stays a fresh product;
no claim of independence from conditioned original P is introduced. -/
theorem whole_suffix (oldLaw : Measure (A × Tape d parent))
    (μ : Measure (A × Prefix d cut)) [SFinite μ]
    (hsplit : oldLaw.map (CausalTailHistory.unpack cut) =
      μ.prod (tapeLaw L (PrivateSamplingProgram.finish (samplingConfig main final N) old direct))) :
    ((kernel S e r Ds main final N hr hDs hmass old direct cut
      L hL J coarse hcoarse center hcenter comparison hcomparison) ∘ₘ oldLaw).map
      (CausalTailHistory.unpackExtended (afterBatch cut)) =
      ((advancedLaw L cut μ) ⊗ₘ
        (referenceConditional S e r Ds main final N hr hDs hmass old direct cut
          L hL J coarse hcoarse center hcenter comparison hcomparison)).prod
        (tapeLaw L (suffix main final N direct)) := by
  exact CausalTailHistory.whole_suffix_fresh_of_split L (afterBatch cut) oldLaw
    (advancedLaw L cut μ) (advanced_split_of_split L cut oldLaw μ hsplit) _

end AcceleratedLogConcave.Oracle.PrivateFinalCoupling
