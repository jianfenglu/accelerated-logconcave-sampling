import AcceleratedLogConcave.Oracle.MeanMainBatchCoupling
import AcceleratedLogConcave.Oracle.PrivateChronologicalCoupling

/-! Actual mean initialization on an arbitrary retained incoming source law.
The entire incoming augmented history and consumed original prefix form the
fixed coarse host. Only the original unread suffix is a fresh product factor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanInitialComparison
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance

local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)

abbrev Host := SourceMeanExecutable.program M nodes anchors seeds main final sampling N

def entryCut := afterBatch (afterBatch (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))

local instance : MeasurableSpace
    (Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) := prefixSpace d _
local instance : MeasurableSpace (Prefix d (entryCut M nodes anchors seeds main final sampling N)) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (afterBatch (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)))) := prefixSpace d _

abbrev Coarse (A : Type*) :=
  A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)
abbrev History (A : Type*) :=
  Coarse (d := d) M nodes anchors seeds main final sampling N A ×
    ((Fin N → Fin n → Point d) × (Fin n → Point d))

def coordinates (p : Prefix d (entryCut M nodes anchors seeds main final sampling N)) :
    Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) × (Fin n → Point d) :=
  let rows := batchParts (afterBatch (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) p
  let noise := batchParts (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) rows.1
  (noise.1,fun i => (noise.2 i).1)

theorem coordinates_measurable : Measurable (coordinates (d := d) M nodes anchors seeds main final sampling N) := by
  have hr := measurable_batchParts (d := d)
    (afterBatch (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))
  have hn := (measurable_batchParts (d := d)
    (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)).comp hr.fst
  exact hn.fst.prodMk (Measurable.of_eval fun i => ((measurable_pi_apply i).comp hn.snd).fst)

variable {A : Type*} [MeasurableSpace A]

def past (z : A × Prefix d (entryCut M nodes anchors seeds main final sampling N)) :
    History (d := d) M nodes anchors seeds main final sampling N A :=
  let p := coordinates M nodes anchors seeds main final sampling N z.2
  ((z.1,p.1),((fun _ => 0),p.2))

theorem past_measurable : Measurable (past (d := d) (A := A) M nodes anchors seeds main final sampling N) := by
  have hp := (coordinates_measurable (d := d) M nodes anchors seeds main final sampling N).comp
    (measurable_snd : Measurable (Prod.snd : A × Prefix d (entryCut M nodes anchors seeds main final sampling N) → _))
  exact (measurable_fst.prodMk hp.fst).prodMk (measurable_const.prodMk hp.snd)

def prepare : A × Tape d (Host M nodes anchors seeds main final sampling N) →
    History (d := d) M nodes anchors seeds main final sampling N A ×
      Tape d (Host M nodes anchors seeds main final sampling N) :=
  PrivateChronologicalCoupling.changeHistory (entryCut M nodes anchors seeds main final sampling N)
    (past M nodes anchors seeds main final sampling N)

variable (L : PrimitiveLaws d)

local instance tape_probability {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    IsProbabilityMeasure (tapeLaw L p) := tapeLaw_probability L p

include L in
theorem prepare_measurable : Measurable (prepare (d := d) (A := A) M nodes anchors seeds main final sampling N) :=
  PrivateChronologicalCoupling.changeHistory_measurable L _ _
    (past_measurable M nodes anchors seeds main final sampling N)

def initialLaw (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :=
  ρ.map (prepare M nodes anchors seeds main final sampling N)

def prefixLaw
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) :=
  (advancedLaw L (afterBatch (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))
    (advancedLaw L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) μ)).map
      (PrivateChronologicalCoupling.changePrefix (entryCut M nodes anchors seeds main final sampling N)
        (past M nodes anchors seeds main final sampling N))

theorem initial_whole_suffix
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) =
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :
    (initialLaw M nodes anchors seeds main final sampling N ρ).map
      (CausalTailHistory.unpack (entryCut M nodes anchors seeds main final sampling N)) =
      (prefixLaw M nodes anchors seeds main final sampling N L μ).prod
        (tapeLaw L (iterateThen (fun i => (main i).size) (fun i => (main i).program)
          (mainSlot (a := a) main final sampling) (fun i => (main i).enumeration)
          layerOrigin mainDesignated residualOrigin (mainAuxiliary main)
          (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling) N batchRef
          (fun i => RefMap.shiftMany n (RefMap.shiftMany n (MeanExecutablePrefix.direct i)))
          (fun q => RefMap.shiftMany n (RefMap.shiftMany n q)))) := by
  have hn := consume_two_batches L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) ρ μ hsplit
  have hμ0 : SFinite (advancedLaw L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) μ) :=
    advancedLaw_sFinite L _ _
  have hμ1 : SFinite (advancedLaw L (afterBatch (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))
      (advancedLaw L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) μ)) :=
    advancedLaw_sFinite L _ _
  exact PrivateChronologicalCoupling.changeHistory_split L _ _
    (past_measurable M nodes anchors seeds main final sampling N) ρ
      (advancedLaw L (afterBatch (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))
        (advancedLaw L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) μ)) hn

include L in
theorem initial_comparison_law (hL : L.pointDraw = stdGaussian (Point d))
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) =
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :
    (initialLaw M nodes anchors seeds main final sampling N ρ).map (fun z => (z.1.1,z.1.2.2)) =
      μ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  let _ : IsProbabilityMeasure (tapeLaw L
    (body (a := a) (h := h) M nodes main final sampling N)) := tapeLaw_probability L _
  have hs : MeasurePreserving
      (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) ρ
      (μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :=
    ⟨CausalTailHistory.measurable_unpack L _,hsplit⟩
  have hnoise : MeasurePreserving
      (fun ω : Tape d (body (a := a) (h := h) M nodes main final sampling N) =>
        fun i : Fin n => (ω.1 i).1)
      (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))
      (Measure.pi fun _ : Fin n => L.pointDraw) :=
    (residualBatch_preserving (c := SourceMeanExecutable.size (a := a) main final sampling)
    (Γ := SourceMeanExecutionRms.Ready n m h) L (initialOrigin (n := n))).comp
      measurePreserving_fst
  rw [hL] at hnoise
  have hp := ((MeasurePreserving.id μ).prod hnoise).comp hs
  rw [initialLaw,Measure.map_map (measurable_fst.fst.prodMk measurable_fst.snd.snd)
    (prepare_measurable M nodes anchors seeds main final sampling N L)]
  simpa only [Function.comp_def,prepare,PrivateChronologicalCoupling.changeHistory,
    past,coordinates,entryCut,split_afterBatch,batchParts_append,CausalTailHistory.unpack,Prod.map,id_eq]
    using hp.map_eq
end AcceleratedLogConcave.Oracle.MeanInitialComparison
