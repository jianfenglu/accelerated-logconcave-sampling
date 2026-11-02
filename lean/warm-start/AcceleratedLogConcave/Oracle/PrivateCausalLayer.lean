import AcceleratedLogConcave.Oracle.PrivateGeneralOccurrence
import AcceleratedLogConcave.Oracle.CausalTailHistory
import AcceleratedLogConcave.Oracle.TailCutExecution
import AcceleratedLogConcave.Oracle.FreshChildBatchCoupling
import AcceleratedLogConcave.Oracle.RecursiveExecutableDomain

/-! Advance the causal cut through the complete literal current child batch.
The original tape and correlated augmented history are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateCausalLayer
open CanonicalTapeMeasurability CanonicalTapeLaw TailOccurrenceCut TailCut

section BatchCut
variable {d c n : ℕ} {Γ Δ : Ctx} {τ σ : Ty} {p : Prog c Γ τ}
  {o : Origin} {children : Fin n → Prog c Δ .point}
  {next : Prog c (List.replicate n .point ++ Δ) σ}
  (cut : TailCut (.batch o children next) p)

def afterBatch : TailCut next p :=
  TailCut.trans (TailCut.batch o children next TailCut.here) cut

def appendBatch : {Γ : Ctx} → {τ : Ty} → {p : Prog c Γ τ} →
    (cut : TailCut (.batch o children next) p) →
    Prefix d cut → (∀ i, Tape d (children i)) → Prefix d (afterBatch cut)
  | _, _, _, .here, _, t => (t,PUnit.unit)
  | _, _, _, .step _ _ _ cut, h, t => (h.1,appendBatch cut h.2 t)
  | _, _, _, .batch _ _ _ cut, h, t => (h.1,appendBatch cut h.2 t)

def batchParts : {Γ : Ctx} → {τ : Ty} → {p : Prog c Γ τ} →
    (cut : TailCut (.batch o children next) p) →
    Prefix d (afterBatch cut) → Prefix d cut × (∀ i, Tape d (children i))
  | _, _, _, .here, h => (PUnit.unit,h.1)
  | _, _, _, .step _ _ _ cut, h =>
      let z := batchParts cut h.2; ((h.1,z.1),z.2)
  | _, _, _, .batch _ _ _ cut, h =>
      let z := batchParts cut h.2; ((h.1,z.1),z.2)

theorem batchParts_append (h : Prefix d cut) (t : ∀ i, Tape d (children i)) :
    batchParts cut (appendBatch cut h t) = (h,t) := by
  induction cut with
  | here => cases h; rfl
  | step o a q cut ih => cases h; simp only [appendBatch,batchParts,ih]
  | batch o cs q cut ih => cases h; simp only [appendBatch,batchParts,ih]

theorem join_afterBatch (h : Prefix d cut) (t : ∀ i, Tape d (children i))
    (s : Tape d next) :
    join (afterBatch cut) (appendBatch cut h t,s) = join cut (h,(t,s)) := by
  induction cut with
  | here => rfl
  | step o a q cut ih =>
      rcases h with ⟨a,h⟩
      change (a,join (afterBatch cut) (appendBatch cut h t,s)) = (a,join cut (h,(t,s)))
      rw [ih]
  | batch o cs q cut ih =>
      rcases h with ⟨a,h⟩
      change (a,join (afterBatch cut) (appendBatch cut h t,s)) = (a,join cut (h,(t,s)))
      rw [ih]

theorem split_afterBatch (ω : Tape d p) :
    split (afterBatch cut) ω =
      (appendBatch cut (split cut ω).1 (split cut ω).2.1,(split cut ω).2.2) := by
  induction cut with
  | here => rfl
  | step o a q cut ih =>
      rcases ω with ⟨a,t⟩
      change ((a,(split (afterBatch cut) t).1),(split (afterBatch cut) t).2) =
        ((a,appendBatch cut (split cut t).1 (split cut t).2.1),(split cut t).2.2)
      rw [ih]
  | batch o cs q cut ih =>
      rcases ω with ⟨a,t⟩
      change ((a,(split (afterBatch cut) t).1),(split (afterBatch cut) t).2) =
        ((a,appendBatch cut (split cut t).1 (split cut t).2.1),(split cut t).2.2)
      rw [ih]

theorem measurable_appendBatch :
    let : MeasurableSpace (Prefix d cut) := prefixSpace d cut
    let : ∀ i, MeasurableSpace (Tape d (children i)) := fun _ => tapeSpace d _
    let : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d _
    Measurable (fun z : Prefix d cut × (∀ i, Tape d (children i)) => appendBatch cut z.1 z.2) := by
  induction cut with
  | here => exact measurable_snd.prodMk measurable_const
  | step o a q cut ih =>
      let : MeasurableSpace (a.Tape d) := instrSpace d a
      let : MeasurableSpace (Prefix d cut) := prefixSpace d cut
      let : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d _
      let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d _
      exact measurable_fst.fst.prodMk (ih.comp (measurable_fst.snd.prodMk measurable_snd))
  | batch o cs q cut ih =>
      let : ∀ i, MeasurableSpace (Tape d (cs i)) := fun i => tapeSpace d _
      let : MeasurableSpace (Prefix d cut) := prefixSpace d cut
      let : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d _
      let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d _
      exact measurable_fst.fst.prodMk (ih.comp (measurable_fst.snd.prodMk measurable_snd))

theorem measurable_batchParts :
    let : MeasurableSpace (Prefix d cut) := prefixSpace d cut
    let : ∀ i, MeasurableSpace (Tape d (children i)) := fun _ => tapeSpace d _
    let : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d _
    Measurable (batchParts (d := d) cut) := by
  induction cut with
  | here => exact measurable_const.prodMk measurable_fst
  | step o a q cut ih =>
      let : MeasurableSpace (a.Tape d) := instrSpace d a
      let : MeasurableSpace (Prefix d cut) := prefixSpace d cut
      let : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d _
      let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d _
      exact (measurable_fst.prodMk (ih.comp measurable_snd).fst).prodMk (ih.comp measurable_snd).snd
  | batch o cs q cut ih =>
      let : ∀ i, MeasurableSpace (Tape d (cs i)) := fun i => tapeSpace d _
      let : MeasurableSpace (Prefix d cut) := prefixSpace d cut
      let : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d _
      let : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d _
      exact (measurable_fst.prodMk (ih.comp measurable_snd).fst).prodMk (ih.comp measurable_snd).snd

end BatchCut

section Advance
variable {d c n : ℕ} {Γ Δ : Ctx} {τ σ : Ty} {p : Prog c Γ τ}
  {o : Origin} {children : Fin n → Prog c Δ .point}
  {next : Prog c (List.replicate n .point ++ Δ) σ}
  (L : PrimitiveLaws d) (cut : TailCut (.batch o children next) p)
  {A : Type*} [MeasurableSpace A]
local instance canonicalTapeSpace (p : Prog c Γ τ) : MeasurableSpace (Tape d p) := tapeSpace d p
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d _
local instance : ∀ i, MeasurableSpace (Tape d (children i)) := fun i => tapeSpace d (children i)
local instance : ∀ i, IsProbabilityMeasure (tapeLaw L (children i)) := fun _ => tapeLaw_probability L _
local instance : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L _

def advanceHistory (z : (A × Prefix d cut) × (∀ i, Tape d (children i))) :
    A × Prefix d (afterBatch cut) := (z.1.1,appendBatch cut z.1.2 z.2)

theorem measurable_advanceHistory : Measurable (advanceHistory (d := d) (A := A) cut) :=
  measurable_fst.fst.prodMk
    ((measurable_appendBatch cut).comp (measurable_fst.snd.prodMk measurable_snd))

/-- The next consumed-history law is obtained from the actual child tapes,
not by sampling another standalone source or replacing earlier coordinates. -/
def advancedLaw (μ : Measure (A × Prefix d cut)) : Measure (A × Prefix d (afterBatch cut)) :=
  (μ.prod (Measure.pi fun i => tapeLaw L (children i))).map (advanceHistory cut)

instance advancedLaw_sFinite (μ : Measure (A × Prefix d cut)) [SFinite μ] :
    SFinite (advancedLaw L cut μ) := by
  unfold advancedLaw
  infer_instance

theorem historyLaw_advance (μ : Measure (A × Prefix d cut)) [SFinite μ] :
    CausalTailHistory.historyLaw L cut μ =
      CausalTailHistory.historyLaw L (afterBatch cut) (advancedLaw L cut μ) := by
  let batchLaw := Measure.pi fun i => tapeLaw L (children i)
  have hm := measurable_advanceHistory (d := d) (A := A) cut
  have hp : (advancedLaw L cut μ).prod (tapeLaw L next) =
      ((μ.prod batchLaw).prod (tapeLaw L next)).map (Prod.map (advanceHistory cut) id) := by
    simpa only [advancedLaw,Measure.map_id] using
      Measure.map_prod_map (μ.prod batchLaw) (tapeLaw L next) hm measurable_id
  rw [CausalTailHistory.historyLaw,CausalTailHistory.historyLaw,hp,
    Measure.map_map (CausalTailHistory.measurable_pack (afterBatch cut)) (hm.prodMap measurable_id)]
  change (μ.prod (batchLaw.prod (tapeLaw L next))).map (CausalTailHistory.pack cut) = _
  rw [← Measure.prodAssoc_prod,
    Measure.map_map (CausalTailHistory.measurable_pack cut) MeasurableEquiv.prodAssoc.measurable]
  congr 1
  funext z
  exact Prod.ext rfl (join_afterBatch cut z.1.1.2 z.1.2 z.2).symm

/-- Advancing through the actual current batch proves the next whole-tail
factorization even for arbitrary correlated augmented history/prefix laws. -/
theorem advanced_split (μ : Measure (A × Prefix d cut)) [SFinite μ] :
    (CausalTailHistory.historyLaw L cut μ).map
      (CausalTailHistory.unpack (afterBatch cut)) =
      (advancedLaw L cut μ).prod (tapeLaw L next) := by
  rw [historyLaw_advance L cut μ,CausalTailHistory.historyLaw_split]

theorem advanced_split_of_split (oldLaw : Measure (A × Tape d p))
    (μ : Measure (A × Prefix d cut)) [SFinite μ]
    (hsplit : oldLaw.map (CausalTailHistory.unpack cut) =
      μ.prod (tapeLaw L (.batch o children next))) :
    oldLaw.map (CausalTailHistory.unpack (afterBatch cut)) =
      (advancedLaw L cut μ).prod (tapeLaw L next) := by
  rw [CausalTailHistory.eq_historyLaw_of_split L cut oldLaw μ hsplit]
  exact advanced_split L cut μ

end Advance

section Private
open Numerics Numerics.AffineGraph SourceExecutableTables PrivateSamplingProgram
open TapeLowering NoisyLayer GeneralMainFocus
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N k : ℕ) (hk : k<N)
  (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)

/-- The batch record is constructed from the actual public private-block
configuration. Its covariance domain follows from the source radius floor. -/
def privateData : FreshChildBatchCoupling.Data n (samplingSize main final) ((PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk)).ctx where
  child := main
  slot i := ((samplingConfig main final N)).mainSlots ∘ childSlot (fun i => (main i).size) (fun i => (main i).program) i
  old := ((PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk)).old
  designated := ((samplingConfig main final N)).mainDesignated ((PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk)).remainingAfter
  auxiliary := ((samplingConfig main final N)).mainAuxiliary ((PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk)).remainingAfter
  rho _ := samplingNoise S r Ds
  radius i := S.radius r (e i)
  Ds := Ds
  rho_nonneg _ := (RecursiveExecutableDomain.sampling_noise_pos S r Ds hr hDs).le
  radius_pos i := S.radius_pos r hr (e i)
  Ds_pos := hDs
  shift_budget := hmass
  small i := RecursiveExecutableDomain.sampling_noise_separation S r Ds hr hDs (e i)

local instance privateTapeSpace {c : ℕ} {Γ : Ctx} {τ : Ty} (q : Prog c Γ τ) :
    MeasurableSpace (Tape d q) := tapeSpace d q
local instance : MeasurableSpace (Prefix d (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk)) := prefixSpace d (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk)
local instance : MeasurableSpace (Prefix d (afterBatch (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk))) := prefixSpace d _

theorem privateData_program (i : Fin n) :
    FreshChildBatchCoupling.program (privateData S e r Ds main final N k hk hr hDs hmass) i = PrivateGeneralOccurrence.child S e r Ds main final N k hk i := rfl

variable {A H : Type*} [MeasurableSpace A] [MeasurableSpace H]
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  (J : FreshChildBatchCoupling.Lower L (privateData S e r Ds main final N k hk hr hDs hmass))
  (coarse : A × Prefix d (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk) → H) (hcoarse : Measurable coarse)
  (center : Fin n → H → Point d) (hcenter : ∀ i, Measurable (center i))
  (comparison : Fin n → A × Prefix d (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk) → Point d)
  (hcomparison : ∀ i, Measurable (comparison i))

/-- Only the old prefix, augmented past, and the just-consumed literal batch
are observed. Comparison noise is read from that past; it is not redrawn. -/
def layerObservation (z : A × Prefix d (afterBatch (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk))) : H × (∀ i, FreshChildBatchCoupling.Raw d (privateData S e r Ds main final N k hk hr hDs hmass) i) :=
  let parts := batchParts (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk) z.2
  let old := (z.1,parts.1)
  (coarse old,fun i => (comparison i old,parts.2 i))

include hcoarse hcomparison in
theorem layerObservation_measurable :
    Measurable (layerObservation S e r Ds main final N k hk hr hDs hmass coarse comparison) := by
  have hp : Measurable (fun z : A × Prefix d
      (afterBatch (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk)) =>
        batchParts (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk) z.2) :=
    (measurable_batchParts (d := d) (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk)).comp measurable_snd
  have hold := measurable_fst.prodMk hp.fst
  exact (hcoarse.comp hold).prodMk (Measurable.of_eval fun i =>
    ((hcomparison i).comp hold).prodMk ((measurable_pi_apply i).comp hp.snd))

/-- Literal lower-child completed-seed disintegrations, evaluated on the same
current batch tapes. This is a constructed conditional, not an arbitrary law. -/
def referenceConditional : Kernel (A × Prefix d (afterBatch (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk))) (Fin n → Point d) :=
  (FreshChildBatchCoupling.referenceBatch L hL (privateData S e r Ds main final N k hk hr hDs hmass) J center hcenter).comap
    (layerObservation S e r Ds main final N k hk hr hDs hmass coarse comparison)
    (layerObservation_measurable S e r Ds main final N k hk hr hDs hmass
      coarse hcoarse comparison hcomparison)

instance referenceConditional_markov : IsMarkovKernel
    (referenceConditional S e r Ds main final N k hk hr hDs hmass
      L hL J coarse hcoarse center hcenter comparison hcomparison) := by
  unfold referenceConditional
  infer_instance

/-- The actual supplied full source tape and augmented past are copied. -/
def layerKernel : Kernel (A × Tape d (ExecutableData.program (SamplingExecutable.build S e r Ds main final N))) ((A × Tape d (ExecutableData.program (SamplingExecutable.build S e r Ds main final N))) × (Fin n → Point d)) :=
  CausalTailHistory.onTape L (afterBatch (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk))
    (referenceConditional S e r Ds main final N k hk hr hDs hmass
      L hL J coarse hcoarse center hcenter comparison hcomparison)

instance layerKernel_markov : IsMarkovKernel
    (layerKernel S e r Ds main final N k hk hr hDs hmass
      L hL J coarse hcoarse center hcenter comparison hcomparison) := by
  unfold layerKernel
  infer_instance

theorem layerKernel_original :
    (layerKernel S e r Ds main final N k hk hr hDs hmass
      L hL J coarse hcoarse center hcenter comparison hcomparison).fst = Kernel.id :=
  CausalTailHistory.onTape_original L (afterBatch (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk)) _

/-- Actual input realization reads each original current child tape exactly;
every later residual, row, layer and finish coordinate is absent from it. -/
theorem layerKernel_reference_apply (a : A) (ω : Tape d (ExecutableData.program (SamplingExecutable.build S e r Ds main final N))) :
    (layerKernel S e r Ds main final N k hk hr hDs hmass
      L hL J coarse hcoarse center hcenter comparison hcomparison).snd (a,ω) =
      FreshChildBatchCoupling.referenceBatch L hL (privateData S e r Ds main final N k hk hr hDs hmass) J center hcenter
        (coarse (a,(split (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk) ω).1),fun i =>
          (comparison i (a,(split (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk) ω).1),(split (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk) ω).2.1 i)) := by
  simp only [layerKernel,CausalTailHistory.onTape,Kernel.snd_prod,Kernel.comap_apply,
    referenceConditional,CausalTailHistory.unpack,layerObservation,split_afterBatch,batchParts_append]

/-- The actual current residual batch and the entire later program remain
one fresh factor after adjoining all lower-child references. The sole source
premise is the chronological whole-tail invariant before this actual batch. -/
theorem layerKernel_whole_suffix
    (oldLaw : Measure (A × Tape d (ExecutableData.program (SamplingExecutable.build S e r Ds main final N))))
    (μ : Measure (A × Prefix d (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk))) [SFinite μ]
    (hsplit : oldLaw.map (CausalTailHistory.unpack (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk)) =
      μ.prod (tapeLaw L (.batch (((samplingConfig main final N)).layerOrigin ((PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk)).remainingAfter)
        (PrivateGeneralOccurrence.child S e r Ds main final N k hk)
        (PrivateGeneralOccurrence.next S e r Ds main final N k hk)))) :
    (layerKernel S e r Ds main final N k hk hr hDs hmass
      L hL J coarse hcoarse center hcenter comparison hcomparison ∘ₘ oldLaw).map
        (CausalTailHistory.unpackExtended (afterBatch (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk))) =
      ((advancedLaw L (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk) μ) ⊗ₘ
        referenceConditional S e r Ds main final N k hk hr hDs hmass
          L hL J coarse hcoarse center hcenter comparison hcomparison).prod
            (tapeLaw L (PrivateGeneralOccurrence.next S e r Ds main final N k hk)) := by
  exact CausalTailHistory.whole_suffix_fresh_of_split L (afterBatch (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk)) oldLaw
    (advancedLaw L (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk) μ) (advanced_split_of_split L (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk) oldLaw μ hsplit) _

theorem layerKernel_preserves_old_joint (oldLaw : Measure (A × Tape d (ExecutableData.program (SamplingExecutable.build S e r Ds main final N)))) [SFinite oldLaw] :
    (layerKernel S e r Ds main final N k hk hr hDs hmass
      L hL J coarse hcoarse center hcenter comparison hcomparison ∘ₘ oldLaw).map Prod.fst = oldLaw :=
  CausalTailHistory.onTape_preserves_original L (afterBatch (PrivateGeneralOccurrence.batchCut S e r Ds main final N k hk)) oldLaw _

end Private
end AcceleratedLogConcave.Oracle.PrivateCausalLayer
