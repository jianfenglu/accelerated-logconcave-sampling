import AcceleratedLogConcave.Oracle.CausalTailRealization

/-! Causal extension with arbitrary correlation between augmented history and
the consumed syntax prefix. Only the WHOLE unread tape is a product factor.
The conditional operates on the supplied original tape, retains its history,
and copies every original coordinate. No independence of the original parent
momentum, augmented past, or consumed prefix is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.CausalTailHistory
open CanonicalTapeMeasurability CanonicalTapeLaw TailOccurrenceCut TailCut

variable {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ}
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (L : PrimitiveLaws d) (cut : TailCut q p)
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance : MeasurableSpace (Tape d p) := tapeSpace d p
local instance : MeasurableSpace (Tape d q) := tapeSpace d q
local instance : IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L q

/-- Join exactly the old prefix and whole unread tape while retaining history. -/
def pack (z : (A × Prefix d cut) × Tape d q) : A × Tape d p :=
  (z.1.1,join cut (z.1.2,z.2))

/-- Split the supplied full original tape, retaining the same augmented history. -/
def unpack (z : A × Tape d p) : (A × Prefix d cut) × Tape d q :=
  ((z.1,(split cut z.2).1),(split cut z.2).2)

omit [MeasurableSpace A] in
theorem pack_unpack (z : A × Tape d p) : pack cut (unpack cut z) = z := by
  change (z.1,join cut (split cut z.2)) = z
  rw [join_split]

omit [MeasurableSpace A] in
theorem unpack_pack (z : (A × Prefix d cut) × Tape d q) : unpack cut (pack cut z) = z := by
  simp only [pack,unpack,split_join]

theorem measurable_pack : Measurable (pack (d := d) (A := A) cut) :=
  measurable_fst.fst.prodMk
    ((measurable_join cut).comp (measurable_fst.snd.prodMk measurable_snd))

include L in
theorem measurable_unpack : Measurable (unpack (d := d) (A := A) cut) := by
  have hs : Measurable (fun z : A × Tape d p => split cut z.2) :=
    (measurePreserving_split L cut).measurable.comp measurable_snd
  exact (measurable_fst.prodMk hs.fst).prodMk hs.snd

/-- Arbitrary joint law of augmented past and consumed prefix. The definition
assumes independence only of their joint pair from the complete unread suffix. -/
def historyLaw (μ : Measure (A × Prefix d cut)) : Measure (A × Tape d p) :=
  (μ.prod (tapeLaw L q)).map (pack cut)

instance historyLaw_sFinite (μ : Measure (A × Prefix d cut)) [SFinite μ] :
    SFinite (historyLaw L cut μ) := by
  unfold historyLaw
  infer_instance

/-- The original correlated history/prefix joint is recovered on splitting;
the unread suffix remains one whole fresh product factor. -/
theorem historyLaw_split (μ : Measure (A × Prefix d cut)) :
    (historyLaw L cut μ).map (unpack cut) = μ.prod (tapeLaw L q) := by
  rw [historyLaw,Measure.map_map (measurable_unpack L cut) (measurable_pack cut)]
  simp only [Function.comp_def,unpack_pack]
  exact Measure.map_id

/-- An actual old history/tape law with the proved cut factorization is the
joined law above. The consumed history/prefix joint need not factor further. -/
theorem eq_historyLaw_of_split (oldLaw : Measure (A × Tape d p))
    (μ : Measure (A × Prefix d cut))
    (hsplit : oldLaw.map (unpack cut) = μ.prod (tapeLaw L q)) :
    oldLaw = historyLaw L cut μ := by
  have h := congrArg (fun ν : Measure ((A × Prefix d cut) × Tape d q) =>
    ν.map (pack cut)) hsplit
  rw [Measure.map_map (measurable_pack cut) (measurable_unpack L cut)] at h
  simp only [Function.comp_def,pack_unpack] at h
  change oldLaw.map id = historyLaw L cut μ at h
  simpa only [Measure.map_id] using h

/-- Conditional augmentation on the original supplied history and tape. It
reads only the correlated history/consumed-prefix pair and retains both. -/
def onTape (κ : Kernel (A × Prefix d cut) B) :
    Kernel (A × Tape d p) ((A × Tape d p) × B) :=
  Kernel.id ×ₖ κ.comap (fun z => (unpack cut z).1) (measurable_unpack L cut).fst

instance onTape_markov (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    IsMarkovKernel (onTape L cut κ) := by
  unfold onTape
  infer_instance

/-- Retention is pointwise in the whole original history/tape input. -/
theorem onTape_original (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    (onTape L cut κ).fst = Kernel.id := by
  unfold onTape
  exact Kernel.fst_prod _ _

/-- Copying the original history and full tape is independent of any cut-law
assumption, and holds for an arbitrary supplied old joint measure. -/
theorem onTape_preserves_original (oldLaw : Measure (A × Tape d p)) [SFinite oldLaw]
    (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    (onTape L cut κ ∘ₘ oldLaw).map Prod.fst = oldLaw := by
  rw [Measure.map_comp _ _ measurable_fst,← Kernel.fst_eq,onTape_original,Measure.id_comp]

def packExtended (z : ((A × Prefix d cut) × B) × Tape d q) : (A × Tape d p) × B :=
  (pack cut (z.1.1,z.2),z.1.2)

def unpackExtended (z : (A × Tape d p) × B) : ((A × Prefix d cut) × B) × Tape d q :=
  (((unpack cut z.1).1,z.2),(unpack cut z.1).2)

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem unpackExtended_packExtended (z : ((A × Prefix d cut) × B) × Tape d q) :
    unpackExtended cut (packExtended cut z) = z := by
  simp only [packExtended,unpackExtended,unpack_pack]

theorem measurable_packExtended : Measurable (packExtended (d := d) (A := A) (B := B) cut) :=
  ((measurable_pack cut).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
    measurable_fst.snd

include L in
theorem measurable_unpackExtended : Measurable (unpackExtended (d := d) (A := A) (B := B) cut) := by
  have hs : Measurable (fun z : (A × Tape d p) × B => unpack cut z.1) :=
    (measurable_unpack L cut).comp measurable_fst
  exact (hs.fst.prodMk measurable_snd).prodMk hs.snd

/-- Distribution-level extension with an arbitrary old correlated history law. -/
def extension (μ : Measure (A × Prefix d cut)) (κ : Kernel (A × Prefix d cut) B) :
    Measure ((A × Tape d p) × B) :=
  ((μ ⊗ₘ κ).prod (tapeLaw L q)).map (packExtended cut)

/-- Actual-input realization, valid for ANY old joint μ. No product between
history A and consumed prefix is introduced or needed in this identity. -/
theorem onTape_realizes_extension (μ : Measure (A × Prefix d cut)) [SFinite μ]
    (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    onTape L cut κ ∘ₘ historyLaw L cut μ = extension L cut μ κ := by
  let R : Kernel (A × Prefix d cut) ((A × Prefix d cut) × B) := Kernel.id ×ₖ κ
  have hm := measurable_packExtended (d := d) (A := A) (B := B) cut
  have hkernel : (onTape L cut κ).comap (pack cut) (measurable_pack cut) =
      (R ∥ₖ Kernel.id).map (packExtended cut) := by
    ext z : 1
    rw [Kernel.comap_apply,Kernel.map_apply _ hm]
    simp only [onTape,Kernel.prod_apply,Kernel.id_apply,Kernel.comap_apply,
      unpack_pack,R,Kernel.parallelComp_apply]
    rw [Measure.dirac_prod,Measure.prod_dirac,Measure.dirac_prod,
      Measure.map_map hm measurable_prodMk_right,
      Measure.map_map (hm.comp measurable_prodMk_right) measurable_prodMk_left]
    rfl
  rw [historyLaw,← Measure.deterministic_comp_eq_map (measurable_pack cut),
    Measure.comp_assoc,Kernel.comp_deterministic_eq_comap,hkernel,
    ← Measure.map_comp _ _ hm,← Measure.prod_comp_left]
  dsimp only [R]
  rw [← Measure.compProd_eq_comp_prod]
  rfl

/-- The full previous joint law of augmented history and ORIGINAL tape is
unchanged after adjoining the new output. -/
theorem original_joint_preserved (μ : Measure (A × Prefix d cut)) [SFinite μ]
    (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    (onTape L cut κ ∘ₘ historyLaw L cut μ).map Prod.fst = historyLaw L cut μ := by
  rw [Measure.map_comp _ _ measurable_fst]
  rw [← Kernel.fst_eq]
  rw [onTape_original,Measure.id_comp]

/-- The augmented consumed past and the WHOLE original unread tape have
exactly this joint product law, even when the old past and prefix correlate. -/
theorem whole_suffix_fresh (μ : Measure (A × Prefix d cut)) [SFinite μ]
    (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    (onTape L cut κ ∘ₘ historyLaw L cut μ).map (unpackExtended cut) =
      (μ ⊗ₘ κ).prod (tapeLaw L q) := by
  rw [onTape_realizes_extension,extension,
    Measure.map_map (measurable_unpackExtended L cut) (measurable_packExtended cut)]
  simp only [Function.comp_def,unpackExtended_packExtended]
  exact Measure.map_id

/-- Concrete adapter for an already constructed chronological history law:
only its entire unread-tail factorization is used; A may correlate with prefix. -/
theorem whole_suffix_fresh_of_split (oldLaw : Measure (A × Tape d p))
    (μ : Measure (A × Prefix d cut)) [SFinite μ]
    (hsplit : oldLaw.map (unpack cut) = μ.prod (tapeLaw L q))
    (κ : Kernel (A × Prefix d cut) B) [IsMarkovKernel κ] :
    (onTape L cut κ ∘ₘ oldLaw).map (unpackExtended cut) =
      (μ ⊗ₘ κ).prod (tapeLaw L q) := by
  rw [eq_historyLaw_of_split L cut oldLaw μ hsplit]
  exact whole_suffix_fresh L cut μ κ

end AcceleratedLogConcave.Oracle.CausalTailHistory
