import AcceleratedLogConcave.Oracle.FreshChildBatchErrorTransfer
import AcceleratedLogConcave.Oracle.MeanChronologicalLaws
import AcceleratedLogConcave.Oracle.MeanChronologicalSuffix
import AcceleratedLogConcave.Oracle.PrivateChronologicalLaws

/-! Joint Gaussian comparison laws of the actual finite mean-main coupling.
The static coarse host retains incoming correlations and the original parent.
Only the complete unread tape is a fresh product factor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanChronologicalLowerProjection
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling MeanChronologicalSuffix
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)
  (r Ds : ℝ) (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  {A : Type*} [MeasurableSpace A]
  (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
  (x P referencePosition : A → Point d) (hx : Measurable x) (hP : Measurable P)
  (hreference : Measurable referencePosition)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (σ : ℝ) (hσ : 0<σ) (hsmall : r^2*ell≤1/2) (δ t w : ℝ)
local instance : MeasurableSpace
    (Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) := prefixSpace d _

local notation "Xmain" => History (d := d) M nodes anchors seeds main final sampling N A ×
  Tape d (Host M nodes anchors seeds main final sampling N)
local notation "centersM" => MeanChronologicalHost.center M nodes anchors seeds main final sampling N x P referencePosition hF hell hlo hup r σ hr hσ hsmall
local notation "hcentersM" => MeanChronologicalHost.center_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference hF hell hlo hup r σ hr hσ hsmall
variable (J : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))
def stageLaw (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (k : ℕ) (hk : k≤N) : Measure Xmain :=
  iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J k hk ∘ₘ
    MeanInitialComparison.initialLaw M nodes anchors seeds main final sampling N ρ
instance stageLaw_probability (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N)))
    [IsProbabilityMeasure ρ] (k : ℕ) (hk : k≤N) : IsProbabilityMeasure
    (stageLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ρ k hk) := by
  unfold stageLaw MeanInitialComparison.initialLaw
  infer_instance
/-- Reaching a positive cursor exposes exactly its current child-batch cut.
This changes only the dependent presentation of the reached source syntax. -/
theorem cursor_batch_split (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (ρ : Measure Xmain) [IsProbabilityMeasure ρ]
    (hw : let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
      ∃ μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d s.cut), SFinite μ ∧
        ρ.map (CausalTailHistory.unpack s.cut) =
          μ.prod (tapeLaw L (Loop M nodes main final sampling s.remaining s.old s.direct s.saved))) :
    let cut := batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs
    ∃ μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d cut), IsProbabilityMeasure μ ∧
      ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw L _) ∧
      μ.map (fun z => (z.1.1,z.1.2.2)) =
        ρ.map (MeanChronologicalLaws.comparison M nodes anchors seeds main final sampling N) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => exact False.elim (Nat.not_lt_zero _ hs)
    | succ remaining =>
      obtain ⟨μ,hμ,he⟩ := hw
      let _ := hμ
      let s : Cursor M nodes anchors seeds main final sampling N := ⟨remaining+1,ctx,old,direct,saved,cut⟩
      have hp := MeanChronologicalLaws.prefix_probability_of_split M nodes anchors seeds main final sampling N L s.cut ρ μ he
      exact ⟨μ,hp,he,
        MeanChronologicalLaws.prefix_comparison_of_split M nodes anchors seeds main final sampling N L s.cut ρ μ he⟩

/-- Actual main occurrence lower projection, before the chronological record
update. It retains the complete current lower seed and its returned reference. -/
def mainLowerProjection (k : ℕ) (hk : k<N) (i : Fin n) (z : Xmain × (Fin n → Point d)) :
    Coarse (d := d) M nodes anchors seeds main final sampling N A × ((Point d × Tape d (main i).program) × Point d) :=
  let s := (stage M nodes anchors seeds main final sampling N k hk.le).1
  let hs := stage_positive M nodes anchors seeds main final sampling N k hk
  let B := data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs
  (z.1.1.1,FreshChildBatchErrorTransfer.completedMap B i
    ((z.1.1.2.2 i,(split (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) z.1.2).2.1 i),z.2 i))

variable (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))

include ha hA hsplit in
/-- The constructed main conditional supplies its exact standalone LOWER
joint law on the actual pre-record sample, with the original P retained. -/
theorem mainLowerProjection_preserving (k : ℕ) (hk : k<N) (i : Fin n) :
    MeasurePreserving (mainLowerProjection M nodes anchors seeds main final sampling N r Ds hr hDs hmass k hk i)
      (adjoin M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall
        (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk) (J k hk) ∘ₘ
          stageLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ρ k hk.le)
      (μ ⊗ₘ ((J k hk).joint i).comap (centersM i) (hcentersM i)) := by
  let s := (stage M nodes anchors seeds main final sampling N k hk.le).1
  let hs := stage_positive M nodes anchors seeds main final sampling N k hk
  let cut := batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs
  let B := data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs
  let oldLaw := stageLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ρ k hk.le
  obtain ⟨ν,hν,hcursorSplit,hcmp⟩ := cursor_batch_split M nodes anchors seeds main final sampling N r Ds hr hDs hmass L s hs oldLaw
    (iteration_whole_suffix M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J k hk.le ρ μ hsplit)
  let _ := hν
  have hcomparison := hcmp.trans (MeanChronologicalLaws.iteration_comparison_law
    M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ha hA k hk.le ρ μ hsplit)
  let W := History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (PrivateCausalLayer.afterBatch cut)
  let obs : W → Coarse (d := d) M nodes anchors seeds main final sampling N A × (∀ i, FreshChildBatchCoupling.Raw d B i) :=
    observation M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs
  have hobs : Measurable obs := observation_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs
  let κ := FreshChildBatchCoupling.referenceBatch L hL B (J k hk) centersM hcentersM
  have he : conditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs (J k hk) = κ.comap obs hobs := rfl
  let ρ := PrivateCausalLayer.advancedLaw L cut ν
  let _ : IsProbabilityMeasure ρ := PrivateChronologicalLaws.advanced_probability L cut ν
  let η := FreshChildBatchErrorTransfer.observedLaw L hL B (J k hk) centersM hcentersM ρ obs hobs
  let _ : IsProbabilityMeasure η := inferInstance
  have hproject : ρ.map obs = μ.prod
      (Measure.pi (FreshChildBatchCoupling.rawLaw L B)) :=
    MeanChronologicalLaws.observation_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L s hs ν
      μ hcomparison
  have hfull : (adjoin M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs (J k hk) ∘ₘ oldLaw).map
      (CausalTailHistory.unpackExtended (PrivateCausalLayer.afterBatch cut)) = η.prod (tapeLaw L _) := by
    have h := CausalTailHistory.whole_suffix_fresh_of_split L (PrivateCausalLayer.afterBatch cut)
      oldLaw ρ (PrivateCausalLayer.advanced_split_of_split L cut oldLaw ν hcursorSplit) (κ.comap obs hobs)
    change _ = (ρ ⊗ₘ κ.comap obs hobs).prod _
    rw [← he] at h ⊢
    exact h
  have hp := FreshChildBatchErrorTransfer.full_sample_projection_preserving L
    (PrivateCausalLayer.afterBatch cut) _ η hfull
  have hl := FreshChildBatchErrorTransfer.observed_completed_preserving L hL B (J k hk) centersM hcentersM
    ρ μ obs hobs hproject i
  convert hl.comp hp using 1
  funext z
  simp only [s,cut,B,mainLowerProjection,FreshChildBatchErrorTransfer.lowerProjection,obs,
    observation,Function.comp_def,PrivateCausalLayer.split_afterBatch,
    PrivateCausalLayer.batchParts_append]


end AcceleratedLogConcave.Oracle.MeanChronologicalLowerProjection
