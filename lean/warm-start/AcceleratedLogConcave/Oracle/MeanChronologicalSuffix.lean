import AcceleratedLogConcave.Oracle.MeanChronologicalCoupling

/-! Exact complete unread-suffix laws for the constructed finite mean loop. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanChronologicalSuffix
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
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

def updateHistory (k : Fin N)
    (z : (History (d := d) M nodes anchors seeds main final sampling N A × (Fin n → Point d)) × (Fin n → Point d)) : History (d := d) M nodes anchors seeds main final sampling N A :=
  (z.1.1.1,(Function.update z.1.1.2.1 k z.1.2,comparisonUpdate M nodes r Ds σ δ t w (z.1.2,z.2)))

theorem updateHistory_measurable (k : Fin N) :
    Measurable (updateHistory (d := d) (A := A) M nodes anchors seeds main final sampling N r Ds σ δ t w k) := by
  have hv : Measurable (fun z : (History (d := d) M nodes anchors seeds main final sampling N A × (Fin n → Point d)) × (Fin n → Point d) =>
      z.1.1.2.1) := measurable_fst.fst.snd.fst
  have hg : Measurable (fun z : (History (d := d) M nodes anchors seeds main final sampling N A × (Fin n → Point d)) × (Fin n → Point d) =>
      z.1.2) := measurable_fst.snd
  have hu := (measurable_update' (X := fun _ : Fin N => Fin n → Point d) (a := k)).comp (hv.prodMk hg)
  have hn := (comparisonUpdate_measurable (d := d) M nodes r Ds σ δ t w).comp (hg.prodMk measurable_snd)
  exact measurable_fst.fst.fst.prodMk (hu.prodMk hn)

variable (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
def layerCut := afterBatch (afterBatch (afterBatch
  (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))

local instance : MeasurableSpace
    (Prefix d (layerCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))) := prefixSpace d _

def residualPrefix (h : Prefix d (layerCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    Fin n → Point d :=
  let rows := batchParts (afterBatch (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))) h
  let noise := batchParts (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) rows.1
  fun i => (noise.2 i).1

theorem residualPrefix_measurable :
    Measurable (residualPrefix (d := d) M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) := by
  have hrows := measurable_batchParts (d := d)
    (afterBatch (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
  have hn := (measurable_batchParts (d := d)
    (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))).comp hrows.fst
  exact Measurable.of_eval fun i => ((measurable_pi_apply i).comp hn.snd).fst

def recordPast (k : Fin N)
    (z : (History (d := d) M nodes anchors seeds main final sampling N A × (Fin n → Point d)) ×
      Prefix d (layerCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) : History (d := d) M nodes anchors seeds main final sampling N A :=
  updateHistory M nodes anchors seeds main final sampling N r Ds σ δ t w k
    (z.1,residualPrefix M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs z.2)

theorem recordPast_measurable (k : Fin N) :
    Measurable (recordPast (d := d) (A := A) M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs k) := by
  exact (updateHistory_measurable M nodes anchors seeds main final sampling N r Ds σ δ t w k).comp (measurable_fst.prodMk
    ((residualPrefix_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs).comp measurable_snd))

omit [MeasurableSpace A] in
theorem changeHistory_record (k : Fin N) :
    PrivateChronologicalCoupling.changeHistory (layerCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)
      (recordPast (d := d) (A := A) M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs k) ∘
        regroupOriginal = record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs k := by
  funext z
  simp only [Function.comp_def,PrivateChronologicalCoupling.changeHistory,recordPast,regroupOriginal,record,
    updateHistory,residualPrefix,layerCut,split_afterBatch,batchParts_append]

local instance : MeasurableSpace
    (Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) := prefixSpace d _

variable (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))

def returnedPrefixLaw
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))) :
    Measure ((History (d := d) M nodes anchors seeds main final sampling N A × (Fin n → Point d)) ×
      Prefix d (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))) :=
  (((advancedLaw L (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) μ) ⊗ₘ
    conditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J).map
      (regroupPrefix (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))))

instance returnedPrefixLaw_sFinite
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
    [SFinite μ] :
    SFinite (returnedPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ) := by
  unfold returnedPrefixLaw
  infer_instance

def nextPrefixLaw (k : Fin N)
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))) :
    Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (layerCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :=
  (advancedLaw L (afterBatch (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
    (advancedLaw L (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
      (returnedPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ))).map
            (PrivateChronologicalCoupling.changePrefix (layerCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)
              (recordPast M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs k))

instance nextPrefixLaw_sFinite (k : Fin N)
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
    [SFinite μ] :
    SFinite (nextPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs J k μ) := by
  have hret : SFinite (returnedPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ) :=
    returnedPrefixLaw_sFinite M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ
  have hres : SFinite (advancedLaw L (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
      (returnedPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ)) :=
    advancedLaw_sFinite L _ _
  have hrows : SFinite (advancedLaw L (afterBatch (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
      (advancedLaw L (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
        (returnedPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ))) :=
    advancedLaw_sFinite L _ _
  unfold nextPrefixLaw
  infer_instance

/-- A concrete executed step preserves the complete next unread suffix.
Only the entering actual cut factorization is assumed; old augmented history,
the consumed prefix, and the parent momentum may correlate arbitrarily. -/
theorem step_whole_suffix (k : Fin N)
    (ρ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
    [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) =
      μ.prod (tapeLaw L (.batch (layerOrigin (s.remaining-1))
        (FreshChildBatchCoupling.program (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
        (next M nodes anchors seeds main final sampling N s)))) :
    (MeanChronologicalCoupling.step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs k J ∘ₘ ρ).map
      (CausalTailHistory.unpack (layerCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) =
        (nextPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs J k μ).prod
          (tapeLaw L (Loop M nodes main final sampling (s.remaining-1) batchRef
            (fun j => preserveDirect (s.direct j)) (fun q => preserveDirect (s.saved q)))) := by
  have hc := CausalTailHistory.whole_suffix_fresh_of_split L
    (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) ρ
    (advancedLaw L (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) μ)
    (advanced_split_of_split L (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) ρ μ hsplit)
    (conditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J)
  have hg := regroup_cut_law L (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
    _ _ hc
  have hn := consume_two_batches L (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
    _ _ hg
  have hret : SFinite (returnedPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ) :=
    returnedPrefixLaw_sFinite M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ
  have hres : SFinite (advancedLaw L (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
      (returnedPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ)) :=
    advancedLaw_sFinite L _ _
  have hrows : SFinite (advancedLaw L (afterBatch (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
      (advancedLaw L (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
        (returnedPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ))) :=
    advancedLaw_sFinite L _ _
  have hh := PrivateChronologicalCoupling.changeHistory_split L (layerCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)
    (recordPast M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs k)
    (recordPast_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs k) _
      (advancedLaw L (afterBatch (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
        (advancedLaw L (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
          (returnedPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ))) hn
  rw [Measure.map_map
    (PrivateChronologicalCoupling.changeHistory_measurable L _ _ (recordPast_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs k))
      regroupOriginal_measurable,changeHistory_record] at hh
  rw [MeanChronologicalCoupling.step,← Measure.map_comp _ _ (record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t w s hs k)]
  exact hh

/-- The same advance stated at the actual entering and reached cursors.
Destructing the positive remaining count discharges the target transport;
no equality with a separately regenerated focus is assumed. -/
theorem step_cursor_whole_suffix (k : Fin N)
    (ρ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    let : MeasurableSpace (Prefix d (advance M nodes anchors seeds main final sampling N s hs).cut) := prefixSpace d _
    ∀ (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d s.cut)) [SFinite μ],
    ρ.map (CausalTailHistory.unpack s.cut) =
      μ.prod (tapeLaw L (Loop M nodes main final sampling s.remaining s.old s.direct s.saved)) →
    ∃ (ν : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (advance M nodes anchors seeds main final sampling N s hs).cut)),
      SFinite ν ∧
      (MeanChronologicalCoupling.step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs k J ∘ₘ ρ).map
        (CausalTailHistory.unpack (advance M nodes anchors seeds main final sampling N s hs).cut) =
          ν.prod (tapeLaw L (Loop M nodes main final sampling (s.remaining-1) batchRef
            (fun j => preserveDirect (s.direct j)) (fun q => preserveDirect (s.saved q)))) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      dsimp only
      intro μ _ hsplit
      let s : Cursor M nodes anchors seeds main final sampling N := ⟨remaining+1,ctx,old,direct,saved,cut⟩
      refine ⟨nextPrefixLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs J k μ,
        nextPrefixLaw_sFinite M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs J k μ,?_⟩
      exact step_whole_suffix M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs J k ρ μ hsplit



variable (Jall : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))

theorem initialPrefix_sFinite
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [SFinite μ] :
    SFinite (MeanInitialComparison.prefixLaw M nodes anchors seeds main final sampling N L μ) := by
  have h0 : SFinite (advancedLaw L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) μ) := advancedLaw_sFinite L _ _
  have h1 : SFinite (advancedLaw L (afterBatch (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))
    (advancedLaw L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) μ)) := advancedLaw_sFinite L _ _
  unfold MeanInitialComparison.prefixLaw
  infer_instance

/-- Every actually executed finite stage retains the complete unread suffix.
The only entering law is the literal original mean body-cut factorization. -/
theorem iteration_whole_suffix (k : ℕ) (hk : k≤N)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :
    let s := (stage M nodes anchors seeds main final sampling N k hk).1
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∃ (ν : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d s.cut)), SFinite ν ∧
      (iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall k hk ∘ₘ MeanInitialComparison.initialLaw M nodes anchors seeds main final sampling N ρ).map
        (CausalTailHistory.unpack s.cut)=ν.prod (tapeLaw L (Loop M nodes main final sampling s.remaining s.old s.direct s.saved)) := by
  induction k with
  | zero =>
    refine ⟨MeanInitialComparison.prefixLaw M nodes anchors seeds main final sampling N L μ,initialPrefix_sFinite M nodes anchors seeds main final sampling N L μ,?_⟩
    simpa only [iteration,stage,entry,Measure.id_comp] using
      MeanInitialComparison.initial_whole_suffix M nodes anchors seeds main final sampling N L ρ μ hsplit
  | succ k ih =>
    obtain ⟨ν,hν,hcut⟩ := ih (by omega)
    let s := (stage M nodes anchors seeds main final sampling N k (by omega)).1
    have hs : 0<s.remaining := stage_positive M nodes anchors seeds main final sampling N k (by omega)
    let _ : SFinite ν := hν
    obtain ⟨ξ,hξ,hξcut⟩ := step_cursor_whole_suffix M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs (Jall k (by omega)) ⟨k,by omega⟩
      (iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall k (by omega) ∘ₘ MeanInitialComparison.initialLaw M nodes anchors seeds main final sampling N ρ) ν hcut
    refine ⟨ξ,hξ,?_⟩
    simpa only [iteration,stage,s,advance,← Measure.comp_assoc] using hξcut

theorem kernel_whole_suffix
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :
    let s := terminalCursor M nodes anchors seeds main final sampling N
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∃ (ν : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d s.cut)), SFinite ν ∧
      (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ).map (CausalTailHistory.unpack s.cut)=
        ν.prod (tapeLaw L (Loop M nodes main final sampling s.remaining s.old s.direct s.saved)) := by
  simpa only [kernel,← Measure.comp_assoc,Measure.deterministic_comp_eq_map,
    MeanInitialComparison.initialLaw,terminalCursor] using
      iteration_whole_suffix M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall N le_rfl ρ μ hsplit

end AcceleratedLogConcave.Oracle.MeanChronologicalSuffix
