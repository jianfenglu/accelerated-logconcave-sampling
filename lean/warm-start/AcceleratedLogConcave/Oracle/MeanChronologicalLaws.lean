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
namespace AcceleratedLogConcave.Oracle.MeanChronologicalLaws
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling MeanChronologicalSuffix
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

def comparison (z : History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) :
    Coarse (d := d) M nodes anchors seeds main final sampling N A × (Fin n → Point d) := (z.1.1,z.1.2.2)

theorem comparison_measurable : Measurable (comparison (d := d) (A := A) M nodes anchors seeds main final sampling N) :=
  measurable_fst.fst.prodMk measurable_fst.snd.snd

variable (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
local instance : MeasurableSpace (Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) := prefixSpace d _
local instance : MeasurableSpace (Prefix d (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))) := prefixSpace d _

theorem observation_law
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
    [IsProbabilityMeasure μ] (ν : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure ν]
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2)) =
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :
    (advancedLaw L (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) μ).map
      (observation M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) =
        ν.prod (Measure.pi (FreshChildBatchCoupling.rawLaw L
          (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))) := by
  let bd := data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs
  let _ : ∀ i, IsProbabilityMeasure (tapeLaw L (FreshChildBatchCoupling.program bd i)) :=
    fun i => tapeLaw_probability L _
  have hp : MeasurePreserving (fun z : History (d := d) M nodes anchors seeds main final sampling N A ×
      Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) => (z.1.1,z.1.2.2)) μ
      (ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :=
    ⟨measurable_fst.fst.prodMk measurable_fst.snd.snd,hcomparison⟩
  have h := ((MeasurePreserving.id ν).prod (FreshChildBatchCoupling.rawSplit_preserving L bd).symm).comp
    ((measurePreserving_prodAssoc ν (Measure.pi fun _ : Fin n => stdGaussian (Point d))
      (Measure.pi fun i => tapeLaw L (FreshChildBatchCoupling.program bd i))).comp
        (hp.prod (MeasurePreserving.id (Measure.pi fun i => tapeLaw L (FreshChildBatchCoupling.program bd i)))))
  rw [advancedLaw,Measure.map_map
    (observation_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)
    (measurable_advanceHistory _)]
  simpa [Function.comp_def,observation,advanceHistory,batchParts_append,
    FreshChildBatchCoupling.rawSplit,MeasurableEquiv.prodAssoc,Equiv.prodAssoc,Prod.map,bd] using h.map_eq


variable (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))

theorem returned_reference_law
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
    [IsProbabilityMeasure μ] (ν : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure ν]
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2))=
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :
    ((advancedLaw L (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) μ) ⊗ₘ conditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J).map
      (fun z => (z.1.1.1,z.2))=ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  unfold conditional
  exact FreshChildBatchCoupling.projected_coarse_reference_law L hL
    (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) J
    (MeanChronologicalHost.center M nodes anchors seeds main final sampling N x P referencePosition hF hell hlo hup r σ hr hσ hsmall)
    (MeanChronologicalHost.center_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference
      hF hell hlo hup r σ hr hσ hsmall)
    (advancedLaw L (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) μ) ν
    (observation M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) (observation_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)
    (observation_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L s hs μ ν hcomparison)

/-- The exact matrix row bound is a deterministic geometry obligation;
no Gaussian law or conditional-reference certificate is assumed. -/
theorem step_comparison_law
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (k : Fin N)
    (ρ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
    [IsProbabilityMeasure μ] (ν : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure ν]
    (hsplit : ρ.map (CausalTailHistory.unpack (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))=
      μ.prod (tapeLaw L (.batch (layerOrigin (s.remaining-1))
        (FreshChildBatchCoupling.program (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) (next M nodes anchors seeds main final sampling N s))))
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2))=
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :
    (MeanChronologicalCoupling.step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs k J ∘ₘ ρ).map (comparison M nodes anchors seeds main final sampling N)=
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  have hcut := CausalTailHistory.whole_suffix_fresh_of_split L
    (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) ρ
    (advancedLaw L (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) μ)
    (advanced_split_of_split L (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) ρ μ hsplit)
    (conditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J)
  have href := returned_reference_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J μ ν hcomparison
  have hnext := actual_recombine_law (residualOrigin (s.remaining-1)) _
    (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) L hL
    (adjoin M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J ∘ₘ ρ)
    ((advancedLaw L (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) μ) ⊗ₘ conditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J)
    ν (fun z => z.1.1) measurable_fst.fst hcut href
    (fun i j => M.matrix r σ (nodes i) (nodes j))
    (RecursiveExecutableDomain.center_noise_pos M r Ds hr hDs) ha hA
  rw [MeanChronologicalCoupling.step,← Measure.map_comp _ _
    (record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t w s hs k),
    Measure.map_map (comparison_measurable M nodes anchors seeds main final sampling N) (record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t w s hs k)]
  exact hnext



variable {Δ : Ctx} {τout : Ty} {q : Prog (SourceMeanExecutable.size (a := a) main final sampling) Δ τout}
  (cut : TailCut q (Host M nodes anchors seeds main final sampling N))
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d _
theorem prefixLaw_eq_of_split
    (ρ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw L q)) :
    ρ.map (fun z => (z.1,(split cut z.2).1)) = μ := by
  let _ : IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L _
  have h := congrArg (fun ν => ν.fst) hsplit
  rw [Measure.fst_prod,Measure.fst,Measure.map_map measurable_fst
    (CausalTailHistory.measurable_unpack L cut)] at h
  exact h

theorem prefix_probability_of_split
    (ρ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw L q)) :
    IsProbabilityMeasure μ := by
  rw [← prefixLaw_eq_of_split M nodes anchors seeds main final sampling N L cut ρ μ hsplit]
  infer_instance

theorem prefix_comparison_of_split
    (ρ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw L q)) :
    μ.map (fun z => (z.1.1,z.1.2.2)) = ρ.map (comparison M nodes anchors seeds main final sampling N) := by
  have hp : Measurable (fun z : History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N) =>
      (z.1,(split cut z.2).1)) := (CausalTailHistory.measurable_unpack L cut).fst
  rw [← prefixLaw_eq_of_split M nodes anchors seeds main final sampling N L cut ρ μ hsplit,
    Measure.map_map (measurable_fst.fst.prodMk measurable_fst.snd.snd) hp]
  rfl

theorem step_cursor_comparison_law
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (k : Fin N)
    (ρ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (ν : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure ν] :
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∀ (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d s.cut)) [SFinite μ],
    ρ.map (CausalTailHistory.unpack s.cut)=μ.prod (tapeLaw L (Loop M nodes main final sampling s.remaining s.old s.direct s.saved)) →
    ρ.map (comparison M nodes anchors seeds main final sampling N)=ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) →
    (MeanChronologicalCoupling.step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs k J ∘ₘ ρ).map (comparison M nodes anchors seeds main final sampling N)=
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      dsimp only
      intro μ _ hsplit hcomparison
      let s : Cursor M nodes anchors seeds main final sampling N := ⟨remaining+1,ctx,old,direct,saved,cut⟩
      let _ : IsProbabilityMeasure μ := prefix_probability_of_split M nodes anchors seeds main final sampling N L s.cut ρ μ hsplit
      have hμ := (prefix_comparison_of_split M nodes anchors seeds main final sampling N L s.cut ρ μ hsplit).trans hcomparison
      exact step_comparison_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs J ha hA k ρ μ ν hsplit hμ

variable (Jall : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))

theorem iteration_comparison_law
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (k : ℕ) (hk : k≤N)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :
    (iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall k hk ∘ₘ MeanInitialComparison.initialLaw M nodes anchors seeds main final sampling N ρ).map (comparison M nodes anchors seeds main final sampling N)=
      μ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  have hinitial : IsProbabilityMeasure (MeanInitialComparison.initialLaw M nodes anchors seeds main final sampling N ρ) := by
    unfold MeanInitialComparison.initialLaw
    infer_instance
  induction k with
  | zero =>
    rw [iteration,Measure.id_comp]
    change (MeanInitialComparison.initialLaw M nodes anchors seeds main final sampling N ρ).map
      (fun z => (z.1.1,z.1.2.2)) = _
    exact MeanInitialComparison.initial_comparison_law M nodes anchors seeds main final sampling N L hL ρ μ hsplit
  | succ k ih =>
    obtain ⟨ν,hν,hcut⟩ := iteration_whole_suffix M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall k (by omega) ρ μ hsplit
    let s := (stage M nodes anchors seeds main final sampling N k (by omega)).1
    have hs : 0<s.remaining := stage_positive M nodes anchors seeds main final sampling N k (by omega)
    let _ : SFinite ν := hν
    have hstep := step_cursor_comparison_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs (Jall k (by omega)) ha hA ⟨k,by omega⟩
      (iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall k (by omega) ∘ₘ MeanInitialComparison.initialLaw M nodes anchors seeds main final sampling N ρ) μ ν hcut (ih (by omega))
    simpa only [iteration,s,← Measure.comp_assoc] using hstep

theorem kernel_comparison_law
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :
    (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ).map (comparison M nodes anchors seeds main final sampling N)=
      μ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  simpa only [kernel,← Measure.comp_assoc,Measure.deterministic_comp_eq_map,MeanInitialComparison.initialLaw] using
    iteration_comparison_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ha hA N le_rfl ρ μ hsplit

theorem kernel_terminal_laws
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :
    let s := terminalCursor M nodes anchors seeds main final sampling N
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∃ (ν : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d s.cut)), IsProbabilityMeasure ν ∧
      (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ).map (CausalTailHistory.unpack s.cut)=
        ν.prod (tapeLaw L (Loop M nodes main final sampling s.remaining s.old s.direct s.saved)) ∧
      ν.map (fun z => (z.1.1,z.1.2.2))=μ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  obtain ⟨ν,hν,hcut⟩ := kernel_whole_suffix M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ρ μ hsplit
  let _ : SFinite ν := hν
  refine ⟨ν,?_,hcut,?_⟩
  · exact prefix_probability_of_split M nodes anchors seeds main final sampling N L (terminalCursor M nodes anchors seeds main final sampling N).cut _ ν hcut
  · exact (prefix_comparison_of_split M nodes anchors seeds main final sampling N L (terminalCursor M nodes anchors seeds main final sampling N).cut _ ν hcut).trans
      (kernel_comparison_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ha hA ρ μ hsplit)

end AcceleratedLogConcave.Oracle.MeanChronologicalLaws
