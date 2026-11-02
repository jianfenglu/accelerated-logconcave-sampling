import AcceleratedLogConcave.Oracle.PrivateChronologicalCoupling

/-! Gaussian comparison laws for the constructed finite private coupling.
The comparison vector consists of returned lower references and actual residual
occurrences; it is never replaced by the original designated child draws. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateChronologicalLaws
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceExecutableTables
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance PrivateChronologicalCoupling

local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

section General
variable {d c n : ℕ} {Γ Δ : Ctx} {τ : Ty} {p : Prog c Γ τ}
  {o : Origin} {children : Fin n → Prog c Δ .point}
  {next : Prog c (replyCtx n Δ) τ} {A : Type*} [MeasurableSpace A]
  (L : PrimitiveLaws d) (cut : TailCut (.batch o children next) p)
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d _
local instance : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d _

instance advanced_probability (μ : Measure (A × Prefix d cut)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (advancedLaw L cut μ) := by
  let _ : ∀ i, IsProbabilityMeasure (tapeLaw L (children i)) := fun i => tapeLaw_probability L _
  unfold advancedLaw
  infer_instance
end General

section Projection
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)

def comparison (z : History d N n × Tape d (Host S e r Ds main final N)) :
    ((Point d × Point d) × Point d) × (Fin n → Point d) := (z.1.1,z.1.2.2)

theorem comparison_measurable : Measurable (comparison (d := d) S e r Ds main final N) :=
  measurable_fst.fst.prodMk measurable_fst.snd.snd
end Projection

section Observation
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
  (L : PrimitiveLaws d)
local instance : MeasurableSpace
    (Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs)) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))) := prefixSpace d _

def observed
    (z : History d N n × Prefix d (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs))) :
    ((Point d × Point d) × Point d) ×
      (∀ i, FreshChildBatchCoupling.Raw d (data S e r Ds main final N hr hDs hmass s hs) i) :=
  (z.1.1,(observation S e r Ds main final N hr hDs hmass s hs z).2)

theorem observed_measurable :
    Measurable (observed (d := d) S e r Ds main final N hr hDs hmass s hs) :=
  measurable_fst.fst.prodMk
    (observation_measurable S e r Ds main final N hr hDs hmass s hs).snd

/-- The full current raw batch law follows from the entering comparison law
and the actual fresh batch tapes. It is not a supplied projection certificate. -/
theorem observation_law
    (μ : Measure (History d N n × Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs)))
    [IsProbabilityMeasure μ] (ν : Measure ((Point d × Point d) × Point d)) [IsProbabilityMeasure ν]
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2)) =
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :
    (advancedLaw L (batchCut S e r Ds main final N hr hDs hmass s hs) μ).map
      (observed S e r Ds main final N hr hDs hmass s hs) =
        ν.prod (Measure.pi (FreshChildBatchCoupling.rawLaw L
          (data S e r Ds main final N hr hDs hmass s hs))) := by
  let B := data S e r Ds main final N hr hDs hmass s hs
  let _ : ∀ i, IsProbabilityMeasure (tapeLaw L (FreshChildBatchCoupling.program B i)) :=
    fun i => tapeLaw_probability L _
  have hp : MeasurePreserving (fun z : History d N n ×
      Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs) => (z.1.1,z.1.2.2)) μ
      (ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :=
    ⟨measurable_fst.fst.prodMk measurable_fst.snd.snd,hcomparison⟩
  have h := ((MeasurePreserving.id ν).prod (FreshChildBatchCoupling.rawSplit_preserving L B).symm).comp
    ((measurePreserving_prodAssoc ν (Measure.pi fun _ : Fin n => stdGaussian (Point d))
      (Measure.pi fun i => tapeLaw L (FreshChildBatchCoupling.program B i))).comp
        (hp.prod (MeasurePreserving.id (Measure.pi fun i => tapeLaw L (FreshChildBatchCoupling.program B i)))))
  rw [advancedLaw,Measure.map_map
    (observed_measurable S e r Ds main final N hr hDs hmass s hs)
    (measurable_advanceHistory _)]
  simpa [Function.comp_def,observed,observation,advanceHistory,batchParts_append,
    FreshChildBatchCoupling.rawSplit,MeasurableEquiv.prodAssoc,Equiv.prodAssoc,Prod.map,B] using h.map_eq

variable (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs))

theorem conditional_augmented_coarse :
    conditional S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J =
      (FreshChildBatchCoupling.referenceBatch L hL
        (data S e r Ds main final N hr hDs hmass s hs) J
        (fun i (c : (Point d × Point d) × Point d) => jointPhi S e hF hell hlo hup hr i c.1)
        (fun i => (jointPhi_continuous S e hF hell hlo hup hr i).measurable.comp measurable_fst)).comap
          (observed S e r Ds main final N hr hDs hmass s hs)
          (observed_measurable S e r Ds main final N hr hDs hmass s hs) := by
  ext z : 1
  simp only [conditional,Kernel.comap_apply,FreshChildBatchCoupling.referenceBatch,
    Conditional.MeanReferenceLayer.finiteProduct_apply n _ (fun _ => inferInstance),Kernel.comap_apply]
  rfl

theorem returned_reference_law
    (μ : Measure (History d N n × Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs)))
    [IsProbabilityMeasure μ] (ν : Measure ((Point d × Point d) × Point d)) [IsProbabilityMeasure ν]
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2)) =
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :
    ((advancedLaw L (batchCut S e r Ds main final N hr hDs hmass s hs) μ) ⊗ₘ
      conditional S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J).map
        (fun z => (z.1.1.1,z.2)) =
          ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  rw [conditional_augmented_coarse S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J]
  exact FreshChildBatchCoupling.projected_coarse_reference_law L hL
    (data S e r Ds main final N hr hDs hmass s hs) J
    (fun i (c : (Point d × Point d) × Point d) => jointPhi S e hF hell hlo hup hr i c.1)
    (fun i => ((jointPhi_continuous S e hF hell hlo hup hr i).measurable.comp measurable_fst))
    (advancedLaw L (batchCut S e r Ds main final N hr hDs hmass s hs) μ) ν
    (observed S e r Ds main final N hr hDs hmass s hs)
    (observed_measurable S e r Ds main final N hr hDs hmass s hs)
    (observation_law S e r Ds main final N hr hDs hmass s hs L μ ν hcomparison)

/-- The exact executed next comparison is Gaussian jointly with its correct
coarse datum. Only returned lower references enter recombination; the current
residual is the literal unread source occurrence. -/
theorem step_comparison_law (hm : 0<m) (k : Fin N)
    (ρ : Measure (History d N n × Tape d (Host S e r Ds main final N)))
    (μ : Measure (History d N n × Prefix d (batchCut S e r Ds main final N hr hDs hmass s hs)))
    [IsProbabilityMeasure μ] (ν : Measure ((Point d × Point d) × Point d)) [IsProbabilityMeasure ν]
    (hsplit : ρ.map (CausalTailHistory.unpack (batchCut S e r Ds main final N hr hDs hmass s hs)) =
      μ.prod (tapeLaw L (.batch ((samplingConfig main final N).layerOrigin (s.remaining-1))
        (FreshChildBatchCoupling.program (data S e r Ds main final N hr hDs hmass s hs))
        (next S e r Ds main final N s))))
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2)) =
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :
    (PrivateChronologicalCoupling.step S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs k J ∘ₘ ρ).map
      (comparison S e r Ds main final N) =
        ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  have hcut := CausalTailHistory.whole_suffix_fresh_of_split L
    (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)) ρ
    (advancedLaw L (batchCut S e r Ds main final N hr hDs hmass s hs) μ)
    (advanced_split_of_split L (batchCut S e r Ds main final N hr hDs hmass s hs) ρ μ hsplit)
    (conditional S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J)
  have href := returned_reference_law S e r Ds main final N hr hDs hmass s hs L hL
    hF hell hlo hup J μ ν hcomparison
  have hnext := actual_sampling_nextComparison_law S e r Ds
    ((samplingConfig main final N).mainResidual (s.remaining-1)) _
    (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)) L hL hm hr hDs
    (adjoin S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J ∘ₘ ρ)
    ((advancedLaw L (batchCut S e r Ds main final N hr hDs hmass s hs) μ) ⊗ₘ
      conditional S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs J) ν
    (fun z => z.1.1) measurable_fst.fst hcut href
  rw [PrivateChronologicalCoupling.step,← Measure.map_comp _ _ (record_measurable S e r Ds main final N hr hDs hmass L s hs k),
    Measure.map_map (comparison_measurable S e r Ds main final N)
      (record_measurable S e r Ds main final N hr hDs hmass L s hs k)]
  exact hnext
end Observation

section Initial
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))

def coarseLaw (x : Point d) : Measure ((Point d × Point d) × Point d) :=
  (((Measure.dirac x).prod (stdGaussian (Point d))).prod (stdGaussian (Point d)))

instance coarseLaw_probability (x : Point d) : IsProbabilityMeasure (coarseLaw x) := by
  unfold coarseLaw
  infer_instance

include hL

/-- Original parent P is retained in the coarse datum throughout chronology.
The initial product with the setup draw and comparison initializer is proved
from their actual distinct original source coordinates. -/
theorem initial_comparison_law (x : Point d) :
    (initial S e r Ds main final N L x).map (comparison S e r Ds main final N) =
      (coarseLaw x).prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  let γ := stdGaussian (Point d)
  let γn := Measure.pi fun _ : Fin n => stdGaussian (Point d)
  let _ : IsProbabilityMeasure γ := inferInstance
  let _ : IsProbabilityMeasure γn := inferInstance
  let _ : IsProbabilityMeasure (tapeLaw L (Host S e r Ds main final N)) := tapeLaw_probability L _
  let _ : IsProbabilityMeasure L.pointDraw := L.point_probability
  let _ : IsProbabilityMeasure (tapeLaw L (PrivateSamplingProgram.code (samplingConfig main final N))) :=
    tapeLaw_probability L _
  have ht := PrivateInitialComparison.joint_preserving (samplingConfig main final N) L hL
  have hs := (MeasurePreserving.id γ).prod ht
  have ha := (measurePreserving_prodAssoc γ γ γn).symm.comp hs
  have hb := ((Measure.measurePreserving_swap (μ := γ) (ν := γ)).prod (MeasurePreserving.id γn)).comp ha
  have hx := (MeasurePreserving.id (Measure.dirac x)).prod hb
  have hc := ((measurePreserving_prodAssoc (Measure.dirac x) γ γ).symm.prod
    (MeasurePreserving.id γn)).comp
      ((measurePreserving_prodAssoc (Measure.dirac x) (γ.prod γ) γn).symm.comp hx)
  rw [initial,Kernel.map_apply _ (initializeState_measurable S e r Ds main final N),
    Measure.map_map (comparison_measurable S e r Ds main final N)
      (initializeState_measurable S e r Ds main final N),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,FreshChildRetainedCoupling.sourceLaw,hL]
  simpa [Function.comp_def,comparison,initializeState,coarseLaw,γ,γn,
    MeasurableEquiv.prodAssoc,Equiv.prodAssoc,Prod.map,Host,SamplingExecutable.build] using hc.map_eq
end Initial

section CutComparison
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  {Δ : Ctx} {σ : Ty} {q : Prog (samplingSize main final) Δ σ}
  (L : PrimitiveLaws d) (cut : TailCut q (Host S e r Ds main final N))
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d _

theorem prefixLaw_eq_of_split
    (ρ : Measure (History d N n × Tape d (Host S e r Ds main final N)))
    (μ : Measure (History d N n × Prefix d cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw L q)) :
    ρ.map (fun z => (z.1,(split cut z.2).1)) = μ := by
  let _ : IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L _
  have h := congrArg (fun ν => ν.fst) hsplit
  rw [Measure.fst_prod,Measure.fst,Measure.map_map measurable_fst
    (CausalTailHistory.measurable_unpack L cut)] at h
  exact h

theorem prefix_probability_of_split
    (ρ : Measure (History d N n × Tape d (Host S e r Ds main final N))) [IsProbabilityMeasure ρ]
    (μ : Measure (History d N n × Prefix d cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw L q)) :
    IsProbabilityMeasure μ := by
  rw [← prefixLaw_eq_of_split S e r Ds main final N L cut ρ μ hsplit]
  infer_instance

theorem prefix_comparison_of_split
    (ρ : Measure (History d N n × Tape d (Host S e r Ds main final N)))
    (μ : Measure (History d N n × Prefix d cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw L q)) :
    μ.map (fun z => (z.1.1,z.1.2.2)) = ρ.map (comparison S e r Ds main final N) := by
  have hp : Measurable (fun z : History d N n × Tape d (Host S e r Ds main final N) =>
      (z.1,(split cut z.2).1)) := (CausalTailHistory.measurable_unpack L cut).fst
  rw [← prefixLaw_eq_of_split S e r Ds main final N L cut ρ μ hsplit,
    Measure.map_map (measurable_fst.fst.prodMk measurable_fst.snd.snd) hp]
  rfl
end CutComparison

section CursorStep
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs))

theorem step_cursor_comparison_law (hm : 0<m) (k : Fin N)
    (ρ : Measure (History d N n × Tape d (Host S e r Ds main final N))) [IsProbabilityMeasure ρ]
    (ν : Measure ((Point d × Point d) × Point d)) [IsProbabilityMeasure ν] :
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∀ (μ : Measure (History d N n × Prefix d s.cut)) [SFinite μ],
    ρ.map (CausalTailHistory.unpack s.cut) =
      μ.prod (tapeLaw L (Loop main final N s.remaining s.old s.direct s.saved)) →
    ρ.map (comparison S e r Ds main final N) =
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) →
    (PrivateChronologicalCoupling.step S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs k J ∘ₘ ρ).map
      (comparison S e r Ds main final N) =
        ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      dsimp only
      intro μ _ hsplit hcomparison
      let s : Cursor S e r Ds main final N := ⟨remaining+1,ctx,old,direct,saved,cut⟩
      let _ : IsProbabilityMeasure μ :=
        prefix_probability_of_split S e r Ds main final N L s.cut ρ μ hsplit
      have hμ := (prefix_comparison_of_split S e r Ds main final N L s.cut ρ μ hsplit).trans hcomparison
      exact step_comparison_law S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup J
        hm k ρ μ ν hsplit hμ
end CursorStep

section Finite
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (J : ∀ (k : ℕ) (hk : k<N), FreshChildBatchCoupling.Lower L
    (data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk)))

/-- Gaussian comparison invariance for each finite constructed stage, with
the original parent P included in the coarse law. No post-horizon lower child
coupling, current-call induction hypothesis, or parent error bound is used. -/
theorem iteration_comparison_law (hm : 0<m) (k : ℕ) (hk : k≤N) (x : Point d) :
    (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk ∘ₘ
      initial S e r Ds main final N L x).map (comparison S e r Ds main final N) =
        (coarseLaw x).prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  induction k with
  | zero => simpa only [iteration,Measure.id_comp] using initial_comparison_law S e r Ds main final N L hL x
  | succ k ih =>
      obtain ⟨μ,hμ,hcut⟩ := iteration_whole_suffix S e r Ds main final N hr hDs hmass
        L hL hF hell hlo hup J k (by omega) x
      let s := (stage S e r Ds main final N k (by omega)).1
      have hs : 0<s.remaining := stage_positive S e r Ds main final N k (by omega)
      let _ : SFinite μ := hμ
      have hstep := step_cursor_comparison_law S e r Ds main final N hr hDs hmass s hs
        L hL hF hell hlo hup (J k (by omega)) hm ⟨k,by omega⟩
        (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k (by omega) ∘ₘ
          initial S e r Ds main final N L x) (coarseLaw x) μ hcut (ih (by omega))
      simpa only [iteration,s,← Measure.comp_assoc] using hstep

theorem kernel_comparison_law (hm : 0<m) (x : Point d) :
    (kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x).map
      (comparison S e r Ds main final N) =
        (coarseLaw x).prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  simpa only [kernel,Kernel.comp_apply] using
    iteration_comparison_law S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J hm N le_rfl x

/-- The constructed terminal kernel supplies both invariants needed by the
actual paid final batch: arbitrary full correlated past versus one fresh
whole suffix, and the exact coarse/benchmark Gaussian joint law. -/
theorem kernel_terminal_laws (hm : 0<m) (x : Point d) :
    let s := terminalCursor S e r Ds main final N
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∃ (μ : Measure (History d N n × Prefix d s.cut)), IsProbabilityMeasure μ ∧
      (kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x).map
        (CausalTailHistory.unpack s.cut) =
          μ.prod (tapeLaw L (Loop main final N s.remaining s.old s.direct s.saved)) ∧
      μ.map (fun z => (z.1.1,z.1.2.2)) =
        (coarseLaw x).prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  obtain ⟨μ,hμ,hcut⟩ := kernel_whole_suffix S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x
  let _ : SFinite μ := hμ
  refine ⟨μ,?_,hcut,?_⟩
  · exact prefix_probability_of_split S e r Ds main final N L (terminalCursor S e r Ds main final N).cut
      _ μ hcut
  · exact (prefix_comparison_of_split S e r Ds main final N L (terminalCursor S e r Ds main final N).cut
      _ μ hcut).trans (kernel_comparison_law S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J hm x)
end Finite
end AcceleratedLogConcave.Oracle.PrivateChronologicalLaws
