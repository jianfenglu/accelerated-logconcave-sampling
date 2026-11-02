import AcceleratedLogConcave.Root.ClockChronologicalSuffix
import AcceleratedLogConcave.Root.ClockInitialComparison
import AcceleratedLogConcave.Oracle.PrivateChronologicalLaws

/-! Full Gaussian comparison law of the actual finite retained Clock loop. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockChronologicalLaws
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open Oracle.TailOccurrenceCut Oracle.PrivateCausalLayer Oracle.PrivateCausalAdvance
open TailCut Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockChronologicalCoupling ClockChronologicalSuffix ClockNoisyLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)

def comparison (z : History P d × Tape d (Host P hR hc hsmall clock label)) :
    Base P d × (Index P → Point d) := (z.1.1,z.1.2.2)

theorem comparison_measurable : Measurable (comparison (d := d) P hR hc hsmall clock label) :=
  measurable_fst.fst.prodMk measurable_fst.snd.snd

variable (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
local instance : MeasurableSpace (Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs)) := prefixSpace d _
local instance : MeasurableSpace (Prefix d (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))) := prefixSpace d _

theorem observation_law
    (μ : Measure (History P d × Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs)))
    [IsProbabilityMeasure μ] (ν : Measure (Base P d)) [IsProbabilityMeasure ν]
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2)) =
      ν.prod (Measure.pi fun _ : Index P => stdGaussian (Point d))) :
    (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (batchCut P hR hc hsmall clock label hK hC hy s hs) μ).map
      (observation P hR hc hsmall clock label hK hC hy s hs) =
        ν.prod (Measure.pi (FreshChildBatchCoupling.rawLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
          (data P hR hc hsmall clock label hK hC hy s hs))) := by
  let bd := data P hR hc hsmall clock label hK hC hy s hs
  let _ : ∀ i, IsProbabilityMeasure (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (FreshChildBatchCoupling.program bd i)) :=
    fun i => tapeLaw_probability (Probability.CanonicalNativeTapeLaw.primitiveLaws d) _
  have hp : MeasurePreserving (fun z : History P d ×
      Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs) => (z.1.1,z.1.2.2)) μ
      (ν.prod (Measure.pi fun _ : Index P => stdGaussian (Point d))) :=
    ⟨measurable_fst.fst.prodMk measurable_fst.snd.snd,hcomparison⟩
  have h := ((MeasurePreserving.id ν).prod (FreshChildBatchCoupling.rawSplit_preserving (Probability.CanonicalNativeTapeLaw.primitiveLaws d) bd).symm).comp
    ((measurePreserving_prodAssoc ν (Measure.pi fun _ : Index P => stdGaussian (Point d))
      (Measure.pi fun i => tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (FreshChildBatchCoupling.program bd i))).comp
        (hp.prod (MeasurePreserving.id (Measure.pi fun i => tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (FreshChildBatchCoupling.program bd i)))))
  rw [advancedLaw,Measure.map_map
    (observation_measurable P hR hc hsmall clock label hK hC hy s hs)
    (measurable_advanceHistory _)]
  simpa [Function.comp_def,observation,advanceHistory,batchParts_append,
    FreshChildBatchCoupling.rawSplit,MeasurableEquiv.prodAssoc,Equiv.prodAssoc,Prod.map,bd] using h.map_eq



theorem returned_reference_law
    (μ : Measure (History P d × Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs)))
    [IsProbabilityMeasure μ] (ν : Measure (Base P d)) [IsProbabilityMeasure ν]
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2))=
      ν.prod (Measure.pi fun _ : Index P => stdGaussian (Point d))) :
    ((advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (batchCut P hR hc hsmall clock label hK hC hy s hs) μ) ⊗ₘ conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs).map
      (fun z => (z.1.1.1,z.2))=ν.prod (Measure.pi fun _ : Index P => stdGaussian (Point d)) := by
  unfold conditional
  exact FreshChildBatchCoupling.projected_coarse_reference_law (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl
    (data P hR hc hsmall clock label hK hC hy s hs) (lower P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs)
    (fun i => center P clock hV hlo hup i)
    (center_measurable P clock hV hlo hup)
    (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (batchCut P hR hc hsmall clock label hK hC hy s hs) μ) ν
    (observation P hR hc hsmall clock label hK hC hy s hs) (observation_measurable P hR hc hsmall clock label hK hC hy s hs)
    (observation_law P hR hc hsmall clock label hK hC hy s hs μ ν hcomparison)

/-- The literal Clock matrix supplies its covariance guard internally. -/
theorem step_comparison_law
    (k : Fin (P.K+4))
    (ρ : Measure (History P d × Tape d (Host P hR hc hsmall clock label)))
    (μ : Measure (History P d × Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs)))
    [IsProbabilityMeasure μ] (ν : Measure (Base P d)) [IsProbabilityMeasure ν]
    (hsplit : ρ.map (CausalTailHistory.unpack (batchCut P hR hc hsmall clock label hK hC hy s hs))=
      μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (.batch []
        (FreshChildBatchCoupling.program (data P hR hc hsmall clock label hK hC hy s hs)) (next P hR hc hsmall clock label s))))
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2))=
      ν.prod (Measure.pi fun _ : Index P => stdGaussian (Point d))) :
    (ClockChronologicalCoupling.step P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k ∘ₘ ρ).map (comparison P hR hc hsmall clock label)=
      ν.prod (Measure.pi fun _ : Index P => stdGaussian (Point d)) := by
  have hcut := CausalTailHistory.whole_suffix_fresh_of_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
    (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)) ρ
    (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (batchCut P hR hc hsmall clock label hK hC hy s hs) μ)
    (advanced_split_of_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (batchCut P hR hc hsmall clock label hK hC hy s hs) ρ μ hsplit)
    (conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs)
  have href := returned_reference_law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ ν hcomparison
  have hnext := actual_recombine_law (ClockRepeatedLayers.residual P (P.K+4) (s.remaining-1)) _
    (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)) (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl
    (adjoin P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs ∘ₘ ρ)
    ((advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (batchCut P hR hc hsmall clock label hK hC hy s hs) μ) ⊗ₘ conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs)
    ν (fun z => z.1.1) measurable_fst.fst hcut href
    (A P clock)
    (rhoC_pos P) (a_pos P) (fun i => ClockCollocation.sum_abs_matrix_le_quarter P.delta P.delta_pos P.K clock (0 : Point d) (0 : Point d) i)
  rw [ClockChronologicalCoupling.step,← Measure.map_comp _ _
    (record_measurable P hR hc hsmall clock label hK hC hy s hs k),
    Measure.map_map (comparison_measurable P hR hc hsmall clock label) (record_measurable P hR hc hsmall clock label hK hC hy s hs k)]
  exact hnext



variable {Δ : Ctx} {τout : Ty} {q : Prog (ClockRetainedFinalSplice.size P hR hc hsmall clock) Δ τout}
  (cut : TailCut q (Host P hR hc hsmall clock label))
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d _
theorem prefixLaw_eq_of_split
    (ρ : Measure (History P d × Tape d (Host P hR hc hsmall clock label)))
    (μ : Measure (History P d × Prefix d cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) q)) :
    ρ.map (fun z => (z.1,(split cut z.2).1)) = μ := by
  let _ : IsProbabilityMeasure (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) q) := tapeLaw_probability (Probability.CanonicalNativeTapeLaw.primitiveLaws d) _
  have h := congrArg (fun ν => ν.fst) hsplit
  rw [Measure.fst_prod,Measure.fst,Measure.map_map measurable_fst
    (CausalTailHistory.measurable_unpack (Probability.CanonicalNativeTapeLaw.primitiveLaws d) cut)] at h
  exact h

theorem prefix_probability_of_split
    (ρ : Measure (History P d × Tape d (Host P hR hc hsmall clock label))) [IsProbabilityMeasure ρ]
    (μ : Measure (History P d × Prefix d cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) q)) :
    IsProbabilityMeasure μ := by
  rw [← prefixLaw_eq_of_split P hR hc hsmall clock label cut ρ μ hsplit]
  infer_instance

theorem prefix_comparison_of_split
    (ρ : Measure (History P d × Tape d (Host P hR hc hsmall clock label)))
    (μ : Measure (History P d × Prefix d cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) q)) :
    μ.map (fun z => (z.1.1,z.1.2.2)) = ρ.map (comparison P hR hc hsmall clock label) := by
  have hp : Measurable (fun z : History P d × Tape d (Host P hR hc hsmall clock label) =>
      (z.1,(split cut z.2).1)) := (CausalTailHistory.measurable_unpack (Probability.CanonicalNativeTapeLaw.primitiveLaws d) cut).fst
  rw [← prefixLaw_eq_of_split P hR hc hsmall clock label cut ρ μ hsplit,
    Measure.map_map (measurable_fst.fst.prodMk measurable_fst.snd.snd) hp]
  rfl

theorem step_cursor_comparison_law
    (k : Fin (P.K+4))
    (ρ : Measure (History P d × Tape d (Host P hR hc hsmall clock label))) [IsProbabilityMeasure ρ]
    (ν : Measure (Base P d)) [IsProbabilityMeasure ν] :
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∀ (μ : Measure (History P d × Prefix d s.cut)) [SFinite μ],
    ρ.map (CausalTailHistory.unpack s.cut)=μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Loop P hR hc hsmall clock label s.remaining s.old s.direct s.saved)) →
    ρ.map (comparison P hR hc hsmall clock label)=ν.prod (Measure.pi fun _ : Index P => stdGaussian (Point d)) →
    (ClockChronologicalCoupling.step P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k ∘ₘ ρ).map (comparison P hR hc hsmall clock label)=
      ν.prod (Measure.pi fun _ : Index P => stdGaussian (Point d)) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      dsimp only
      intro μ _ hsplit hcomparison
      let s : Cursor P hR hc hsmall clock label := ⟨remaining+1,ctx,old,direct,saved,cut⟩
      let _ : IsProbabilityMeasure μ := prefix_probability_of_split P hR hc hsmall clock label s.cut ρ μ hsplit
      have hμ := (prefix_comparison_of_split P hR hc hsmall clock label s.cut ρ μ hsplit).trans hcomparison
      exact step_comparison_law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k ρ μ ν hsplit hμ



variable (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν]
local instance entryPrefixSpace : MeasurableSpace (Prefix d (entry P hR hc hsmall clock label).cut) := prefixSpace d _
local instance tape_probability {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    IsProbabilityMeasure (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) p) :=
  tapeLaw_probability _ _
local instance entry_prefix_probability :
    IsProbabilityMeasure (prefixLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (entry P hR hc hsmall clock label).cut) :=
  prefixLaw_probability _ _
local instance initial_probability : IsProbabilityMeasure (ClockInitialComparison.initialLaw P hR hc hsmall clock label ν) := by
  unfold ClockInitialComparison.initialLaw
  infer_instance
local instance initialPrefix_sFinite : SFinite (ClockInitialComparison.initialPrefixLaw P hR hc hsmall clock label ν) := by
  unfold ClockInitialComparison.initialPrefixLaw
  infer_instance

/-- Every finite stage has the joint coarse/current Gaussian law, obtained
from the actual initialization and concrete lower-child disintegrations. -/
theorem iteration_comparison_law (k : ℕ) (hk : k≤P.K+4) :
    (iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k hk ∘ₘ ClockInitialComparison.initialLaw P hR hc hsmall clock label ν).map (comparison P hR hc hsmall clock label)=
      (ν.prod ((stdGaussian (Point d)).prod (Measure.pi fun _ : Index P => stdGaussian (Point d)))).prod (Measure.pi fun _ : Index P => stdGaussian (Point d)) := by
  induction k with
  | zero =>
    rw [iteration,Measure.id_comp]
    exact ClockInitialComparison.initial_comparison_law P hR hc hsmall clock label ν
  | succ k ih =>
    obtain ⟨μ,hμ,hcut⟩ := iteration_whole_suffix P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k (by omega)
      (ClockInitialComparison.initialLaw P hR hc hsmall clock label ν) (ClockInitialComparison.initialPrefixLaw P hR hc hsmall clock label ν)
      (ClockInitialComparison.initial_whole_suffix P hR hc hsmall clock label ν)
    let s := (stage P hR hc hsmall clock label k (by omega)).1
    have hs : 0<s.remaining := stage_positive P hR hc hsmall clock label k (by omega)
    let _ : SFinite μ := hμ
    have hstep := step_cursor_comparison_law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs ⟨k,by omega⟩
      (iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k (by omega) ∘ₘ ClockInitialComparison.initialLaw P hR hc hsmall clock label ν)
      (ν.prod ((stdGaussian (Point d)).prod (Measure.pi fun _ : Index P => stdGaussian (Point d)))) μ hcut (ih (by omega))
    simpa only [iteration,s,← Measure.comp_assoc] using hstep

/-- Concrete complete main-loop kernel: no supplied comparison or tail law. -/
theorem kernel_comparison_law :
    (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ ν.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))).map
      (comparison P hR hc hsmall clock label)=(ν.prod ((stdGaussian (Point d)).prod (Measure.pi fun _ : Index P => stdGaussian (Point d)))).prod
        (Measure.pi fun _ : Index P => stdGaussian (Point d)) := by
  simpa only [kernel,← Measure.comp_assoc,Measure.deterministic_comp_eq_map,ClockInitialComparison.initialLaw] using
    iteration_comparison_law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν (P.K+4) le_rfl

/-- At the reached final-child cut, the entire unread final tape is fresh
jointly of the complete retained history, and the current comparison is the
full Gaussian vector over the original input/split coarse host. -/
theorem kernel_terminal_laws :
    let s := terminalCursor P hR hc hsmall clock label
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∃ (μ : Measure (History P d × Prefix d s.cut)), IsProbabilityMeasure μ ∧
      (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ ν.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))).map
        (CausalTailHistory.unpack s.cut)=μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
          (Loop P hR hc hsmall clock label s.remaining s.old s.direct s.saved)) ∧
      μ.map (fun z => (z.1.1,z.1.2.2))=(ν.prod ((stdGaussian (Point d)).prod (Measure.pi fun _ : Index P => stdGaussian (Point d)))).prod
        (Measure.pi fun _ : Index P => stdGaussian (Point d)) := by
  obtain ⟨μ,hμ,hcut⟩ := kernel_whole_suffix P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
    (ν.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label)))
    (ClockInitialComparison.initialPrefixLaw P hR hc hsmall clock label ν) (ClockInitialComparison.initial_whole_suffix P hR hc hsmall clock label ν)
  let _ : SFinite μ := hμ
  refine ⟨μ,?_,hcut,?_⟩
  · exact prefix_probability_of_split P hR hc hsmall clock label (terminalCursor P hR hc hsmall clock label).cut _ μ hcut
  · exact (prefix_comparison_of_split P hR hc hsmall clock label (terminalCursor P hR hc hsmall clock label).cut _ μ hcut).trans
      (kernel_comparison_law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν)

end AcceleratedLogConcave.Root.ClockChronologicalLaws
