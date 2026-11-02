import AcceleratedLogConcave.Root.ClockChronologicalLaws
import AcceleratedLogConcave.Oracle.FreshChildBatchErrorTransfer
import AcceleratedLogConcave.Root.ClockInitialComparison
import AcceleratedLogConcave.Oracle.PrivateChronologicalLaws

/-! Full Gaussian comparison law of the actual finite retained Clock loop. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockChronologicalLowerProjection
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

local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance tape_probability {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    IsProbabilityMeasure (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) p) := tapeLaw_probability _ _
local notation "Xmain" => History P d × Tape d (Host P hR hc hsmall clock label)
def stageLaw (ρ : Measure ((Point d × Point d) × Tape d (Host P hR hc hsmall clock label)))
    (k : ℕ) (hk : k≤(P.K+4)) : Measure Xmain :=
  iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k hk ∘ₘ
    ρ.map (prepare P hR hc hsmall clock label)
instance stageLaw_probability (ρ : Measure ((Point d × Point d) × Tape d (Host P hR hc hsmall clock label)))
    [IsProbabilityMeasure ρ] (k : ℕ) (hk : k≤(P.K+4)) : IsProbabilityMeasure
    (stageLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ρ k hk) := by
  unfold stageLaw
  infer_instance
/-- Reaching a positive cursor exposes exactly its current child-batch cut.
This changes only the dependent presentation of the reached source syntax. -/
theorem cursor_batch_split (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
    (ρ : Measure Xmain) [IsProbabilityMeasure ρ]
    (hw : let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
      ∃ μ : Measure (History P d × Prefix d s.cut), SFinite μ ∧
        ρ.map (CausalTailHistory.unpack s.cut) =
          μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Loop P hR hc hsmall clock label s.remaining s.old s.direct s.saved))) :
    let cut := batchCut P hR hc hsmall clock label hK hC hy s hs
    ∃ μ : Measure (History P d × Prefix d cut), IsProbabilityMeasure μ ∧
      ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) _) ∧
      μ.map (fun z => (z.1.1,z.1.2.2)) =
        ρ.map (ClockChronologicalLaws.comparison P hR hc hsmall clock label) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => exact False.elim (Nat.not_lt_zero _ hs)
    | succ remaining =>
      obtain ⟨μ,hμ,he⟩ := hw
      let _ := hμ
      let s : Cursor P hR hc hsmall clock label := ⟨remaining+1,ctx,old,direct,saved,cut⟩
      have hp := ClockChronologicalLaws.prefix_probability_of_split P hR hc hsmall clock label s.cut ρ μ he
      exact ⟨μ,hp,he,
        ClockChronologicalLaws.prefix_comparison_of_split P hR hc hsmall clock label s.cut ρ μ he⟩

/-- Actual main occurrence lower projection, before the chronological record
update. It retains the complete current lower seed and its returned reference. -/
def mainLowerProjection (k : ℕ) (hk : k<(P.K+4)) (i : Index P) (z : Xmain × (Index P → Point d)) :
    Base P d × ((Point d × Tape d (child P hR hc hsmall clock i).program) × Point d) :=
  let s := (stage P hR hc hsmall clock label k hk.le).1
  let hs := stage_positive P hR hc hsmall clock label k hk
  let B := data P hR hc hsmall clock label hK hC hy s hs
  (z.1.1.1,FreshChildBatchErrorTransfer.completedMap B i
    ((z.1.1.2.2 i,(split (batchCut P hR hc hsmall clock label hK hC hy s hs) z.1.2).2.1 i),z.2 i))

/-- The constructed main conditional supplies its exact standalone LOWER
joint law on the actual pre-record sample, with the original P retained. -/
theorem mainLowerProjection_preserving (νInput : Measure (Point d × Point d)) [IsProbabilityMeasure νInput] (k : ℕ) (hk : k<(P.K+4)) (i : Index P) :
    MeasurePreserving (mainLowerProjection P hR hc hsmall clock label hK hC hy k hk i)
      (adjoin P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
        (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk) ∘ₘ
          stageLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (νInput.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))) k hk.le)
      ((νInput.prod ((stdGaussian (Point d)).prod (Measure.pi fun _ : Index P => stdGaussian (Point d)))) ⊗ₘ ((lower P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk)).joint i).comap ((fun i => center P clock hV hlo hup i) i) ((center_measurable P clock hV hlo hup) i)) := by
  let ρ := νInput.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))
  let μ := νInput.prod ((stdGaussian (Point d)).prod (Measure.pi fun _ : Index P => stdGaussian (Point d)))
  let s := (stage P hR hc hsmall clock label k hk.le).1
  let hs := stage_positive P hR hc hsmall clock label k hk
  let cut := batchCut P hR hc hsmall clock label hK hC hy s hs
  let B := data P hR hc hsmall clock label hK hC hy s hs
  let oldLaw := stageLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ρ k hk.le
  let : SFinite (ClockInitialComparison.initialPrefixLaw P hR hc hsmall clock label νInput) := by
    let := prefixLaw_probability (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (entry P hR hc hsmall clock label).cut
    unfold ClockInitialComparison.initialPrefixLaw
    infer_instance
  obtain ⟨ν,hν,hcursorSplit,hcmp⟩ := cursor_batch_split P hR hc hsmall clock label hK hC hy s hs oldLaw
    (iteration_whole_suffix P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k hk.le (ClockInitialComparison.initialLaw P hR hc hsmall clock label νInput) (ClockInitialComparison.initialPrefixLaw P hR hc hsmall clock label νInput) (ClockInitialComparison.initial_whole_suffix P hR hc hsmall clock label νInput))
  let _ := hν
  have hcomparison := hcmp.trans (ClockChronologicalLaws.iteration_comparison_law
    P hR hc hsmall clock label hK hC hy hV hlo hup hyMean νInput k hk.le)
  let W := History P d × Prefix d (PrivateCausalLayer.afterBatch cut)
  let obs : W → Base P d × (∀ i, FreshChildBatchCoupling.Raw d B i) :=
    observation P hR hc hsmall clock label hK hC hy s hs
  have hobs : Measurable obs := observation_measurable P hR hc hsmall clock label hK hC hy s hs
  let κ := FreshChildBatchCoupling.referenceBatch (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl B (lower P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs) (fun i => center P clock hV hlo hup i) (center_measurable P clock hV hlo hup)
  have he : conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs = κ.comap obs hobs := rfl
  let ρ := PrivateCausalLayer.advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) cut ν
  let _ : IsProbabilityMeasure ρ := PrivateChronologicalLaws.advanced_probability (Probability.CanonicalNativeTapeLaw.primitiveLaws d) cut ν
  let η := FreshChildBatchErrorTransfer.observedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl B (lower P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs) (fun i => center P clock hV hlo hup i) (center_measurable P clock hV hlo hup) ρ obs hobs
  let _ : IsProbabilityMeasure η := inferInstance
  have hproject : ρ.map obs = μ.prod
      (Measure.pi (FreshChildBatchCoupling.rawLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) B)) :=
    ClockChronologicalLaws.observation_law P hR hc hsmall clock label hK hC hy s hs ν
      μ hcomparison
  have hfull : (adjoin P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs ∘ₘ oldLaw).map
      (CausalTailHistory.unpackExtended (PrivateCausalLayer.afterBatch cut)) = η.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) _) := by
    have h := CausalTailHistory.whole_suffix_fresh_of_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (PrivateCausalLayer.afterBatch cut)
      oldLaw ρ (PrivateCausalLayer.advanced_split_of_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d) cut oldLaw ν hcursorSplit) (κ.comap obs hobs)
    change _ = (ρ ⊗ₘ κ.comap obs hobs).prod _
    rw [← he] at h ⊢
    exact h
  have hp := FreshChildBatchErrorTransfer.full_sample_projection_preserving (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
    (PrivateCausalLayer.afterBatch cut) _ η hfull
  have hl := FreshChildBatchErrorTransfer.observed_completed_preserving (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl B (lower P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs) (fun i => center P clock hV hlo hup i) (center_measurable P clock hV hlo hup)
    ρ μ obs hobs hproject i
  convert hl.comp hp using 1 <;> try rfl
  funext z
  simp only [s,cut,B,mainLowerProjection,FreshChildBatchErrorTransfer.lowerProjection,obs,
    observation,Function.comp_def,PrivateCausalLayer.split_afterBatch,
    PrivateCausalLayer.batchParts_append]

end AcceleratedLogConcave.Root.ClockChronologicalLowerProjection
