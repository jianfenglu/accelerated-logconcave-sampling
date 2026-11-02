import AcceleratedLogConcave.Root.ClockChronologicalCoupling
import AcceleratedLogConcave.Oracle.PrivateChronologicalCoupling

/-! Exact complete unread-suffix law of the actual finite retained Clock loop. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockChronologicalSuffix
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open Oracle.TailOccurrenceCut Oracle.PrivateCausalLayer Oracle.PrivateCausalAdvance
open TailCut Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockChronologicalCoupling ClockNoisyLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)

def updateHistory (k : Fin (P.K+4))
    (z : (History P d × (Index P → Point d)) × (Index P → Point d)) : History P d :=
  (z.1.1.1,(Function.update z.1.1.2.1 k z.1.2,comparisonUpdate P clock (z.1.2,z.2)))

theorem updateHistory_measurable (k : Fin (P.K+4)) :
    Measurable (updateHistory (d := d) P clock k) := by
  have hv : Measurable (fun z : (History P d × (Index P → Point d)) × (Index P → Point d) =>
      z.1.1.2.1) := measurable_fst.fst.snd.fst
  have hg : Measurable (fun z : (History P d × (Index P → Point d)) × (Index P → Point d) =>
      z.1.2) := measurable_fst.snd
  have hu := (measurable_update' (X := fun _ : Fin (P.K+4) => Index P → Point d) (a := k)).comp (hv.prodMk hg)
  have hn := (comparisonUpdate_measurable (d := d) P clock).comp (hg.prodMk measurable_snd)
  exact measurable_fst.fst.fst.prodMk (hu.prodMk hn)

variable (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
def layerCut := afterBatch (afterBatch (afterBatch
  (batchCut P hR hc hsmall clock label hK hC hy s hs)))

local instance : MeasurableSpace
    (Prefix d (layerCut P hR hc hsmall clock label hK hC hy s hs)) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)))) := prefixSpace d _

def residualPrefix (h : Prefix d (layerCut P hR hc hsmall clock label hK hC hy s hs)) :
    Index P → Point d :=
  let rows := batchParts (afterBatch (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))) h
  let noise := batchParts (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)) rows.1
  fun i => (noise.2 i).1

theorem residualPrefix_measurable :
    Measurable (residualPrefix (d := d) P hR hc hsmall clock label hK hC hy s hs) := by
  have hrows := measurable_batchParts (d := d)
    (afterBatch (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)))
  have hn := (measurable_batchParts (d := d)
    (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))).comp hrows.fst
  exact Measurable.of_eval fun i => ((measurable_pi_apply i).comp hn.snd).fst

def recordPast (k : Fin (P.K+4))
    (z : (History P d × (Index P → Point d)) ×
      Prefix d (layerCut P hR hc hsmall clock label hK hC hy s hs)) : History P d :=
  updateHistory P clock k
    (z.1,residualPrefix P hR hc hsmall clock label hK hC hy s hs z.2)

theorem recordPast_measurable (k : Fin (P.K+4)) :
    Measurable (recordPast (d := d) P hR hc hsmall clock label hK hC hy s hs k) := by
  exact (updateHistory_measurable P clock k).comp (measurable_fst.prodMk
    ((residualPrefix_measurable P hR hc hsmall clock label hK hC hy s hs).comp measurable_snd))

theorem changeHistory_record (k : Fin (P.K+4)) :
    PrivateChronologicalCoupling.changeHistory (layerCut P hR hc hsmall clock label hK hC hy s hs)
      (recordPast (d := d) P hR hc hsmall clock label hK hC hy s hs k) ∘
        regroupOriginal = record P hR hc hsmall clock label hK hC hy s hs k := by
  funext z
  simp only [Function.comp_def,PrivateChronologicalCoupling.changeHistory,recordPast,regroupOriginal,record,
    updateHistory,residualPrefix,layerCut,split_afterBatch,batchParts_append]

local instance : MeasurableSpace
    (Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs)) := prefixSpace d _


def returnedPrefixLaw
    (μ : Measure (History P d × Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs))) :
    Measure ((History P d × (Index P → Point d)) ×
      Prefix d (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))) :=
  (((advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (batchCut P hR hc hsmall clock label hK hC hy s hs) μ) ⊗ₘ
    conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs).map
      (regroupPrefix (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))))

instance returnedPrefixLaw_sFinite
    (μ : Measure (History P d × Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs)))
    [SFinite μ] :
    SFinite (returnedPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ) := by
  unfold returnedPrefixLaw
  infer_instance

def nextPrefixLaw (k : Fin (P.K+4))
    (μ : Measure (History P d × Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs))) :
    Measure (History P d × Prefix d (layerCut P hR hc hsmall clock label hK hC hy s hs)) :=
  (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)))
    (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))
      (returnedPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ))).map
            (PrivateChronologicalCoupling.changePrefix (layerCut P hR hc hsmall clock label hK hC hy s hs)
              (recordPast P hR hc hsmall clock label hK hC hy s hs k))

instance nextPrefixLaw_sFinite (k : Fin (P.K+4))
    (μ : Measure (History P d × Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs)))
    [SFinite μ] :
    SFinite (nextPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k μ) := by
  have hret : SFinite (returnedPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ) :=
    returnedPrefixLaw_sFinite P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ
  have hres : SFinite (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))
      (returnedPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ)) :=
    advancedLaw_sFinite (Probability.CanonicalNativeTapeLaw.primitiveLaws d) _ _
  have hrows : SFinite (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)))
      (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))
        (returnedPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ))) :=
    advancedLaw_sFinite (Probability.CanonicalNativeTapeLaw.primitiveLaws d) _ _
  unfold nextPrefixLaw
  infer_instance

/-- A concrete executed step preserves the complete next unread suffix.
Only the entering actual cut factorization is assumed; old augmented history,
the consumed prefix, and the parent momentum may correlate arbitrarily. -/
theorem step_whole_suffix (k : Fin (P.K+4))
    (ρ : Measure (History P d × Tape d (Host P hR hc hsmall clock label)))
    (μ : Measure (History P d × Prefix d (batchCut P hR hc hsmall clock label hK hC hy s hs)))
    [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (batchCut P hR hc hsmall clock label hK hC hy s hs)) =
      μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (.batch []
        (FreshChildBatchCoupling.program (data P hR hc hsmall clock label hK hC hy s hs))
        (next P hR hc hsmall clock label s)))) :
    (ClockChronologicalCoupling.step P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k ∘ₘ ρ).map
      (CausalTailHistory.unpack (layerCut P hR hc hsmall clock label hK hC hy s hs)) =
        (nextPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k μ).prod
          (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Loop P hR hc hsmall clock label (s.remaining-1) batchRef
            (fun j => preserveDirect (s.direct j)) (fun q => preserveDirect (s.saved q)))) := by
  have hcutFresh := CausalTailHistory.whole_suffix_fresh_of_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
    (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)) ρ
    (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (batchCut P hR hc hsmall clock label hK hC hy s hs) μ)
    (advanced_split_of_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (batchCut P hR hc hsmall clock label hK hC hy s hs) ρ μ hsplit)
    (conditional P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs)
  have hg := regroup_cut_law (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))
    _ _ hcutFresh
  have hn := consume_two_batches (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))
    _ _ hg
  have hret : SFinite (returnedPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ) :=
    returnedPrefixLaw_sFinite P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ
  have hres : SFinite (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))
      (returnedPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ)) :=
    advancedLaw_sFinite (Probability.CanonicalNativeTapeLaw.primitiveLaws d) _ _
  have hrows : SFinite (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)))
      (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))
        (returnedPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ))) :=
    advancedLaw_sFinite (Probability.CanonicalNativeTapeLaw.primitiveLaws d) _ _
  have hh := PrivateChronologicalCoupling.changeHistory_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (layerCut P hR hc hsmall clock label hK hC hy s hs)
    (recordPast P hR hc hsmall clock label hK hC hy s hs k)
    (recordPast_measurable P hR hc hsmall clock label hK hC hy s hs k) _
      (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs)))
        (advancedLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (batchCut P hR hc hsmall clock label hK hC hy s hs))
          (returnedPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs μ))) hn
  rw [Measure.map_map
    (PrivateChronologicalCoupling.changeHistory_measurable (Probability.CanonicalNativeTapeLaw.primitiveLaws d) _ _ (recordPast_measurable P hR hc hsmall clock label hK hC hy s hs k))
      regroupOriginal_measurable,changeHistory_record] at hh
  rw [ClockChronologicalCoupling.step,← Measure.map_comp _ _ (record_measurable P hR hc hsmall clock label hK hC hy s hs k)]
  exact hh

/-- The same advance stated at the actual entering and reached cursors.
Destructing the positive remaining count discharges the target transport;
no equality with a separately regenerated focus is assumed. -/
theorem step_cursor_whole_suffix (k : Fin (P.K+4))
    (ρ : Measure (History P d × Tape d (Host P hR hc hsmall clock label))) :
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    let : MeasurableSpace (Prefix d (advance P hR hc hsmall clock label s hs).cut) := prefixSpace d _
    ∀ (μ : Measure (History P d × Prefix d s.cut)) [SFinite μ],
    ρ.map (CausalTailHistory.unpack s.cut) =
      μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Loop P hR hc hsmall clock label s.remaining s.old s.direct s.saved)) →
    ∃ (ν : Measure (History P d × Prefix d (advance P hR hc hsmall clock label s hs).cut)),
      SFinite ν ∧
      (ClockChronologicalCoupling.step P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k ∘ₘ ρ).map
        (CausalTailHistory.unpack (advance P hR hc hsmall clock label s hs).cut) =
          ν.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Loop P hR hc hsmall clock label (s.remaining-1) batchRef
            (fun j => preserveDirect (s.direct j)) (fun q => preserveDirect (s.saved q)))) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      dsimp only
      intro μ _ hsplit
      let s : Cursor P hR hc hsmall clock label := ⟨remaining+1,ctx,old,direct,saved,cut⟩
      refine ⟨nextPrefixLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k μ,
        nextPrefixLaw_sFinite P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k μ,?_⟩
      exact step_whole_suffix P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k ρ μ hsplit



local instance entryPrefixSpace : MeasurableSpace (Prefix d (entry P hR hc hsmall clock label).cut) := prefixSpace d _

/-- Complete unread-tail factorization at every actual finite stage, from the
literal entering-prefix factorization. -/
theorem iteration_whole_suffix (k : ℕ) (hk : k≤P.K+4)
    (ρ : Measure (History P d × Tape d (Host P hR hc hsmall clock label)))
    (μ : Measure (History P d × Prefix d (entry P hR hc hsmall clock label).cut)) [SFinite μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (entry P hR hc hsmall clock label).cut)=
      μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
        (Loop P hR hc hsmall clock label (P.K+4) (entry P hR hc hsmall clock label).old (entry P hR hc hsmall clock label).direct (entry P hR hc hsmall clock label).saved))) :
    let s := (stage P hR hc hsmall clock label k hk).1
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∃ (ν : Measure (History P d × Prefix d s.cut)), SFinite ν ∧
      (iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k hk ∘ₘ ρ).map (CausalTailHistory.unpack s.cut)=
        ν.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
          (Loop P hR hc hsmall clock label s.remaining s.old s.direct s.saved)) := by
  induction k with
  | zero =>
    refine ⟨μ,inferInstance,?_⟩
    simpa only [iteration,stage,entry,Measure.id_comp] using hsplit
  | succ k ih =>
    obtain ⟨ν,hν,hcut⟩ := ih (by omega)
    let s := (stage P hR hc hsmall clock label k (by omega)).1
    have hs : 0<s.remaining := stage_positive P hR hc hsmall clock label k (by omega)
    let _ : SFinite ν := hν
    obtain ⟨ξ,hξ,hξcut⟩ := step_cursor_whole_suffix P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs ⟨k,by omega⟩
      (iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k (by omega) ∘ₘ ρ) ν hcut
    refine ⟨ξ,hξ,?_⟩
    simpa only [iteration,stage,s,advance,← Measure.comp_assoc] using hξcut

/-- The constructed whole main-loop kernel has a full fresh tail at its actual
reached final-child cut; the canonical initial factorization is the only input. -/
theorem kernel_whole_suffix
    (ρ : Measure ((Point d × Point d) × Tape d (Host P hR hc hsmall clock label)))
    (μ : Measure (History P d × Prefix d (entry P hR hc hsmall clock label).cut)) [SFinite μ]
    (hsplit : (ρ.map (prepare P hR hc hsmall clock label)).map (CausalTailHistory.unpack (entry P hR hc hsmall clock label).cut)=
      μ.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
        (Loop P hR hc hsmall clock label (P.K+4) (entry P hR hc hsmall clock label).old (entry P hR hc hsmall clock label).direct (entry P hR hc hsmall clock label).saved))) :
    let s := terminalCursor P hR hc hsmall clock label
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    ∃ (ν : Measure (History P d × Prefix d s.cut)), SFinite ν ∧
      (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ ρ).map (CausalTailHistory.unpack s.cut)=
        ν.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
          (Loop P hR hc hsmall clock label s.remaining s.old s.direct s.saved)) := by
  simpa only [kernel,← Measure.comp_assoc,Measure.deterministic_comp_eq_map,terminalCursor] using
    iteration_whole_suffix P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (P.K+4) le_rfl (ρ.map (prepare P hR hc hsmall clock label)) μ hsplit

end AcceleratedLogConcave.Root.ClockChronologicalSuffix
