import AcceleratedLogConcave.Root.ClockChronologicalCoupling

/-! The literal Clock initialization retains its input and whole original
mixed tape. Its consumed history is independent only of the complete unread
loop suffix; the initial comparison vector has its full joint Gaussian law. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockInitialComparison
open Oracle Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut
open ClockChronologicalCoupling
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}
local notation "cut" => (entry P hR hc hsmall clock label).cut
local instance canonicalTapeSpace {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance prefixMeasurable {c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (t : TailCut q p) :
    MeasurableSpace (Prefix d t) := prefixSpace d t
local instance instructionMeasurable {c : ℕ} {Γ : Ctx} {τ : Ty} (a : Instr c Γ τ) :
    MeasurableSpace (a.Tape d) := instrSpace d a

/-- Only consumed syntax coordinates: the split draw, raw assembly and initialization array. -/
def coordinates (z : Prefix d cut) : Point d × ((ClockNoisyLayer.Index P → Point d) × (ClockNoisyLayer.Index P → Point d)) :=
  (z.2.2.1,((fun i => (z.2.2.2.2.2.1 i).1),fun i => (z.2.2.2.2.2.2.2.1 i).1))

theorem coordinates_measurable : Measurable (coordinates (d := d) P hR hc hsmall clock label) := by
  exact measurable_snd.snd.fst.prodMk ((Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_snd.snd.snd.snd.snd.fst).fst).prodMk
    (Measurable.of_eval fun i =>
      ((measurable_pi_apply i).comp measurable_snd.snd.snd.snd.snd.snd.snd.fst).fst))

def past (z : (Point d × Point d) × Prefix d cut) : History P d :=
  ((z.1,((coordinates P hR hc hsmall clock label z.2).1,
      (coordinates P hR hc hsmall clock label z.2).2.1)),
    (fun _ _ => 0,(coordinates P hR hc hsmall clock label z.2).2.2))

theorem past_measurable : Measurable (past (d := d) P hR hc hsmall clock label) := by
  have hm := (coordinates_measurable (d := d) P hR hc hsmall clock label).comp
    (measurable_snd : Measurable (Prod.snd : (Point d × Point d) × Prefix d cut → _))
  exact (measurable_fst.prodMk (hm.fst.prodMk hm.snd.fst)).prodMk (measurable_const.prodMk hm.snd.snd)

/-- The actual prepare reads only the consumed prefix, never the loop tail. -/
theorem prepare_eq_changeHistory : prepare (d := d) P hR hc hsmall clock label =
    PrivateChronologicalCoupling.changeHistory cut (past P hR hc hsmall clock label) := by
  rfl

variable (ν : Measure (Point d × Point d)) [SFinite ν]
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d
local instance tape_probability {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    IsProbabilityMeasure (tapeLaw L p) := tapeLaw_probability L p

def initialLaw := (ν.prod (tapeLaw L (Host P hR hc hsmall clock label))).map
  (prepare P hR hc hsmall clock label)

def initialPrefixLaw := (ν.prod (prefixLaw L cut)).map
  (PrivateChronologicalCoupling.changePrefix cut (past P hR hc hsmall clock label))

/-- Complete original unread suffix is fresh jointly of the augmented consumed
history and prefix, including every uniform and structural unit coordinate. -/
theorem initial_whole_suffix :
    (initialLaw P hR hc hsmall clock label ν).map (CausalTailHistory.unpack cut) =
      (initialPrefixLaw P hR hc hsmall clock label ν).prod
        (tapeLaw L (ClockRetainedFinalSplice.loop P hR hc hsmall clock label)) := by
  let := prefixLaw_probability L cut
  let := tapeLaw_probability L (ClockRetainedFinalSplice.loop P hR hc hsmall clock label)
  have hp := ((measurePreserving_prodAssoc ν (prefixLaw L cut) _).symm).comp
    ((MeasurePreserving.id ν).prod (measurePreserving_split L cut))
  rw [initialLaw,prepare_eq_changeHistory]
  exact PrivateChronologicalCoupling.changeHistory_split L cut
    (past P hR hc hsmall clock label) (past_measurable P hR hc hsmall clock label) _ _ hp.map_eq

/-- Full joint initial benchmark law over the original input, split draw and raw assembly.
No assertion conditions on the subsequently read child seeds or on a random clock. -/
theorem initial_comparison_law :
    (initialLaw P hR hc hsmall clock label ν).map (fun z => (z.1.1,z.1.2.2)) =
      (ν.prod ((stdGaussian (Point d)).prod
        (Measure.pi fun _ : ClockNoisyLayer.Index P => stdGaussian (Point d)))).prod
        (Measure.pi fun _ : ClockNoisyLayer.Index P => stdGaussian (Point d)) := by
  let : MeasurableSpace (ClockRetainedFinalSplice.MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    ClockRetainedWholeTapeLaw.mainFinalSpace P hR hc hsmall clock label
  let μ := stdGaussian (Point d)
  let μZ := Measure.pi fun _ : ClockNoisyLayer.Index P => μ
  let μM := ClockRetainedWholeTapeLaw.mainFinalLaw P hR hc hsmall clock label (d := d)
  let : IsProbabilityMeasure μM := by
    unfold μM ClockRetainedWholeTapeLaw.mainFinalLaw
    let := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
      (ClockRetainedFinalSplice.loop P hR hc hsmall clock label)
    infer_instance
  have hw : MeasurePreserving
      (ClockRetainedWholeTapeLaw.wholeTapeMeasurableEquiv P hR hc hsmall clock label)
      (tapeLaw L (Host P hR hc hsmall clock label))
      (μ.prod (μZ.prod (μZ.prod μM))) :=
    ⟨(ClockRetainedWholeTapeLaw.wholeTapeMeasurableEquiv P hR hc hsmall clock label).measurable,
      ClockRetainedWholeTapeLaw.map_wholeTape P hR hc hsmall clock label⟩
  have hkeep := (MeasurePreserving.id μ).prod
    ((MeasurePreserving.id μZ).prod (measurePreserving_fst (μ := μZ) (ν := μM)))
  have hinput := (MeasurePreserving.id ν).prod (hkeep.comp hw)
  have hinner := (MeasurePreserving.id ν).prod ((measurePreserving_prodAssoc μ μZ μZ).symm)
  have hh := ((measurePreserving_prodAssoc ν (μ.prod μZ) μZ).symm).comp (hinner.comp hinput)
  rw [initialLaw,Measure.map_map (measurable_fst.fst.prodMk measurable_fst.snd.snd)
    (prepare_measurable P hR hc hsmall clock label)]
  exact hh.map_eq

/-- The same coarse-host Gaussian product is already present in the consumed
prefix law used to start the chronological induction. -/
theorem prefix_comparison_law :
    (initialPrefixLaw P hR hc hsmall clock label ν).map (fun z => (z.1.1,z.1.2.2)) =
      (ν.prod ((stdGaussian (Point d)).prod
        (Measure.pi fun _ : ClockNoisyLayer.Index P => stdGaussian (Point d)))).prod
        (Measure.pi fun _ : ClockNoisyLayer.Index P => stdGaussian (Point d)) := by
  let := tapeLaw_probability L (ClockRetainedFinalSplice.loop P hR hc hsmall clock label)
  have hp : MeasurePreserving (fun z : History P d × Tape d (Host P hR hc hsmall clock label) =>
      (z.1,(split cut z.2).1)) (initialLaw P hR hc hsmall clock label ν)
      (initialPrefixLaw P hR hc hsmall clock label ν) :=
    measurePreserving_fst.comp
      ⟨CausalTailHistory.measurable_unpack L cut,initial_whole_suffix P hR hc hsmall clock label ν⟩
  rw [← hp.map_eq,Measure.map_map (measurable_fst.fst.prodMk measurable_fst.snd.snd) hp.measurable]
  exact initial_comparison_law P hR hc hsmall clock label ν

end AcceleratedLogConcave.Root.ClockInitialComparison
