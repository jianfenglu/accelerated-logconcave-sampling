import AcceleratedLogConcave.Root.ClockRetainedWholeTapeLaw

/-! The retained root interpreter on an arbitrary joint position/momentum
input. Only fresh tape randomness is independent; the two input coordinates
need not be independent or Gaussian. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockJointInputTapeLaw
open MeasureTheory ProbabilityTheory
open Oracle Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open Oracle.CanonicalTapeFactorization Oracle.TapeLowering
open ClockRetainedFinalSplice ClockRetainedWholeTapeLaw
variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
    (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock) {d : ℕ} (ell : ℕ)

/-- Exact whole-tape packing preserves the complete original joint input. -/
theorem jointInputAndWholeTapeLaw (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν] :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
      mainFinalSpace P hR hc hsmall clock ell
    (ν.prod (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall clock ell))).map
      (Prod.map (id : Point d × Point d → Point d × Point d)
        (wholeTapeMeasurableEquiv P hR hc hsmall clock ell)) =
      ν.prod (wholeDataLaw P hR hc hsmall clock ell) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    mainFinalSpace P hR hc hsmall clock ell
  have := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell)
  have h : MeasurePreserving
      (wholeTapeMeasurableEquiv P hR hc hsmall clock ell)
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d) (code P hR hc hsmall clock ell))
      (wholeDataLaw P hR hc hsmall clock ell) :=
    ⟨(wholeTapeMeasurableEquiv P hR hc hsmall clock ell).measurable,
      map_wholeTape P hR hc hsmall clock ell⟩
  exact ((MeasurePreserving.id ν).prod h).map_eq

/-- Joint measurability of the literal root value with its original input
retained. This uses the existing evaluator and the prescribed coefficient table. -/
theorem retainedRun_measurable (G : Point d → Point d) (hG : Measurable G) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    Measurable (β := (Point d × Point d) × Point d) (fun a : (Point d × Point d) × Tape d (code P hR hc hsmall clock ell) =>
      (a.1, (run (code P hR hc hsmall clock ell) G
        ⟨table P hR hc hsmall clock, a.1.1, a.1.2⟩ Env.empty a.2).value)) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  exact measurable_fst.prodMk (program_point_of_measurable
    (α := (Point d × Point d) × Tape d (code P hR hc hsmall clock ell))
    (code P hR hc hsmall clock ell) G hG
    (fun _ => table P hR hc hsmall clock) (fun a => a.1.1) (fun a => a.1.2)
    (fun a => a.2) measurable_const measurable_fst.fst measurable_fst.snd measurable_snd)

/-- Actual joint input/output law of the finite original-oracle interpreter. -/
def retainedRunLaw (G : Point d → Point d) (ν : Measure (Point d × Point d)) :
    Measure ((Point d × Point d) × Point d) :=
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  (ν.prod (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell))).map
    (fun a => (a.1, (run (code P hR hc hsmall clock ell) G
      ⟨table P hR hc hsmall clock, a.1.1, a.1.2⟩ Env.empty a.2).value))

theorem retainedRunLaw_probability (G : Point d → Point d) (hG : Measurable G)
    (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (retainedRunLaw P hR hc hsmall clock ell G ν) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  have := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell)
  exact (Measure.isProbabilityMeasure_map_iff
    (retainedRun_measurable P hR hc hsmall clock ell G hG).aemeasurable).mpr inferInstance

/-- The actual interpreter law retains exactly the supplied joint input law. -/
theorem retainedRunLaw_input (G : Point d → Point d) (hG : Measurable G)
    (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν] :
    (retainedRunLaw P hR hc hsmall clock ell G ν).map Prod.fst = ν := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  have := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell)
  rw [retainedRunLaw, Measure.map_map measurable_fst
    (retainedRun_measurable P hR hc hsmall clock ell G hG)]
  change (ν.prod (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell))).map Prod.fst = ν
  simp

/-- Reading the exact packed tape through its inverse gives the same joint
input/output law as the actual interpreter, with all residual coordinates. -/
theorem retainedRunLaw_packed (G : Point d → Point d) (hG : Measurable G)
    (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν] :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
      mainFinalSpace P hR hc hsmall clock ell
    (ν.prod (wholeDataLaw P hR hc hsmall clock ell)).map
      (β := (Point d × Point d) × Point d)
      (fun a => (a.1, (run (code P hR hc hsmall clock ell) G
        ⟨table P hR hc hsmall clock, a.1.1, a.1.2⟩ Env.empty
        ((wholeTapeMeasurableEquiv P hR hc hsmall clock ell).symm a.2)).value)) =
      retainedRunLaw P hR hc hsmall clock ell G ν := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    mainFinalSpace P hR hc hsmall clock ell
  let e := wholeTapeMeasurableEquiv P hR hc hsmall clock ell (d := d)
  let f : (Point d × Point d) × Tape d (code P hR hc hsmall clock ell) →
      (Point d × Point d) × Point d := fun a => (a.1,
        (run (code P hR hc hsmall clock ell) G
          ⟨table P hR hc hsmall clock, a.1.1, a.1.2⟩ Env.empty a.2).value)
  let pack := Prod.map (id : Point d × Point d → Point d × Point d) e
  let unpack := Prod.map (id : Point d × Point d → Point d × Point d) e.symm
  have hm : Measurable (f ∘ unpack) :=
    (retainedRun_measurable P hR hc hsmall clock ell G hG).comp
      (measurable_id.prodMap e.symm.measurable)
  have he := jointInputAndWholeTapeLaw P hR hc hsmall clock ell ν
  change (ν.prod (wholeDataLaw P hR hc hsmall clock ell)).map (f ∘ unpack) = _
  rw [← he]
  calc
    _ = (ν.prod (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell))).map ((f ∘ unpack) ∘ pack) :=
      Measure.map_map hm (measurable_id.prodMap e.measurable)
    _ = retainedRunLaw P hR hc hsmall clock ell G ν := by
      have hf : (f ∘ unpack) ∘ pack = f := by
        funext a
        change f (a.1, e.symm (e a.2)) = f a
        rw [e.symm_apply_apply]
      rw [hf]
      rfl

end AcceleratedLogConcave.Root.ClockJointInputTapeLaw
