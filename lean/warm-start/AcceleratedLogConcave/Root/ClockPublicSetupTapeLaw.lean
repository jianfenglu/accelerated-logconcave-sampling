import AcceleratedLogConcave.Root.ClockPublicSetup
import AcceleratedLogConcave.Oracle.SamplingCanonicalTapeLaw
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! Canonical measurable and probability transport for the literal public setup.
The target retains the complete continuation tape, including all uniforms.
The input center is already normalized. No law or independence of the retained
split outputs at a fixed input momentum is asserted. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockPublicSetupTapeLaw
open MeasureTheory ProbabilityTheory
open Oracle Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockPublicSetup

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock)
  {d : ℕ} {τ : Ty} (ell : ℕ)
  (next : Prog (size P hR hc hsmall clock) (readyCtx P) τ)

/-- Projection from the exact existing tape, with canonical measurable spaces. -/
theorem measurable_unpackTape :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
      tapeSpace d (code P hR hc hsmall clock ell next)
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    Measurable (unpackTape P hR hc hsmall clock ell next (d := d)) := by
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  let : ∀ j, MeasurableSpace (Tape d (splitRow P hR hc hsmall clock j)) :=
    fun j => tapeSpace d (splitRow P hR hc hsmall clock j)
  let : ∀ i, MeasurableSpace (Tape d (directRow P hR hc hsmall clock i)) :=
    fun i => tapeSpace d (directRow P hR hc hsmall clock i)
  exact (measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
    (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))))

/-- The inverse inserts precisely the existing unique pure-row tapes. -/
theorem measurable_packTape :
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
      tapeSpace d (code P hR hc hsmall clock ell next)
    Measurable (packTape P hR hc hsmall clock ell next (d := d)) := by
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  let : ∀ j, MeasurableSpace (Tape d (splitRow P hR hc hsmall clock j)) :=
    fun j => tapeSpace d (splitRow P hR hc hsmall clock j)
  let : ∀ i, MeasurableSpace (Tape d (directRow P hR hc hsmall clock i)) :=
    fun i => tapeSpace d (directRow P hR hc hsmall clock i)
  exact measurable_const.prodMk (measurable_const.prodMk
    (measurable_fst.prodMk (measurable_const.prodMk
      (measurable_const.prodMk measurable_snd))))

/-- Measurable upgrade of `ClockPublicSetup.tapeEquiv`, without a new carrier. -/
def tapeMeasurableEquiv :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
      tapeSpace d (code P hR hc hsmall clock ell next)
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    Tape d (code P hR hc hsmall clock ell next) ≃ᵐ Point d × Tape d next := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
    tapeSpace d (code P hR hc hsmall clock ell next)
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  exact { tapeEquiv P hR hc hsmall clock ell next with
    measurable_toFun := measurable_unpackTape P hR hc hsmall clock ell next
    measurable_invFun := measurable_packTape P hR hc hsmall clock ell next }

theorem tapeMeasurableEquiv_toEquiv :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
      tapeSpace d (code P hR hc hsmall clock ell next)
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    (tapeMeasurableEquiv P hR hc hsmall clock ell next (d := d)).toEquiv =
      tapeEquiv P hR hc hsmall clock ell next := rfl

/-- The one fresh point and the entire continuation have their exact product law. -/
theorem measurePreserving_tapeEquiv (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
      tapeSpace d (code P hR hc hsmall clock ell next)
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    MeasurePreserving (tapeMeasurableEquiv P hR hc hsmall clock ell next)
      (tapeLaw L (code P hR hc hsmall clock ell next))
      (L.pointDraw.prod (tapeLaw L next)) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
    tapeSpace d (code P hR hc hsmall clock ell next)
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  let : ∀ j, MeasurableSpace (Tape d (splitRow P hR hc hsmall clock j)) :=
    fun j => tapeSpace d (splitRow P hR hc hsmall clock j)
  let : ∀ i, MeasurableSpace (Tape d (directRow P hR hc hsmall clock i)) :=
    fun i => tapeSpace d (directRow P hR hc hsmall clock i)
  let : ∀ j, IsProbabilityMeasure (tapeLaw L (splitRow P hR hc hsmall clock j)) :=
    fun j => tapeLaw_probability L _
  let : ∀ i, IsProbabilityMeasure (tapeLaw L (directRow P hR hc hsmall clock i)) :=
    fun i => tapeLaw_probability L _
  let : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L next
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let μs := Measure.pi (fun j => tapeLaw L (splitRow P hR hc hsmall clock j))
  let μb := Measure.pi (fun i => tapeLaw L (directRow P hR hc hsmall clock i))
  let μn := tapeLaw L next
  let μ0 := Measure.dirac (α := PUnit) PUnit.unit
  have ht := (measurePreserving_snd (μ := μb) (ν := μn)).comp
    (measurePreserving_snd (μ := μs) (ν := μb.prod μn))
  have hg := (MeasurePreserving.id L.pointDraw).prod ht
  exact hg.comp ((measurePreserving_snd (μ := μ0)
    (ν := L.pointDraw.prod (μs.prod (μb.prod μn)))).comp
    (measurePreserving_snd (μ := μ0)
      (ν := μ0.prod (L.pointDraw.prod (μs.prod (μb.prod μn))))))

/-- Reverse transport uses the inverse of that same measurable equivalence. -/
theorem measurePreserving_packTape (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
      tapeSpace d (code P hR hc hsmall clock ell next)
    MeasurePreserving (packTape P hR hc hsmall clock ell next)
      (L.pointDraw.prod (tapeLaw L next))
      (tapeLaw L (code P hR hc hsmall clock ell next)) := by
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
    tapeSpace d (code P hR hc hsmall clock ell next)
  exact (measurePreserving_tapeEquiv P hR hc hsmall clock ell next L).symm
    (tapeMeasurableEquiv P hR hc hsmall clock ell next)

theorem map_unpackTape (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
      tapeSpace d (code P hR hc hsmall clock ell next)
    (tapeLaw L (code P hR hc hsmall clock ell next)).map
      (unpackTape P hR hc hsmall clock ell next) =
      L.pointDraw.prod (tapeLaw L next) := by
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
    tapeSpace d (code P hR hc hsmall clock ell next)
  exact (measurePreserving_tapeEquiv P hR hc hsmall clock ell next L).map_eq

theorem map_packTape (L : PrimitiveLaws d) :
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
      tapeSpace d (code P hR hc hsmall clock ell next)
    (L.pointDraw.prod (tapeLaw L next)).map
      (packTape P hR hc hsmall clock ell next) =
      tapeLaw L (code P hR hc hsmall clock ell next) := by
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
    tapeSpace d (code P hR hc hsmall clock ell next)
  exact (measurePreserving_packTape P hR hc hsmall clock ell next L).map_eq

/-- Literal full Result, including trace, for every target raw tape. -/
theorem run_every_tape (G : Point d → Point d) (xF momentum : Point d)
    (tape : Tape d (code P hR hc hsmall clock ell next)) :
    let data := tapeMeasurableEquiv P hR hc hsmall clock ell next tape
    let input : Inputs d (size P hR hc hsmall clock) :=
      ⟨table P hR hc hsmall clock, xF, momentum⟩
    let tail := run next G input (readyEnv P clock xF momentum data.1) data.2
    run (code P hR hc hsmall clock ell next) G input Env.empty tape =
      ⟨tail.value, Event.gaussian (origin ell) :: tail.trace⟩ :=
  ClockPublicSetup.run_every_tape P hR hc hsmall clock ell next G xF momentum tape

variable (nextPoint : Prog (size P hR hc hsmall clock) (readyCtx P) .point)

/-- Measurability of actual source execution is supplied by the evaluator theorem. -/
theorem measurable_run (G : Point d → Point d) (hG : Measurable G)
    (xF momentum : Point d) :
    @Measurable _ (Point d)
      (tapeSpace d (code P hR hc hsmall clock ell nextPoint)) _
      (fun tape => (run (code P hR hc hsmall clock ell nextPoint) G
        ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty tape).value) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell nextPoint)) :=
    tapeSpace d (code P hR hc hsmall clock ell nextPoint)
  exact program_point_of_measurable _ G hG (fun _ => table P hR hc hsmall clock)
    (fun _ => xF) (fun _ => momentum) (fun tape => tape)
    measurable_const measurable_const measurable_const measurable_id

/-- No separate measurable-ready-environment or output premise is assumed. -/
theorem measurable_ready_run (G : Point d → Point d) (hG : Measurable G)
    (xF momentum : Point d) :
    let : MeasurableSpace (Tape d nextPoint) := tapeSpace d nextPoint
    Measurable (β := Point d) (fun data : Point d × Tape d nextPoint =>
      (run nextPoint G ⟨table P hR hc hsmall clock, xF, momentum⟩
        (readyEnv P clock xF momentum data.1) data.2).value) := by
  let : MeasurableSpace (Tape d nextPoint) := tapeSpace d nextPoint
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock 0 nextPoint)) :=
    tapeSpace d (code P hR hc hsmall clock 0 nextPoint)
  have hh := (measurable_run P hR hc hsmall clock 0 nextPoint G hG xF momentum).comp
    (measurable_packTape P hR hc hsmall clock 0 nextPoint)
  have heq : (fun data : Point d × Tape d nextPoint =>
      (run (code P hR hc hsmall clock 0 nextPoint) G
        ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty
        (packTape P hR hc hsmall clock 0 nextPoint data)).value) =
      (fun data : Point d × Tape d nextPoint =>
        (run nextPoint G ⟨table P hR hc hsmall clock, xF, momentum⟩
          (readyEnv P clock xF momentum data.1) data.2).value) := by
    funext data
    have hv := congrArg (fun r : Result d .point => r.value)
      (ClockPublicSetup.run_packed P hR hc hsmall clock 0 nextPoint G xF momentum
        data.1 data.2)
    exact hv
  change Measurable (β := Point d) (fun data =>
    (run (code P hR hc hsmall clock 0 nextPoint) G
      ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty
      (packTape P hR hc hsmall clock 0 nextPoint data)).value) at hh
  rw [heq] at hh
  exact hh

/-- Source-closed execution bridge under the exact product tape law. The oracle
is measurable; all other execution measurability follows from the fixed syntax. -/
theorem run_output_law (L : PrimitiveLaws d)
    (G : Point d → Point d) (hG : Measurable G) (xF momentum : Point d) :
    let : MeasurableSpace (Tape d nextPoint) := tapeSpace d nextPoint
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell nextPoint)) :=
      tapeSpace d (code P hR hc hsmall clock ell nextPoint)
    (tapeLaw L (code P hR hc hsmall clock ell nextPoint)).map (β := Point d)
      (fun tape => (run (code P hR hc hsmall clock ell nextPoint) G
        ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty tape).value) =
    (L.pointDraw.prod (tapeLaw L nextPoint)).map (β := Point d)
      (fun data => (run nextPoint G ⟨table P hR hc hsmall clock, xF, momentum⟩
        (readyEnv P clock xF momentum data.1) data.2).value) := by
  let : MeasurableSpace (Tape d nextPoint) := tapeSpace d nextPoint
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell nextPoint)) :=
    tapeSpace d (code P hR hc hsmall clock ell nextPoint)
  rw [← map_packTape P hR hc hsmall clock ell nextPoint L]
  rw [Measure.map_map (measurable_run P hR hc hsmall clock ell nextPoint G hG xF momentum)
    (measurable_packTape P hR hc hsmall clock ell nextPoint)]
  congr 1
  funext data
  have hv := congrArg (fun r : Result d .point => r.value)
    (ClockPublicSetup.run_packed P hR hc hsmall clock ell nextPoint G xF momentum
      data.1 data.2)
  exact hv

/-- Standard Gaussian blocks and genuine closed-unit-interval uniform draws. -/
def standardLaws (d : ℕ) : PrimitiveLaws d where
  pointDraw := stdGaussian (Point d)
  uniformDraw := volume
  point_probability := inferInstance
  uniform_probability := inferInstance

theorem standard_map_unpackTape :
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
      tapeSpace d (code P hR hc hsmall clock ell next)
    (tapeLaw (standardLaws d) (code P hR hc hsmall clock ell next)).map
      (unpackTape P hR hc hsmall clock ell next) =
      (stdGaussian (Point d)).prod (tapeLaw (standardLaws d) next) :=
  map_unpackTape P hR hc hsmall clock ell next (standardLaws d)

theorem standard_map_packTape :
    let : MeasurableSpace (Tape d next) := tapeSpace d next
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell next)) :=
      tapeSpace d (code P hR hc hsmall clock ell next)
    ((stdGaussian (Point d)).prod (tapeLaw (standardLaws d) next)).map
      (packTape P hR hc hsmall clock ell next) =
      tapeLaw (standardLaws d) (code P hR hc hsmall clock ell next) :=
  map_packTape P hR hc hsmall clock ell next (standardLaws d)

theorem standard_run_output_law (G : Point d → Point d) (hG : Measurable G)
    (xF momentum : Point d) :
    let : MeasurableSpace (Tape d nextPoint) := tapeSpace d nextPoint
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell nextPoint)) :=
      tapeSpace d (code P hR hc hsmall clock ell nextPoint)
    (tapeLaw (standardLaws d) (code P hR hc hsmall clock ell nextPoint)).map (β := Point d)
      (fun tape => (run (code P hR hc hsmall clock ell nextPoint) G
        ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty tape).value) =
    ((stdGaussian (Point d)).prod (tapeLaw (standardLaws d) nextPoint)).map (β := Point d)
      (fun data => (run nextPoint G ⟨table P hR hc hsmall clock, xF, momentum⟩
        (readyEnv P clock xF momentum data.1) data.2).value) :=
  run_output_law P hR hc hsmall clock ell nextPoint (standardLaws d) G hG xF momentum

end AcceleratedLogConcave.Root.ClockPublicSetupTapeLaw
