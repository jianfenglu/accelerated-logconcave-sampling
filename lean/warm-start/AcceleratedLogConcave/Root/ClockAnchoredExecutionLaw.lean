import AcceleratedLogConcave.Root.ClockRetainedTapeTransport
import AcceleratedLogConcave.Root.ClockJointInputExecutionKernel

/-! The literal retained-root output and input/output law on one complete
anchor tape. The clock remains fixed in each theorem; joint clock
measurability is a later coefficient-table result. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AcceleratedLogConcave.Root.ClockAnchoredExecutionLaw
open MeasureTheory ProbabilityTheory
open Oracle Oracle.TapeLowering Oracle.CanonicalTapeMeasurability
open Oracle.CanonicalTapeLaw ClockRetainedFinalSplice
open ClockRetainedTapeTransport ClockJointInputExecutionKernel

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock) {d : ℕ} (ell : ℕ)

/-- Point output of the unchanged root interpreter on the fixed zero-clock
syntax, with the actual clock's complete coefficient table. -/
def anchoredRunOutput (G : Point d → Point d)
    (a : (Point d × Point d) ×
      Tape d (code P hR hc hsmall anchorClock ell)) : Point d :=
  (run (code P hR hc hsmall anchorClock ell) G
    ⟨anchorTable P hR hc hsmall clock ell, a.1.1, a.1.2⟩ Env.empty a.2).value

theorem anchoredRunOutput_measurable (G : Point d → Point d)
    (hG : Measurable G) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    Measurable (anchoredRunOutput P hR hc hsmall clock ell G) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let e := anchorTapeEquiv P hR hc hsmall clock d ell
  have hm : Measurable (fun a : (Point d × Point d) ×
      Tape d (code P hR hc hsmall anchorClock ell) => (a.1, e a.2)) :=
    measurable_fst.prodMk (e.measurable.comp measurable_snd)
  have hf := runOutput_measurable P hR hc hsmall clock ell G hG
  have heq : anchoredRunOutput P hR hc hsmall clock ell G =
      runOutput P hR hc hsmall clock ell G ∘
        (fun a => (a.1, e a.2)) := by
    funext a
    exact (congrArg (fun r => r.value)
      (run_anchorTape P hR hc hsmall clock ell G a.1.1 a.1.2 a.2)).symm
  rw [heq]
  exact hf.comp hm

/-- The anchored complete-tape pushforward is exactly the already constructed
literal execution-kernel fiber at this clock and arbitrary joint input. -/
theorem anchored_fiber_eq_executionKernel (G : Point d → Point d)
    (hG : Measurable G) (x : Point d × Point d) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall anchorClock ell)).map
        (fun ω => anchoredRunOutput P hR hc hsmall clock ell G (x, ω)) =
      executionKernel P hR hc hsmall clock ell G hG x := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let e := anchorTapeEquiv P hR hc hsmall clock d ell
  let f : Tape d (code P hR hc hsmall anchorClock ell) → Point d :=
    fun ω => anchoredRunOutput P hR hc hsmall clock ell G (x, ω)
  let g : Tape d (code P hR hc hsmall clock ell) → Point d :=
    fun ω => runOutput P hR hc hsmall clock ell G (x, ω)
  have he : Measurable e := e.measurable
  have hg : Measurable g :=
    (runOutput_measurable P hR hc hsmall clock ell G hG).comp
      measurable_prodMk_left
  have hfg : f = g ∘ e := by
    funext ω
    exact (congrArg (fun r => r.value)
      (run_anchorTape P hR hc hsmall clock ell G x.1 x.2 ω)).symm
  calc
    _ = (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall anchorClock ell)).map (g ∘ e) := by
          change (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
            (code P hR hc hsmall anchorClock ell)).map f = _
          rw [hfg]
    _ = ((tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall anchorClock ell)).map e).map g := by
          rw [Measure.map_map hg he]
    _ = (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell)).map g := by
          rw [map_anchorTapeLaw P hR hc hsmall clock d ell]
    _ = executionKernel P hR hc hsmall clock ell G hG x :=
      (executionKernel_apply P hR hc hsmall clock ell G hG x).symm

/-- The same fixed-clock fiber packaged as a Markov kernel on arbitrary joint
position/momentum inputs. -/
def anchoredExecutionKernel (G : Point d → Point d) (hG : Measurable G) :
    Kernel (Point d × Point d) (Point d) :=
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  letI : IsProbabilityMeasure
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall anchorClock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall anchorClock ell)
  Channels.freshKernel
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall anchorClock ell))
    (anchoredRunOutput P hR hc hsmall clock ell G)
    (anchoredRunOutput_measurable P hR hc hsmall clock ell G hG)

theorem anchoredExecutionKernel_eq (G : Point d → Point d) (hG : Measurable G) :
    anchoredExecutionKernel P hR hc hsmall clock ell G hG =
      executionKernel P hR hc hsmall clock ell G hG := by
  ext x s
  exact congrArg (fun μ : Measure (Point d) => μ s)
    (anchored_fiber_eq_executionKernel P hR hc hsmall clock ell G hG x)

/-- For every joint input law, the anchor tape produces exactly the existing
literal interpreter input/output law. The input coordinates remain arbitrary. -/
theorem anchored_joint_law_eq (G : Point d → Point d) (hG : Measurable G)
    (ν : Measure (Point d × Point d)) [SFinite ν] :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    (ν.prod (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall anchorClock ell))).map
        (fun a => (a.1, anchoredRunOutput P hR hc hsmall clock ell G a)) =
      ClockJointInputTapeLaw.retainedRunLaw P hR hc hsmall clock ell G ν := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have : IsProbabilityMeasure
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall anchorClock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall anchorClock ell)
  rw [← Channels.compProd_freshKernel ν _
    (anchoredRunOutput P hR hc hsmall clock ell G)
    (anchoredRunOutput_measurable P hR hc hsmall clock ell G hG)]
  change ν ⊗ₘ anchoredExecutionKernel P hR hc hsmall clock ell G hG = _
  rw [anchoredExecutionKernel_eq P hR hc hsmall clock ell G hG]
  exact compProd_executionKernel P hR hc hsmall clock ell G hG ν

end AcceleratedLogConcave.Root.ClockAnchoredExecutionLaw
