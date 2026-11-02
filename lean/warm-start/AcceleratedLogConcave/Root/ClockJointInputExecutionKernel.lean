import AcceleratedLogConcave.Root.ClockJointInputTapeLaw
import AcceleratedLogConcave.Channels.GaussianReverseKL

/-! The literal retained root interpreter as a Markov kernel on its complete
joint position/momentum input. Each fiber runs the unchanged finite program
against an independent draw of the canonical full tape. No reference-channel
identification is used. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockJointInputExecutionKernel
open MeasureTheory ProbabilityTheory
open Oracle Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open Oracle.TapeLowering ClockRetainedFinalSplice ClockJointInputTapeLaw

variable (P : SourceSchedule) (hR : P.R ≤ 1 / 2) (hc : 0 < P.csch)
    (hsmall : P.csch < 1 / 160) (clock : ClockLaw.Clock) {d : ℕ} (ell : ℕ)

/-- The point output of the actual root code for a supplied joint input and
one complete fresh syntax tape. -/
def runOutput (G : Point d → Point d)
    (a : (Point d × Point d) × Tape d (code P hR hc hsmall clock ell)) : Point d :=
  (run (code P hR hc hsmall clock ell) G
    ⟨table P hR hc hsmall clock, a.1.1, a.1.2⟩ Env.empty a.2).value

theorem runOutput_measurable (G : Point d → Point d) (hG : Measurable G) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    Measurable (runOutput P hR hc hsmall clock ell G) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  exact measurable_snd.comp
    (retainedRun_measurable P hR hc hsmall clock ell G hG)

/-- Every input is sent to its actual run output under the independent
canonical tape law. The input coordinates remain jointly arbitrary. -/
def executionKernel (G : Point d → Point d) (hG : Measurable G) :
    Kernel (Point d × Point d) (Point d) :=
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  letI : IsProbabilityMeasure
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall clock ell)
  Channels.freshKernel
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall clock ell))
    (runOutput P hR hc hsmall clock ell G)
    (runOutput_measurable P hR hc hsmall clock ell G hG)

instance executionKernel_markov (G : Point d → Point d) (hG : Measurable G) :
    IsMarkovKernel (executionKernel P hR hc hsmall clock ell G hG) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  have : IsProbabilityMeasure
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall clock ell)
  unfold executionKernel
  infer_instance

/-- The kernel's fiber is the pushforward of the same complete tape used by
the interpreter, for each particular joint input. -/
theorem executionKernel_apply (G : Point d → Point d) (hG : Measurable G)
    (x : Point d × Point d) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    executionKernel P hR hc hsmall clock ell G hG x =
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell)).map
        (fun t => runOutput P hR hc hsmall clock ell G (x, t)) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  unfold executionKernel
  rfl

/-- The literal input/output law is exactly the joint law obtained by
composing any `SFinite` joint input distribution with the execution kernel. -/
theorem compProd_executionKernel (G : Point d → Point d) (hG : Measurable G)
    (ν : Measure (Point d × Point d)) [SFinite ν] :
    ν ⊗ₘ executionKernel P hR hc hsmall clock ell G hG =
      retainedRunLaw P hR hc hsmall clock ell G ν := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  have : IsProbabilityMeasure
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall clock ell)
  unfold executionKernel retainedRunLaw
  rw [Channels.compProd_freshKernel]
  rfl

/-- Averaging the actual kernel over an arbitrary joint warm input is exactly
the output marginal of the existing retained interpreter law. -/
theorem outputLaw_composition (G : Point d → Point d) (hG : Measurable G)
    (ν : Measure (Point d × Point d)) [SFinite ν] :
    executionKernel P hR hc hsmall clock ell G hG ∘ₘ ν =
      (retainedRunLaw P hR hc hsmall clock ell G ν).map Prod.snd := by
  rw [← Measure.snd_compProd ν
    (executionKernel P hR hc hsmall clock ell G hG),
    compProd_executionKernel P hR hc hsmall clock ell G hG ν]
  rfl

end AcceleratedLogConcave.Root.ClockJointInputExecutionKernel
