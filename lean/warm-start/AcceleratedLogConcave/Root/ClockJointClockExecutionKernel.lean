import AcceleratedLogConcave.Root.ClockAnchoredExecutionLaw
import AcceleratedLogConcave.Root.ClockRetainedTableMeasurability
import AcceleratedLogConcave.Root.ClockOriginalGradientKernel

/-! The actual retained root on a single tape space, with its source clock
and arbitrary joint position/momentum input exposed together. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockJointClockExecutionKernel
open MeasureTheory ProbabilityTheory Oracle Oracle.TapeLowering
open Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockRetainedFinalSplice ClockRetainedTapeTransport ClockAnchoredExecutionLaw
variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
    (hsmall : P.csch < 1/160) {d : ℕ} (ell : ℕ)

def output (G : Point d → Point d)
    (a : (ClockLaw.Clock × (Point d × Point d)) ×
      Tape d (code P hR hc hsmall anchorClock ell)) : Point d :=
  anchoredRunOutput P hR hc hsmall a.1.1 ell G (a.1.2,a.2)

/-- Every fiber is already the literal execution fiber. Joint measurability
will be obtained from the actual recursively constructed coefficient array. -/
theorem fiber_eq (G : Point d → Point d) (hG : Measurable G)
    (clock : ClockLaw.Clock) (x : Point d × Point d) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall anchorClock ell)).map
      (fun ω => output P hR hc hsmall ell G ((clock,x),ω)) =
      ClockJointInputExecutionKernel.executionKernel P hR hc hsmall clock ell G hG x :=
  anchored_fiber_eq_executionKernel P hR hc hsmall clock ell G hG x

/-- Joint measurability comes from the actual recursive table theorem; no
child-family or table-measurability hypothesis remains. -/
theorem output_measurable (G : Point d → Point d) (hG : Measurable G) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    Measurable (output P hR hc hsmall ell G) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  exact program_point_of_measurable
    (α := (ClockLaw.Clock × (Point d × Point d)) ×
      Tape d (code P hR hc hsmall anchorClock ell))
    (code P hR hc hsmall anchorClock ell) G hG
    (fun a => anchorTable P hR hc hsmall a.1.1 ell)
    (fun a => a.1.2.1) (fun a => a.1.2.2) (fun a => a.2)
    ((ClockRetainedTableMeasurability.measurable_anchorTable P hR hc hsmall ell).comp
      measurable_fst.fst)
    measurable_fst.snd.fst measurable_fst.snd.snd measurable_snd

/-- The literal executed root, with clock and full joint input exposed. -/
def kernel (G : Point d → Point d) (hG : Measurable G) :
    Kernel (ClockLaw.Clock × (Point d × Point d)) (Point d) :=
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  letI : IsProbabilityMeasure (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall anchorClock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall anchorClock ell)
  Channels.freshKernel
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (code P hR hc hsmall anchorClock ell))
    (output P hR hc hsmall ell G) (output_measurable P hR hc hsmall ell G hG)

instance kernel_markov (G : Point d → Point d) (hG : Measurable G) :
    IsMarkovKernel (kernel P hR hc hsmall ell G hG) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall anchorClock ell)
  unfold kernel
  infer_instance

theorem kernel_apply (G : Point d → Point d) (hG : Measurable G)
    (clock : ClockLaw.Clock) (x : Point d × Point d) :
    kernel P hR hc hsmall ell G hG (clock,x) =
      ClockJointInputExecutionKernel.executionKernel P hR hc hsmall clock ell G hG x :=
  fiber_eq P hR hc hsmall ell G hG clock x

/-- Exact retained joint law for any clock/input distribution. This does not
assert independence after conditioning on a clock or the entering momentum. -/
theorem compProd_kernel (G : Point d → Point d) (hG : Measurable G)
    (ξ : Measure (ClockLaw.Clock × (Point d × Point d))) [SFinite ξ] :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    ξ ⊗ₘ kernel P hR hc hsmall ell G hG =
      (ξ.prod (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall anchorClock ell))).map
        (fun a => (a.1,output P hR hc hsmall ell G a)) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall anchorClock ell)
  exact Channels.compProd_freshKernel ξ _ _
    (output_measurable P hR hc hsmall ell G hG)

/-- No extra oracle is present: specialize to the original C² gradient. -/
def originalGradientKernel (V : Point d → ℝ) (hV : ContDiff ℝ 2 V) :
    Kernel (ClockLaw.Clock × (Point d × Point d)) (Point d) :=
  kernel P hR hc hsmall ell (gradient V)
    (ClockOriginalGradientKernel.originalGradient_measurable hV)

instance originalGradientKernel_markov (V : Point d → ℝ) (hV : ContDiff ℝ 2 V) :
    IsMarkovKernel (originalGradientKernel P hR hc hsmall ell V hV) := by
  unfold originalGradientKernel
  infer_instance

theorem originalGradientKernel_apply (V : Point d → ℝ) (hV : ContDiff ℝ 2 V)
    (clock : ClockLaw.Clock) (x : Point d × Point d) :
    originalGradientKernel P hR hc hsmall ell V hV (clock,x) =
      ClockOriginalGradientKernel.originalGradientKernel P hR hc hsmall clock ell V hV x :=
  kernel_apply P hR hc hsmall ell (gradient V)
    (ClockOriginalGradientKernel.originalGradient_measurable hV) clock x

end AcceleratedLogConcave.Root.ClockJointClockExecutionKernel
