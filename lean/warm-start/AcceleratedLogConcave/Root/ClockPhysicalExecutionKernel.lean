import AcceleratedLogConcave.Root.ClockUniformExecutionKernel
import AcceleratedLogConcave.Root.ClockPhysicalReadout
import AcceleratedLogConcave.Root.ClockJointClockExposedKernel

/-! The source momentum readout retains the original momentum and the initial
Gaussian split. The first input coordinate is the normalized center xF. This module constructs its literal execution law; accuracy and
identification with a reference transition are separate statements. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockPhysicalExecutionKernel
open MeasureTheory ProbabilityTheory Oracle Oracle.TapeLowering
open Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockRetainedFinalSplice ClockRetainedTapeTransport

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
    (hsmall : P.csch < 1/160) {d : ℕ} (ell : ℕ)

/-- Keep the original input and its actual first Gaussian; neither is redrawn. -/
def output (G : Point d → Point d)
    (a : (Point d × Point d) × (UniformValue ×
      Tape d (code P hR hc hsmall anchorClock ell))) : Point d :=
  let E0 := (ClockRetainedTapeLaw.publicPrefixMeasurableEquiv
    P hR hc hsmall anchorClock ell a.2.2).1
  a.1.2 + ClockPublicSetup.noise •
    (ClockUniformExecutionKernel.output P hR hc hsmall ell G a -
      ClockPublicSetup.splitValues a.1.2 E0 1)

/-- The readout is the source adapter using the same retained E0. -/
theorem output_eq_physicalOutput (G : Point d → Point d)
    (a : (Point d × Point d) × (UniformValue ×
      Tape d (code P hR hc hsmall anchorClock ell))) :
    output P hR hc hsmall ell G a =
      ClockPhysicalReadout.physicalOutput a.1.2
        (ClockRetainedTapeLaw.publicPrefixMeasurableEquiv
          P hR hc hsmall anchorClock ell a.2.2).1
        (ClockUniformExecutionKernel.output P hR hc hsmall ell G a) := rfl

theorem output_measurable (G : Point d → Point d) (hG : Measurable G) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    Measurable (output P hR hc hsmall ell G) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  have he := (ClockRetainedTapeLaw.publicPrefixMeasurableEquiv
    P hR hc hsmall anchorClock ell (d := d)).measurable
  have hP : Measurable (fun a : (Point d × Point d) × (UniformValue ×
      Tape d (code P hR hc hsmall anchorClock ell)) => a.1.2) := measurable_fst.snd
  have hE : Measurable (fun a : (Point d × Point d) × (UniformValue ×
      Tape d (code P hR hc hsmall anchorClock ell)) =>
      (ClockRetainedTapeLaw.publicPrefixMeasurableEquiv
        P hR hc hsmall anchorClock ell a.2.2).1) :=
    (he.comp measurable_snd.snd).fst
  have hH := (hP.const_smul ClockPublicSetup.noise).add
    (hE.const_smul (-ClockPublicSetup.s))
  exact hP.add (((ClockUniformExecutionKernel.output_measurable P hR hc hsmall ell G hG).sub hH).const_smul ClockPublicSetup.noise)

private theorem draw_probability :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    IsProbabilityMeasure (ClockUniformExecutionKernel.drawLaw P hR hc hsmall (d := d) ell) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have := (ClockPublicSetupTapeLaw.standardLaws d).uniform_probability
  have := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall anchorClock ell)
  unfold ClockUniformExecutionKernel.drawLaw
  infer_instance

/-- Finite root execution followed by the source affine momentum readout. -/
def kernel (G : Point d → Point d) (hG : Measurable G) :
    Kernel (Point d × Point d) (Point d) :=
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have := draw_probability P hR hc hsmall (d := d) ell
  Channels.freshKernel (ClockUniformExecutionKernel.drawLaw P hR hc hsmall ell)
    (output P hR hc hsmall ell G) (output_measurable P hR hc hsmall ell G hG)

instance kernel_markov (G : Point d → Point d) (hG : Measurable G) :
    IsMarkovKernel (kernel P hR hc hsmall ell G hG) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have := draw_probability P hR hc hsmall (d := d) ell
  unfold kernel
  infer_instance

/-- Exact retained input/output law, for arbitrary dependence between entering
normalized center and momentum, with the full mixed residual tape still present. -/
theorem compProd_kernel (G : Point d → Point d) (hG : Measurable G)
    (ν : Measure (Point d × Point d)) [SFinite ν] :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    ν ⊗ₘ kernel P hR hc hsmall ell G hG =
      (ν.prod (ClockUniformExecutionKernel.drawLaw P hR hc hsmall ell)).map
        (fun a => (a.1, output P hR hc hsmall ell G a)) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  unfold kernel
  have := draw_probability P hR hc hsmall (d := d) ell
  exact Channels.compProd_freshKernel ν _ _
    (output_measurable P hR hc hsmall ell G hG)

/-- The anchored implementation is exactly the source readout of the
clock's literal program, with the complete tape transported and E0 preserved. -/
theorem output_transport (G : Point d → Point d)
    (a : (Point d × Point d) × (UniformValue ×
      Tape d (code P hR hc hsmall anchorClock ell))) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    let clock := ClockUniformDraw.clockOfUniform a.2.1
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (assembled P hR hc hsmall anchorClock ell)
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    let ω := anchorTapeEquiv P hR hc hsmall clock d ell a.2.2
    output P hR hc hsmall ell G a =
      (ClockPhysicalReadout.readoutResult a.1.2 ω.2.2.1
        (run (code P hR hc hsmall clock ell) G
          ⟨table P hR hc hsmall clock,a.1.1,a.1.2⟩ Env.empty ω)).value := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  let clock := ClockUniformDraw.clockOfUniform a.2.1
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (assembled P hR hc hsmall anchorClock ell)
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let ω := anchorTapeEquiv P hR hc hsmall clock d ell a.2.2
  have hE := ClockJointClockExposedKernel.anchorTape_firstGaussian P hR hc hsmall ell
    (ClockUniformDraw.clockOfUniform a.2.1) a.2.2
  have hr := run_anchorTape P hR hc hsmall (ClockUniformDraw.clockOfUniform a.2.1)
    ell G a.1.1 a.1.2 a.2.2
  have hseed : (ClockRetainedTapeLaw.publicPrefixMeasurableEquiv
      P hR hc hsmall anchorClock ell a.2.2).1 = a.2.2.2.2.1 := rfl
  have hvalue := (congrArg (fun r : Result d .point => r.value) hr).symm
  exact congrArg₂ (ClockPhysicalReadout.physicalOutput a.1.2)
    (hseed.trans hE.symm) hvalue

/-- At the zero primitive clock the actual physical root returns its original
momentum, for every complete residual tape. -/
theorem output_zero (G : Point d → Point d) (x : Point d × Point d)
    (ω : Tape d (code P hR hc hsmall anchorClock ell)) :
    output P hR hc hsmall ell G (x,(⟨0,by constructor <;> norm_num⟩,ω)) = x.2 := by
  rw [output_transport]
  have hclock : ClockUniformDraw.clockOfUniform ⟨0,by constructor <;> norm_num⟩ =
      anchorClock := by
    apply Subtype.ext
    simp [ClockUniformDraw.clockOfUniform,anchorClock]
  dsimp only
  rw [hclock]
  exact ClockPhysicalReadout.run_code_physical_zero P hR hc hsmall ell G x.1 x.2 _

/-- Original-gradient specialization; the entering center remains normalized. -/
def originalGradientKernel (V : Point d → ℝ) (hV : ContDiff ℝ 2 V) :
    Kernel (Point d × Point d) (Point d) :=
  kernel P hR hc hsmall ell (gradient V)
    (ClockOriginalGradientKernel.originalGradient_measurable hV)

instance originalGradientKernel_markov (V : Point d → ℝ) (hV : ContDiff ℝ 2 V) :
    IsMarkovKernel (originalGradientKernel P hR hc hsmall ell V hV) := by
  unfold originalGradientKernel
  infer_instance

end AcceleratedLogConcave.Root.ClockPhysicalExecutionKernel
