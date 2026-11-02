import AcceleratedLogConcave.Root.ClockPhysicalExecutionKernel

/-! The finite phase uses the actual root at the normalized center, the same
uniform clock, and two fresh Gaussian draws for reheating and momentum refresh.
No claim of reference coupling or accuracy is made by its construction. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockFinitePhaseKernel
open MeasureTheory ProbabilityTheory Oracle Oracle.TapeLowering
open Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockRetainedFinalSplice ClockRetainedTapeTransport

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
    (hsmall : P.csch < 1/160) {d : ℕ} (ell : ℕ)

abbrev Draw := ((UniformValue × Tape d (code P hR hc hsmall anchorClock ell)) ×
  Point d) × Point d

/-- Physical position becomes xF=x/√h only at the input to the normalized root. -/
def normalizedInput (x : Point d × Point d) : Point d × Point d :=
  ((Real.sqrt P.delta)⁻¹ • x.1, x.2)

def output (Γ : ℝ) (G : Point d → Point d)
    (a : (Point d × Point d) × Draw P hR hc hsmall (d := d) ell) : Point d × Point d :=
  let W := ClockPhysicalExecutionKernel.output P hR hc hsmall ell G
    (normalizedInput P a.1,a.2.1.1)
  let clock := ClockUniformDraw.clockOfUniform a.2.1.1.1
  (a.1.1 + (Real.sqrt (2*P.delta^2) * (ClockPublicSetup.s * (clock : ℝ))) •
    (W+a.2.1.2), Real.exp (-Γ) • W + Real.sqrt (1-Real.exp (-2*Γ)) • a.2.2)

theorem output_measurable (Γ : ℝ) (G : Point d → Point d) (hG : Measurable G) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    Measurable (output P hR hc hsmall ell Γ G) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have hi : Measurable (normalizedInput P (d := d)) :=
    (measurable_fst.const_smul ((Real.sqrt P.delta)⁻¹)).prodMk measurable_snd
  have hW : Measurable (fun a : (Point d × Point d) × Draw P hR hc hsmall (d := d) ell =>
      ClockPhysicalExecutionKernel.output P hR hc hsmall ell G
        (normalizedInput P a.1,a.2.1.1)) := (ClockPhysicalExecutionKernel.output_measurable P hR hc hsmall ell G hG).comp
    ((hi.comp measurable_fst).prodMk measurable_snd.fst.fst)
  have hu : Measurable (fun a : (Point d × Point d) × Draw P hR hc hsmall (d := d) ell =>
      (ClockUniformDraw.clockOfUniform a.2.1.1.1 : ℝ)) :=
    measurable_subtype_coe.comp (ClockUniformDraw.measurable_clockOfUniform.comp
      measurable_snd.fst.fst.fst)
  exact (measurable_fst.fst.add
    ((hu.const_mul ClockPublicSetup.s |>.const_mul (Real.sqrt (2*P.delta^2))).smul
      (hW.add measurable_snd.fst.snd))).prodMk
    ((hW.const_smul (Real.exp (-Γ))).add
      (measurable_snd.snd.const_smul (Real.sqrt (1-Real.exp (-2*Γ)))))

def drawLaw :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    Measure (Draw P hR hc hsmall (d := d) ell) :=
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  ((ClockUniformExecutionKernel.drawLaw P hR hc hsmall ell).prod
    (stdGaussian (Point d))).prod (stdGaussian (Point d))

private theorem draw_probability :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    IsProbabilityMeasure (drawLaw P hR hc hsmall (d := d) ell) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have := (ClockPublicSetupTapeLaw.standardLaws d).uniform_probability
  have := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall anchorClock ell)
  unfold drawLaw ClockUniformExecutionKernel.drawLaw
  infer_instance

/-- Literal finite phase kernel with fresh draws independent of the joint input. -/
def kernel (Γ : ℝ) (G : Point d → Point d) (hG : Measurable G) :
    Kernel (Point d × Point d) (Point d × Point d) :=
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have := draw_probability P hR hc hsmall (d := d) ell
  Channels.freshKernel (drawLaw P hR hc hsmall ell)
    (output P hR hc hsmall ell Γ G) (output_measurable P hR hc hsmall ell Γ G hG)

instance kernel_markov (Γ : ℝ) (G : Point d → Point d) (hG : Measurable G) :
    IsMarkovKernel (kernel P hR hc hsmall ell Γ G hG) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have := draw_probability P hR hc hsmall (d := d) ell
  unfold kernel
  infer_instance

theorem compProd_kernel (Γ : ℝ) (G : Point d → Point d) (hG : Measurable G)
    (ν : Measure (Point d × Point d)) [SFinite ν] :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    ν ⊗ₘ kernel P hR hc hsmall ell Γ G hG =
      (ν.prod (drawLaw P hR hc hsmall ell)).map
        (fun a => (a.1, output P hR hc hsmall ell Γ G a)) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
    tapeSpace d (code P hR hc hsmall anchorClock ell)
  have := draw_probability P hR hc hsmall (d := d) ell
  unfold kernel
  exact Channels.compProd_freshKernel ν _ _
    (output_measurable P hR hc hsmall ell Γ G hG)

/-- Manuscript momentum refresh time, fixed before oracle answers. -/
def sourceGamma (κ : ℝ) : ℝ := P.delta / Real.sqrt (κ + 2*P.delta^2)

/-- The literal source phase, querying only the original C² potential. -/
def originalGradientKernel (κ : ℝ) (V : Point d → ℝ) (hV : ContDiff ℝ 2 V) :
    Kernel (Point d × Point d) (Point d × Point d) :=
  kernel P hR hc hsmall ell (sourceGamma P κ) (gradient V)
    (ClockOriginalGradientKernel.originalGradient_measurable hV)

instance originalGradientKernel_markov (κ : ℝ) (V : Point d → ℝ)
    (hV : ContDiff ℝ 2 V) :
    IsMarkovKernel (originalGradientKernel P hR hc hsmall ell κ V hV) := by
  unfold originalGradientKernel
  infer_instance

theorem originalGradient_compProd (κ : ℝ) (V : Point d → ℝ) (hV : ContDiff ℝ 2 V)
    (ν : Measure (Point d × Point d)) [SFinite ν] :
    let : MeasurableSpace (Tape d (code P hR hc hsmall anchorClock ell)) :=
      tapeSpace d (code P hR hc hsmall anchorClock ell)
    ν ⊗ₘ originalGradientKernel P hR hc hsmall ell κ V hV =
      (ν.prod (drawLaw P hR hc hsmall ell)).map
        (fun a => (a.1, output P hR hc hsmall ell (sourceGamma P κ) (gradient V) a)) :=
  compProd_kernel P hR hc hsmall ell (sourceGamma P κ) (gradient V)
    (ClockOriginalGradientKernel.originalGradient_measurable hV) ν

end AcceleratedLogConcave.Root.ClockFinitePhaseKernel
