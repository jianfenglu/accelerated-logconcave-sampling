import AcceleratedLogConcave.Root.ClockJointInputExecutionKernel

/-! Expose the literal first Gaussian draw as an input of the executed root.
Only the remaining complete syntax tape is integrated. The input may have
arbitrary position/momentum correlation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
namespace AcceleratedLogConcave.Root.ClockExposedGaussianKernel
open MeasureTheory ProbabilityTheory Oracle Oracle.TapeLowering
open Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockRetainedFinalSplice ClockRetainedTapeLaw
variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
    (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock) {d : ℕ} (ell : ℕ)

def output (G : Point d → Point d)
    (a : ((Point d × Point d) × Point d) ×
      Tape d (assembled P hR hc hsmall clock ell)) : Point d :=
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  ClockJointInputExecutionKernel.runOutput P hR hc hsmall clock ell G
    (a.1.1, (publicPrefixMeasurableEquiv P hR hc hsmall clock ell).symm (a.1.2,a.2))

theorem output_measurable (G : Point d → Point d) (hG : Measurable G) :
    let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
      tapeSpace d (assembled P hR hc hsmall clock ell)
    Measurable (output P hR hc hsmall clock ell G) := by
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let e := publicPrefixMeasurableEquiv P hR hc hsmall clock ell (d := d)
  let f : ((Point d × Point d) × Point d) ×
      Tape d (assembled P hR hc hsmall clock ell) →
        (Point d × Point d) × Tape d (code P hR hc hsmall clock ell) :=
    fun a => (a.1.1, e.symm (a.1.2,a.2))
  have hf : Measurable f :=
    measurable_fst.fst.prodMk
      (e.symm.measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  have heq : output P hR hc hsmall clock ell G =
      ClockJointInputExecutionKernel.runOutput P hR hc hsmall clock ell G ∘ f := rfl
  rw [heq]
  exact (ClockJointInputExecutionKernel.runOutput_measurable P hR hc hsmall clock ell G hG).comp hf

def kernel (G : Point d → Point d) (hG : Measurable G) :
    Kernel ((Point d × Point d) × Point d) (Point d) :=
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  letI : IsProbabilityMeasure (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (assembled P hR hc hsmall clock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
      (assembled P hR hc hsmall clock ell)
  Channels.freshKernel
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (assembled P hR hc hsmall clock ell))
    (output P hR hc hsmall clock ell G)
    (output_measurable P hR hc hsmall clock ell G hG)

instance kernel_markov (G : Point d → Point d) (hG : Measurable G) :
    IsMarkovKernel (kernel P hR hc hsmall clock ell G hG) := by
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  have := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (assembled P hR hc hsmall clock ell)
  unfold kernel
  infer_instance

/-- The literal law obtained by drawing the exposed Gaussian and every
remaining syntax-tape coordinate independently. -/
def integratedOutputLaw (G : Point d → Point d) (x : Point d × Point d) :
    Measure (Point d) :=
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  ((stdGaussian (Point d)).prod
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (assembled P hR hc hsmall clock ell))).map
    (fun a => output P hR hc hsmall clock ell G ((x,a.1),a.2))

/-- Integrating the exposed Gaussian together with the remaining full tape
recovers exactly the existing executed kernel, at every joint input. -/
theorem integrate_exposed (G : Point d → Point d) (hG : Measurable G)
    (x : Point d × Point d) :
    integratedOutputLaw P hR hc hsmall clock ell G x =
      ClockJointInputExecutionKernel.executionKernel P hR hc hsmall clock ell G hG x := by
  let : MeasurableSpace (Tape d (assembled P hR hc hsmall clock ell)) :=
    tapeSpace d (assembled P hR hc hsmall clock ell)
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  let e := publicPrefixMeasurableEquiv P hR hc hsmall clock ell (d := d)
  let μ := tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell)
  let ν := (stdGaussian (Point d)).prod
    (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (assembled P hR hc hsmall clock ell))
  let f : Point d × Tape d (assembled P hR hc hsmall clock ell) → Point d :=
    fun a => output P hR hc hsmall clock ell G ((x,a.1),a.2)
  let g : Tape d (code P hR hc hsmall clock ell) → Point d :=
    fun ω => ClockJointInputExecutionKernel.runOutput P hR hc hsmall clock ell G (x,ω)
  have hp : μ.map e = ν :=
    map_publicPrefix P hR hc hsmall clock ell
      (ClockPublicSetupTapeLaw.standardLaws d)
  have hf : Measurable f :=
    (output_measurable P hR hc hsmall clock ell G hG).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hfg : f ∘ e = g := by
    funext ω
    change ClockJointInputExecutionKernel.runOutput P hR hc hsmall clock ell G
      (x, e.symm (e ω)) = g ω
    rw [e.symm_apply_apply]
  have hm : ν.map f = μ.map g := by
    calc
      _ = (μ.map e).map f := congrArg (Measure.map f) hp.symm
      _ = μ.map (f ∘ e) := Measure.map_map hf e.measurable
      _ = μ.map g := by rw [hfg]
  change ν.map f = ClockJointInputExecutionKernel.executionKernel P hR hc hsmall clock ell G hG x
  calc
    _ = μ.map g := hm
    _ = ClockJointInputExecutionKernel.executionKernel P hR hc hsmall clock ell G hG x :=
      (ClockJointInputExecutionKernel.executionKernel_apply
        P hR hc hsmall clock ell G hG x).symm

end AcceleratedLogConcave.Root.ClockExposedGaussianKernel
