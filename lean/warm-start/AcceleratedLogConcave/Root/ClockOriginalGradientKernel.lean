import AcceleratedLogConcave.Root.ClockJointInputExecutionKernel
import AcceleratedLogConcave.Root.TerminalReferenceFamily

/-! The literal retained root execution kernel with the supplied original
potential's gradient as its oracle. This is an execution-law specialization;
no reference transition or accuracy identification is asserted. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockOriginalGradientKernel
open MeasureTheory ProbabilityTheory
open Oracle Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open Oracle.TapeLowering ClockRetainedFinalSplice
open ClockJointInputTapeLaw ClockJointInputExecutionKernel

variable (P : SourceSchedule) (hR : P.R ≤ 1 / 2) (hc : 0 < P.csch)
    (hsmall : P.csch < 1 / 160) (clock : ClockLaw.Clock) {d : ℕ} (ell : ℕ)

/-- The repository's source gradient is measurable under the original `C²`
potential regularity assumption. -/
theorem originalGradient_measurable {V : Point d → ℝ}
    (hV : ContDiff ℝ 2 V) : Measurable (gradient V) :=
  (TerminalReferenceFamily.continuous_source_gradient
    (hV.of_le (by norm_num))).measurable

/-- Actual input-indexed root kernel with the literal original-gradient oracle. -/
def originalGradientKernel (V : Point d → ℝ) (hV : ContDiff ℝ 2 V) :
    Kernel (Point d × Point d) (Point d) :=
  executionKernel P hR hc hsmall clock ell (gradient V)
    (originalGradient_measurable hV)

instance originalGradientKernel_markov (V : Point d → ℝ)
    (hV : ContDiff ℝ 2 V) :
    IsMarkovKernel (originalGradientKernel P hR hc hsmall clock ell V hV) := by
  unfold originalGradientKernel
  infer_instance

/-- Every fiber pushes the canonical complete tape through the actual code
run with `gradient V` at the designated input, including entering momentum. -/
theorem originalGradientKernel_apply (V : Point d → ℝ)
    (hV : ContDiff ℝ 2 V) (x : Point d × Point d) :
    let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
      tapeSpace d (code P hR hc hsmall clock ell)
    originalGradientKernel P hR hc hsmall clock ell V hV x =
      (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
        (code P hR hc hsmall clock ell)).map
        (fun t => (show Point d from
          (run (code P hR hc hsmall clock ell) (gradient V)
            ⟨table P hR hc hsmall clock, x.1, x.2⟩ Env.empty t).value)) := by
  let : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
    tapeSpace d (code P hR hc hsmall clock ell)
  exact executionKernel_apply P hR hc hsmall clock ell (gradient V)
    (originalGradient_measurable hV) x

/-- Actual original-gradient joint input/output law for any jointly
distributed position and momentum input. -/
theorem compProd_originalGradientKernel (V : Point d → ℝ)
    (hV : ContDiff ℝ 2 V) (ν : Measure (Point d × Point d)) [SFinite ν] :
    ν ⊗ₘ originalGradientKernel P hR hc hsmall clock ell V hV =
      retainedRunLaw P hR hc hsmall clock ell (gradient V) ν :=
  compProd_executionKernel P hR hc hsmall clock ell (gradient V)
    (originalGradient_measurable hV) ν

/-- Averaging the actual original-gradient kernel gives exactly the literal
retained run's output marginal. -/
theorem originalGradient_outputLaw (V : Point d → ℝ)
    (hV : ContDiff ℝ 2 V) (ν : Measure (Point d × Point d)) [SFinite ν] :
    originalGradientKernel P hR hc hsmall clock ell V hV ∘ₘ ν =
      (retainedRunLaw P hR hc hsmall clock ell (gradient V) ν).map Prod.snd :=
  outputLaw_composition P hR hc hsmall clock ell (gradient V)
    (originalGradient_measurable hV) ν

end AcceleratedLogConcave.Root.ClockOriginalGradientKernel
