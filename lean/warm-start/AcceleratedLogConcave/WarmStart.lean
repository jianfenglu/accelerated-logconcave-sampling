import AcceleratedLogConcave.Root.SourceWarmLocalKL
import AcceleratedLogConcave.Root.SourceWarmReferenceOutput
import AcceleratedLogConcave.Root.SourceWarmInitialization
import AcceleratedLogConcave.Root.SourceWarmComplexity

/-! The original-gradient warm-start sampler of `sources/warm-start.tex`,
Theorem 1.1. All reference accuracy, local KL, mixing, cooling and work
premises are supplied by the actual programs and original C2 hypotheses. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.WarmStart
open Oracle Root
variable (η Cw ε : ℝ) (D : ℕ) (hη : 0<η)
  (hD : SourceWarmSchedule.dimensionThreshold η Cw ε SourceWarmSampler.costCoefficient≤D)
  {κ : ℝ} (hκ : 1≤κ) {V : Point D→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,κ⁻¹*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
local notation "P" => SourceWarmSchedule.schedule η Cw D
local notation "hR" => SourceWarmSampler.radius_guard η Cw ε D hη hD
local notation "hK" => ((SourceWarmSchedule.scalar_guards η Cw D).1)
local notation "hc" => ((SourceWarmSchedule.scalar_guards η Cw D).2.1)
local notation "hsmall" => ((SourceWarmSchedule.scalar_guards η Cw D).2.2.1)
local notation "hC" => ((SourceWarmSchedule.scalar_guards η Cw D).2.2.2)
local notation "hy" => SourceWarmSchedule.mean_threshold hη hD
local notation "hI" => Schedule.PhysicalReturnedLaw.densityIntegrable hκ hV hlo
local notation "ref" => SourceWarmReference.phase η Cw ε D hη hD hκ hV hlo hup
local notation "impl" => SourceWarmSampler.phase η Cw ε D hη hD κ V hV
local notation "cool" => SourceWarmSampler.cool η Cw ε D hη hD V
local notation "a" => Schedule.Dyadic.sourceVariance (P).delta
local notation "exactCool" => Schedule.Dyadic.coolingKernel V hV.continuous.measurable hI a
local notation "N" => SourceWarmSampler.phases η Cw ε D κ
local notation "L" => SourceWarmSampler.cooling ε D

/-- Probability of the actual returned law follows from the proved program kernels. -/
instance returned_probability (ν : Measure (Point D×Point D)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (SourceWarmSampler.returnedLaw η Cw ε D hη hD κ V hV ν) := by
  let : ∀ j,IsMarkovKernel (SourceWarmSampler.cool η Cw ε D hη hD V j) :=
    fun j => SourceWarmSampler.cool_markov η Cw ε D hη hD V hV j
  unfold SourceWarmSampler.returnedLaw
  infer_instance

include hup in
/-- Actual returned-law accuracy from original C2 curvature, the condition
number cap and an arbitrary supplied joint phase-warm input. No accuracy,
coupling, derivative, mixing or local-KL certificate is an argument. -/
theorem implemented_error (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4)
    (hcap : κ≤(D:ℝ)^(100:ℕ))
    (ν : Measure (Point D×Point D)) [IsProbabilityMeasure ν]
    (hw : Probability.L2Warm (Schedule.Dyadic.phaseReference V a) ν ((D:ℝ)^Cw)) :
    letI := isProbabilityMeasure_tilted hI
    letI : ∀ j,IsMarkovKernel (cool j) :=
      fun j => SourceWarmSampler.cool_markov η Cw ε D hη hD V hV j
    Probability.totalVariationDistance
      (SourceWarmSampler.returnedLaw η Cw ε D hη hD κ V hV ν)
      (volume.tilted (fun x => -V x))≤ε := by
  let := isProbabilityMeasure_tilted hI
  let : ∀ j,IsMarkovKernel (cool j) :=
    fun j => SourceWarmSampler.cool_markov η Cw ε D hη hD V hV j
  let := Schedule.Dyadic.cooledLaw_isProbabilityMeasure hI a L
  let exactLaw := Schedule.PhaseCooling.returnedLaw ν ref Prod.fst measurable_fst exactCool N L
  let actualLaw := SourceWarmSampler.returnedLaw η Cw ε D hη hD κ V hV ν
  have hi := CoolingSourceReturnedLaw.implementation_error P hK hc hsmall hC hy V hV
    (show 0<κ⁻¹ from inv_pos.mpr (lt_of_lt_of_le (by norm_num) hκ)) hlo hup hκ
    (show 180≤SourceWarmSampler.costCoefficient by norm_num [SourceWarmSampler.costCoefficient])
    hw ref impl (SourceWarmReference.invariant η Cw ε D hη hD hκ hV hlo hup) N L
    (SourceWarmLocalKL.phase_KL η Cw ε D hη hD hκ hV hlo hup)
  have hpaid := SourceWarmSampler.scalar_path_payment η Cw ε D hη hD hCw hε hε4 hκ hcap
  have hdiff : Probability.totalVariationDistance actualLaw exactLaw≤ε/4 := by
    rw [Probability.totalVariationDistance_comm]
    exact hi.trans hpaid
  have hm := SourceWarmReferenceOutput.mixing η Cw ε D hη hD hκ hV hlo hup hCw hε ν hw
  have hb := SourceWarmReferenceOutput.terminal_bias η Cw ε D hη hD hκ hV hlo hup hε
  have he : Probability.totalVariationDistance exactLaw (volume.tilted (fun x => -V x))≤ε/4+ε/16 :=
    (Probability.totalVariationDistance_triangle exactLaw (Schedule.Dyadic.cooledLaw V a L)
      (volume.tilted (fun x => -V x))).trans (add_le_add hm hb)
  exact ((Probability.totalVariationDistance_triangle actualLaw exactLaw
    (volume.tilted (fun x => -V x))).trans (add_le_add hdiff he)).trans (by linarith)

include hη in
/-- Explicit constants fixed before the dimension, potential and oracle answers. -/
theorem public_parameters (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4) :
    0<SourceWarmSchedule.exponent η ∧ 0<SourceWarmSampler.workConstant η Cw ε :=
  ⟨SourceWarmSchedule.exponent_pos hη,
    SourceWarmComplexity.workConstant_pos η Cw ε hη hCw hε hε4⟩

include hup in
/-- Theorem 1.1: accuracy of the actual implemented returned law and the
original-gradient query bound on every complete execution, with explicit
constants depending only on η,Cw,ε. The warm sample is supplied. -/
theorem accelerated_warm_start (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4)
    (hcap : κ≤(D:ℝ)^(100:ℕ))
    (ν : Measure (Point D×Point D)) [IsProbabilityMeasure ν]
    (hw : Probability.L2Warm (Schedule.Dyadic.phaseReference V a) ν ((D:ℝ)^Cw)) :
    letI := isProbabilityMeasure_tilted hI
    letI : ∀ j,IsMarkovKernel (cool j) :=
      fun j => SourceWarmSampler.cool_markov η Cw ε D hη hD V hV j
    Probability.totalVariationDistance
      (SourceWarmSampler.returnedLaw η Cw ε D hη hD κ V hV ν)
      (volume.tilted (fun x => -V x))≤ε ∧
      ∀ (draws : Fin N→(Point D×Point D) × ClockFinitePhaseKernel.Draw P hR hc hsmall (d:=D) 0)
    (x : Fin L→Point D)
    (ω : ∀ i : Fin L,CoolingExecutable.FullTape
      (CoolingPrescribedPayments.setup P hR hc hsmall) D (P).delta
      (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K),
    (∑ i : Fin N,
      ((traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall 0
        (ClockFinitePhaseKernel.sourceGamma P κ) (gradient V) (draws i)).trace).queries:ℝ))+
    (∑ i : Fin L,
      ((traceCounts (CoolingExecutable.execute (CoolingPrescribedPayments.setup P hR hc hsmall)
        (P).delta (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K (gradient V) (x i) (ω i)).trace).queries:ℝ))≤
      SourceWarmSampler.workConstant η Cw ε*Real.sqrt κ*(D:ℝ)^η := by
  refine ⟨implemented_error η Cw ε D hη hD hκ hV hlo hup hCw hε hε4 hcap ν hw,?_⟩
  intro draws centers tapes
  exact SourceWarmComplexity.execution_queries η Cw ε D hη hD hCw hε hε4 hκ V draws centers tapes

include hup in
/-- Corollary 1.2: two independent Gaussian draws turn the supplied original
Gibbs-warm positional input into the exact phase-warm input of the same sampler.
The initialization makes no gradient query; the every-execution bound above
uses the identical phase/cooling programs and counts. -/
theorem original_target_warm_error (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4)
    (hcap : κ≤(D:ℝ)^(100:ℕ))
    (ν : Measure (Point D)) [IsProbabilityMeasure ν]
    (hw : Probability.L2Warm (volume.tilted (fun x => -V x)) ν ((D:ℝ)^Cw)) :
    letI := isProbabilityMeasure_tilted hI
    letI : ∀ j,IsMarkovKernel (cool j) :=
      fun j => SourceWarmSampler.cool_markov η Cw ε D hη hD V hV j
    Probability.totalVariationDistance
      (SourceWarmSampler.returnedLaw η Cw ε D hη hD κ V hV
        (Probability.gaussianWarmInitializationLaw ν (P).delta))
      (volume.tilted (fun x => -V x))≤ε :=
  implemented_error η Cw ε D hη hD hκ hV hlo hup hCw hε hε4 hcap _
    (SourceWarmInitialization.warm hI ν (P).delta_pos.le hw)

end AcceleratedLogConcave.WarmStart
