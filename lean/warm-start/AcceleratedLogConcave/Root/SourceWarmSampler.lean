import AcceleratedLogConcave.Root.SourceWarmSchedule
import AcceleratedLogConcave.Root.CoolingSourceReturnedLaw

/-! Concrete finite warm-start phase/cooling kernel at the single public
parameter choice. Correctness is proved downstream, not built into the
constructor. All programs query the original gradient only. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.SourceWarmSampler
open Oracle Numerics Kinetic

def costCoefficient : ℝ := 4096
variable (η Cw ε : ℝ) (D : ℕ) (hη : 0<η)
  (hD : SourceWarmSchedule.dimensionThreshold η Cw ε costCoefficient≤D)
local notation "P" => SourceWarmSchedule.schedule η Cw D
local notation "hK" => ((SourceWarmSchedule.scalar_guards η Cw D).1)
local notation "hc" => ((SourceWarmSchedule.scalar_guards η Cw D).2.1)
local notation "hsmall" => ((SourceWarmSchedule.scalar_guards η Cw D).2.2.1)
local notation "hC" => ((SourceWarmSchedule.scalar_guards η Cw D).2.2.2)
local notation "hyMean" => SourceWarmSchedule.mean_threshold hη hD

include hη hD in
theorem private_threshold : PrivateSourceScalarAbsorption.threshold P≤(P).y :=
  MeanSourceScalarAbsorption.private_threshold P hc (by norm_num [SourceWarmSchedule.schedule,SourceWorkResolution.schedule])
    (by norm_num [SourceWarmSchedule.schedule,SourceWorkResolution.schedule]) hyMean

include hη hD in
theorem cubic_threshold : CubicScheduleThreshold.threshold P≤(P).y :=
  PrivateSourceScalarAbsorption.base_threshold P hc
    (by norm_num [SourceWarmSchedule.schedule,SourceWorkResolution.schedule])
    (by norm_num [SourceWarmSchedule.schedule,SourceWorkResolution.schedule])
    (private_threshold η Cw ε D hη hD)

include hη hD in
theorem radius_guard : (P).R≤1/2 :=
  CubicSchedulePayments.radius_guard P hK hc hsmall hC (cubic_threshold η Cw ε D hη hD)

def phases (κ : ℝ) : ℕ := referenceHorizon (sourceRate sourceDamping κ (P).delta)
  (warmMixingExponent ((D:ℝ)^(Cw+1)) (ε/4))
def cooling : ℕ := CoolingDyadicHorizon.count D (ε/4)

def phase (κ : ℝ) (V : Point D→ℝ) (hV : ContDiff ℝ 2 V) : Kernel (Point D×Point D) (Point D×Point D) :=
  ClockFinitePhaseKernel.originalGradientKernel P (radius_guard η Cw ε D hη hD) hc hsmall 0 κ V hV
instance phase_markov (κ : ℝ) (V : Point D→ℝ) (hV : ContDiff ℝ 2 V) :
    IsMarkovKernel (phase η Cw ε D hη hD κ V hV) := by unfold phase; infer_instance

def cool (V : Point D→ℝ) (j : ℕ) : Kernel (Point D) (Point D) :=
  CoolingSourceDyadicKL.implemented P hK hc hsmall hC hyMean V j
theorem cool_markov (V : Point D→ℝ) (hV : ContDiff ℝ 2 V) (j : ℕ) :
    IsMarkovKernel (cool η Cw ε D hη hD V j) :=
  CoolingSourceDyadicKL.implemented_markov P hK hc hsmall hC hyMean V hV j

/-- The law returned by the actual phase, discard and public tau=1 cooling
programs, with the prescribed finite counts. The warm input is supplied. -/
def returnedLaw (κ : ℝ) (V : Point D→ℝ) (hV : ContDiff ℝ 2 V)
    (ν : Measure (Point D×Point D)) : Measure (Point D) :=
  Schedule.PhaseCooling.returnedLaw ν (phase η Cw ε D hη hD κ V hV) Prod.fst measurable_fst
    (cool η Cw ε D hη hD V) (phases η Cw ε D κ) (cooling ε D)

/-- Fixed every-trace coefficient, depending only on the three public inputs. -/
def workConstant : ℝ := SourcePhaseCoolingDimensionWork.workConstant sourceDamping Cw (ε/4)
  (SourceWarmSchedule.exponent η)

include hη hD in
/-- This exact schedule pays the scalar path comparison, with a fixed explicit
coefficient. Establishing its actual local KL is not a premise of construction. -/
theorem scalar_path_payment (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4)
    {κ : ℝ} (hκ : 1≤κ) (hcap : κ≤(D:ℝ)^(100:ℕ)) :
    Real.sqrt ((D:ℝ)^Cw/2*(costCoefficient*(D:ℝ)*(P).delta^(2*(P).K-2))*
      ((phases η Cw ε D κ:ℝ)/Schedule.Dyadic.sourceRate κ (P).delta+(cooling ε D:ℝ)))≤ε/4 :=
  SourceWarmSchedule.path_payment hη hCw hε hε4 (by norm_num [costCoefficient]) hκ hcap hD
include hη hD in
/-- Complete every-trace query and Gaussian-block bound for precisely the
public schedule and its phase/cooling counts. Inputs and whole tapes may be
adaptive; no work or accuracy certificate is an argument. -/
theorem execution_work (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4)
    {κ : ℝ} (hκ : 1≤κ)
    (G : Point D→Point D)
    (a : Fin (phases η Cw ε D κ)→(Point D×Point D) ×
      ClockFinitePhaseKernel.Draw P (radius_guard η Cw ε D hη hD) hc hsmall (d:=D) 0)
    (x : Fin (cooling ε D)→Point D)
    (ω : ∀ i : Fin (cooling ε D),CoolingExecutable.FullTape
      (CoolingPrescribedPayments.setup P (radius_guard η Cw ε D hη hD) hc hsmall)
      D (P).delta (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K) :
    (∑ i : Fin (phases η Cw ε D κ),
      (((traceCounts (ClockFinitePhaseWork.execute P (radius_guard η Cw ε D hη hD) hc hsmall 0
        (ClockFinitePhaseKernel.sourceGamma P κ) G (a i)).trace).queries+
        (traceCounts (ClockFinitePhaseWork.execute P (radius_guard η Cw ε D hη hD) hc hsmall 0
          (ClockFinitePhaseKernel.sourceGamma P κ) G (a i)).trace).gaussianBlocks:ℕ):ℝ))+
    (∑ i : Fin (cooling ε D),
      (((traceCounts (CoolingExecutable.execute
        (CoolingPrescribedPayments.setup P (radius_guard η Cw ε D hη hD) hc hsmall)
        (P).delta (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K G (x i) (ω i)).trace).queries+
        (traceCounts (CoolingExecutable.execute
          (CoolingPrescribedPayments.setup P (radius_guard η Cw ε D hη hD) hc hsmall)
          (P).delta (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K G (x i) (ω i)).trace).gaussianBlocks:ℕ):ℝ))≤
      workConstant η Cw ε*Real.sqrt κ*(D:ℝ)^η := by
  exact SourcePhaseCoolingDimensionWork.executed_work_le
    (SourceWarmSchedule.order η Cw) D D (1/320) 8 sourceDamping κ Cw (ε/4)
    (SourceWarmSchedule.exponent η) η hK hc hsmall hC
    (SourceWarmSchedule.dimension_components hD).2.2.1 le_rfl sourceDamping_pos hκ
    (SourceWarmSchedule.exponent_pos hη) hCw (by positivity) (by linarith)
    (SourceWarmSchedule.exponent_le_third η) (fun _ => 0) G a x ω
end AcceleratedLogConcave.Root.SourceWarmSampler
