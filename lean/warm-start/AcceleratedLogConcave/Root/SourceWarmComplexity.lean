import AcceleratedLogConcave.Root.SourceWarmSampler

/-! Named every-execution original-gradient complexity at the actual public
warm-start schedule. The coefficient is positive and depends only on η,Cw,ε;
the input lists and entire tapes may be adaptive. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
open scoped BigOperators
namespace AcceleratedLogConcave.Root.SourceWarmComplexity
open Oracle Numerics Kinetic
variable (η Cw ε : ℝ)

/-- The same published work coefficient is strictly positive. -/
theorem workConstant_pos (hη : 0<η) (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4) :
    0<SourceWarmSampler.workConstant η Cw ε := by
  have hp := sourceDimensionPhaseConstant_pos sourceDamping_pos
    (show 0≤Cw+1 by linarith) (SourceWarmSchedule.exponent_pos hη)
    (show 0<ε/4 by positivity) (show ε/4<1/4 by linarith)
  have hc := SourcePhaseCoolingDimensionWork.coolingConstant_pos
    (SourceWarmSchedule.exponent_pos hη) (show 0<ε/4 by positivity) (show ε/4<1/4 by linarith)
  unfold SourceWarmSampler.workConstant SourcePhaseCoolingDimensionWork.workConstant
  linarith

variable (D : ℕ) (hη : 0<η)
  (hD : SourceWarmSchedule.dimensionThreshold η Cw ε SourceWarmSampler.costCoefficient≤D)
local notation "P" => SourceWarmSchedule.schedule η Cw D
local notation "hR" => SourceWarmSampler.radius_guard η Cw ε D hη hD
local notation "hc" => ((SourceWarmSchedule.scalar_guards η Cw D).2.1)
local notation "hsmall" => ((SourceWarmSchedule.scalar_guards η Cw D).2.2.1)
local notation "N" => SourceWarmSampler.phases η Cw ε D
local notation "L" => SourceWarmSampler.cooling ε D

include hη hD in
/-- The actual original-gradient executions pay all queries and Gaussian
blocks, including both final phase refreshes and the final cooling children. -/
theorem execution_work (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4)
    {κ : ℝ} (hκ : 1≤κ)
    (V : Point D→ℝ)
    (a : Fin (SourceWarmSampler.phases η Cw ε D κ)→(Point D×Point D) ×
      ClockFinitePhaseKernel.Draw P (SourceWarmSampler.radius_guard η Cw ε D hη hD) hc hsmall (d:=D) 0)
    (x : Fin (SourceWarmSampler.cooling ε D)→Point D)
    (ω : ∀ i : Fin (SourceWarmSampler.cooling ε D),CoolingExecutable.FullTape
      (CoolingPrescribedPayments.setup P (SourceWarmSampler.radius_guard η Cw ε D hη hD) hc hsmall)
      D (P).delta (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K) :
    (∑ i : Fin (SourceWarmSampler.phases η Cw ε D κ),
      (((traceCounts (ClockFinitePhaseWork.execute P (SourceWarmSampler.radius_guard η Cw ε D hη hD) hc hsmall 0
        (ClockFinitePhaseKernel.sourceGamma P κ) (gradient V) (a i)).trace).queries+
        (traceCounts (ClockFinitePhaseWork.execute P (SourceWarmSampler.radius_guard η Cw ε D hη hD) hc hsmall 0
          (ClockFinitePhaseKernel.sourceGamma P κ) (gradient V) (a i)).trace).gaussianBlocks:ℕ):ℝ))+
    (∑ i : Fin (SourceWarmSampler.cooling ε D),
      (((traceCounts (CoolingExecutable.execute
        (CoolingPrescribedPayments.setup P (SourceWarmSampler.radius_guard η Cw ε D hη hD) hc hsmall)
        (P).delta (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K (gradient V) (x i) (ω i)).trace).queries+
        (traceCounts (CoolingExecutable.execute
          (CoolingPrescribedPayments.setup P (SourceWarmSampler.radius_guard η Cw ε D hη hD) hc hsmall)
          (P).delta (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K (gradient V) (x i) (ω i)).trace).gaussianBlocks:ℕ):ℝ))≤
      SourceWarmSampler.workConstant η Cw ε*Real.sqrt κ*(D:ℝ)^η := by
  exact SourceWarmSampler.execution_work η Cw ε D hη hD hCw hε hε4 hκ (gradient V) a x ω

include hη hD in
/-- Original-gradient query-only corollary on every complete execution list.
The actual prescribed phase and cooling counts, entering states and full tapes
are the same as in the stronger query-plus-Gaussian estimate. -/
theorem execution_queries (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4)
    {κ : ℝ} (hκ : 1≤κ) (V : Point D→ℝ)
    (a : Fin (N κ)→(Point D×Point D) × ClockFinitePhaseKernel.Draw P hR hc hsmall (d:=D) 0)
    (x : Fin L→Point D)
    (ω : ∀ i : Fin L,CoolingExecutable.FullTape
      (CoolingPrescribedPayments.setup P hR hc hsmall) D (P).delta
      (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K) :
    (∑ i : Fin (N κ),
      ((traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall 0
        (ClockFinitePhaseKernel.sourceGamma P κ) (gradient V) (a i)).trace).queries:ℝ))+
    (∑ i : Fin L,
      ((traceCounts (CoolingExecutable.execute (CoolingPrescribedPayments.setup P hR hc hsmall)
        (P).delta (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K (gradient V) (x i) (ω i)).trace).queries:ℝ))≤
      SourceWarmSampler.workConstant η Cw ε*Real.sqrt κ*(D:ℝ)^η := by
  have hfull := execution_work η Cw ε D hη hD hCw hε hε4 hκ V a x ω
  refine (add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => ?_)).trans hfull
  · exact_mod_cast Nat.le_add_right
      (traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall 0
        (ClockFinitePhaseKernel.sourceGamma P κ) (gradient V) (a i)).trace).queries
      (traceCounts (ClockFinitePhaseWork.execute P hR hc hsmall 0
        (ClockFinitePhaseKernel.sourceGamma P κ) (gradient V) (a i)).trace).gaussianBlocks
  · exact_mod_cast Nat.le_add_right
      (traceCounts (CoolingExecutable.execute (CoolingPrescribedPayments.setup P hR hc hsmall)
        (P).delta (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K (gradient V) (x i) (ω i)).trace).queries
      (traceCounts (CoolingExecutable.execute (CoolingPrescribedPayments.setup P hR hc hsmall)
        (P).delta (CoolingDyadicReference.variance (P).delta (i:ℕ)) (P).K (gradient V) (x i) (ω i)).trace).gaussianBlocks

end AcceleratedLogConcave.Root.SourceWarmComplexity
