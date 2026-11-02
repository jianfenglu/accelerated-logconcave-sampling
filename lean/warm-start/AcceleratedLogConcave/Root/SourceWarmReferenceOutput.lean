import AcceleratedLogConcave.Root.SourceWarmReference
import AcceleratedLogConcave.Schedule.PhaseCoolingMixing
import AcceleratedLogConcave.Schedule.PhysicalReturnedLaw

/-! Exact reference output at the same actual finite counts. Mixing is
transported through the literal discard/cooling suffix and terminal bias is
paid once. Neither is supplied as a new hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace AcceleratedLogConcave.Root.SourceWarmReferenceOutput
open Oracle Numerics Kinetic
variable (η Cw ε : ℝ) (D : ℕ) (hη : 0<η)
  (hD : SourceWarmSchedule.dimensionThreshold η Cw ε SourceWarmSampler.costCoefficient≤D)
  {κ : ℝ} (hκ : 1≤κ) {V : Point D→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,κ⁻¹*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
local notation "P" => SourceWarmSchedule.schedule η Cw D
local notation "a" => Schedule.Dyadic.sourceVariance (P).delta
local notation "hI" => Schedule.PhysicalReturnedLaw.densityIntegrable hκ hV hlo
local notation "ref" => SourceWarmReference.phase η Cw ε D hη hD hκ hV hlo hup
local notation "cool" => Schedule.Dyadic.coolingKernel V hV.continuous.measurable hI a
local notation "N" => SourceWarmSampler.phases η Cw ε D κ
local notation "L" => SourceWarmSampler.cooling ε D

theorem mixing (hCw : 0≤Cw) (hε : 0<ε)
    (ν : Measure (Point D×Point D)) [IsProbabilityMeasure ν]
    (hw : Probability.L2Warm (Schedule.Dyadic.phaseReference V a) ν ((D:ℝ)^Cw)) :
    letI := Schedule.Dyadic.cooledLaw_isProbabilityMeasure hI a L
    Probability.totalVariationDistance
      (Schedule.PhaseCooling.returnedLaw ν ref Prod.fst measurable_fst cool N L)
      (Schedule.Dyadic.cooledLaw V a L)≤ε/4 := by
  let := Schedule.Dyadic.phaseReference_isProbabilityMeasure hI a
  let : ∀ j,IsProbabilityMeasure (Schedule.Dyadic.cooledLaw V a j) :=
    fun j => Schedule.Dyadic.cooledLaw_isProbabilityMeasure hI a j
  exact Schedule.PhaseCooling.returnedLaw_mixing_le ν (Schedule.Dyadic.phaseReference V a)
    (Schedule.Dyadic.cooledLaw V a) ref Prod.fst measurable_fst cool
    (Schedule.Dyadic.phaseReference_map_fst V a)
    (Schedule.Dyadic.coolingKernel_comp_cooledLaw hV.continuous.measurable hI
      (Schedule.Dyadic.sourceVariance_pos (P).delta_pos)) N L
    (SourceWarmReference.finite_mixing η Cw ε D hη hD hκ hV hlo hup hCw hε ν hw)

include hη hD hup in
theorem terminal_bias (hε : 0<ε) :
    letI := isProbabilityMeasure_tilted hI
    letI := Schedule.Dyadic.cooledLaw_isProbabilityMeasure hI a L
    Probability.totalVariationDistance (Schedule.Dyadic.cooledLaw V a L)
      (volume.tilted (fun x => -V x))≤ε/16 := by
  let := isProbabilityMeasure_tilted hI
  let := Schedule.Dyadic.cooledLaw_isProbabilityMeasure hI a L
  have hb := Schedule.PhysicalReturnedLaw.cooledLaw_heatBias_le
    (volume.tilted (fun x => -V x)) V κ hκ hV hlo hup rfl a L
  have hh : (P).delta≤1 :=
    ((SourceWarmSchedule.mixing_step hη hD).2.trans sourceMixingStep_le_quarter).trans (by norm_num)
  have hp := CoolingDyadicHorizon.bias_payment D (P).delta_pos.le hh (show 0<ε/4 by positivity)
  have he : (1/2:ℝ)*Real.sqrt ((D:ℝ)*((a/2^L:ℝ≥0):ℝ))≤ε/16 := by
    change (1/2:ℝ)*Real.sqrt ((D:ℝ)*(2*(P).delta^2/(2:ℝ)^CoolingDyadicHorizon.count D (ε/4)))≤ε/16
    convert hp using 1 <;> ring
  exact hb.trans he
end AcceleratedLogConcave.Root.SourceWarmReferenceOutput
