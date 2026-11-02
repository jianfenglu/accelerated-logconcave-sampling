import AcceleratedLogConcave.Root.SourcePathDimensionPayment
import AcceleratedLogConcave.Root.ClockQuadratureResolution
import AcceleratedLogConcave.Kinetic.SourceDimensionMixing

/-! A single explicit public parameter choice for the final warm-start join.
All orders, caps and thresholds depend only on accuracy/warmness/work inputs,
not the potential, condition number or oracle answers. This module pays scalar
conditions; it does not assume or assert a local KL or sampler accuracy result. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
namespace AcceleratedLogConcave.Root.SourceWarmSchedule
open Oracle Numerics Kinetic

def exponent (η : ℝ) : ℝ := min (η/3) (1/100)
def order (η Cw : ℝ) : ℕ := SourcePathDimensionPayment.precision Cw (exponent η)
def schedule (η Cw : ℝ) (D : ℕ) : Oracle.SourceSchedule :=
  SourceWorkResolution.schedule (order η Cw) (1/320) 8 (exponent η*Real.log (D:ℝ))
def baseThreshold (η Cw : ℝ) : ℝ := MeanSourceScalarAbsorption.threshold
  (SourceWorkResolution.schedule (order η Cw) (1/320) 8 0)

def dimensionThreshold (η Cw ε C : ℝ) : ℕ :=
  max 1 (max (sourceMixingDimension (exponent η))
    (max (SourcePhaseCoolingDimensionWork.dimensionBound (order η Cw) (1/320) 8 (exponent η))
      (max (ClockQuadratureResolution.dimensionThreshold (order η Cw) (exponent η) (baseThreshold η Cw))
        (SourcePathDimensionPayment.dimensionThreshold sourceDamping Cw (ε/4) (exponent η) C (ε/4)))))

theorem exponent_pos {η : ℝ} (hη : 0<η) : 0<exponent η := by
  unfold exponent
  exact lt_min (by positivity) (by norm_num)

theorem exponent_le_third (η : ℝ) : exponent η≤η/3 := min_le_left _ _
theorem order_ge_ten (η Cw : ℝ) : 10≤order η Cw := SourcePathDimensionPayment.precision_ge_ten _ _
theorem scalar_guards (η Cw : ℝ) (D : ℕ) :
    10≤(schedule η Cw D).K ∧ 0<(schedule η Cw D).csch ∧
    (schedule η Cw D).csch<1/160 ∧ 8≤(schedule η Cw D).Csch := by
  refine ⟨order_ge_ten η Cw,?_,?_,le_rfl⟩ <;> norm_num [schedule,SourceWorkResolution.schedule]

theorem dimension_components {η Cw ε C : ℝ} {D : ℕ}
    (hD : dimensionThreshold η Cw ε C≤D) :
    1≤D ∧ sourceMixingDimension (exponent η)≤D ∧
    SourcePhaseCoolingDimensionWork.dimensionBound (order η Cw) (1/320) 8 (exponent η)≤D ∧
    ClockQuadratureResolution.dimensionThreshold (order η Cw) (exponent η) (baseThreshold η Cw)≤D ∧
    SourcePathDimensionPayment.dimensionThreshold sourceDamping Cw (ε/4) (exponent η) C (ε/4)≤D := by
  simpa only [dimensionThreshold,max_le_iff] using hD

theorem delta_eq {η Cw ε C : ℝ} {D : ℕ} (hD : dimensionThreshold η Cw ε C≤D) :
    (schedule η Cw D).delta=(D:ℝ)^(-exponent η) :=
  SourceNumericalAccuracy.delta_dimension (by have := (dimension_components hD).1; omega)

theorem mean_threshold {η Cw ε C : ℝ} {D : ℕ} (hη : 0<η)
    (hD : dimensionThreshold η Cw ε C≤D) :
    MeanSourceScalarAbsorption.threshold (schedule η Cw D)≤(schedule η Cw D).y :=
  SourcePhaseCoolingDimensionWork.schedule_threshold (exponent_pos hη) (dimension_components hD).2.2.1

theorem quadrature_threshold {η Cw ε C : ℝ} {D : ℕ} (hη : 0<η)
    (hD : dimensionThreshold η Cw ε C≤D) :
    ClockQuadratureResolution.threshold (schedule η Cw D).K≤(schedule η Cw D).y :=
  (ClockQuadratureResolution.dimension_payments (exponent_pos hη) (dimension_components hD).2.2.2.1).2

theorem mixing_step {η Cw ε C : ℝ} {D : ℕ} (hη : 0<η)
    (hD : dimensionThreshold η Cw ε C≤D) :
    0<(schedule η Cw D).delta ∧ (schedule η Cw D).delta≤sourceMixingStep := by
  rw [delta_eq hD]
  exact source_dimension_step (exponent_pos hη) (dimension_components hD).2.1

/-- The actual source quadrature constant is paid at this one public schedule. -/
theorem quadrature_payment {η Cw ε C : ℝ} {D : ℕ} (hη : 0<η)
    (hD : dimensionThreshold η Cw ε C≤D) :
    ClockQuadraturePower.orderConstant (schedule η Cw D).K*(schedule η Cw D).delta^6≤1 :=
  ClockQuadratureResolution.order_payment _ (quadrature_threshold hη hD)

/-- All scalar contributions in the existing path comparison are paid by
this schedule. The local KL supplier itself remains a separate theorem. -/
theorem path_payment {η Cw ε C κ : ℝ} {D : ℕ}
    (hη : 0<η) (hCw : 0≤Cw) (hε : 0<ε) (hε4 : ε<1/4) (hC : 0≤C)
    (hκ : 1≤κ) (hcap : κ≤(D:ℝ)^(100:ℕ))
    (hD : dimensionThreshold η Cw ε C≤D) :
    let P := schedule η Cw D
    Real.sqrt ((D:ℝ)^Cw/2*(C*(D:ℝ)*P.delta^(2*P.K-2))*
      ((referenceHorizon (sourceRate sourceDamping κ P.delta)
        (warmMixingExponent ((D:ℝ)^(Cw+1)) (ε/4)):ℝ)/
        Schedule.Dyadic.sourceRate κ P.delta+(CoolingDyadicHorizon.count D (ε/4):ℝ)))≤ε/4 := by
  dsimp only
  rw [delta_eq hD]
  apply SourcePathDimensionPayment.epsilon_payment le_rfl
    (by exact_mod_cast (dimension_components hD).1) sourceDamping_pos hκ hcap
    (exponent_pos hη) hCw (by positivity) (by linarith) hC
    (by have := order_ge_ten η Cw; change 1≤order η Cw; omega)
    (SourcePathDimensionPayment.precision_payment (exponent_pos hη)) (by positivity)
    (dimension_components hD).2.2.2.2
end AcceleratedLogConcave.Root.SourceWarmSchedule
