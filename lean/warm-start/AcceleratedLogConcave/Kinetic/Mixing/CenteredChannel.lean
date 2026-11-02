import AcceleratedLogConcave.Kinetic.ReferenceChannel
import AcceleratedLogConcave.Kinetic.Mixing.Iteration

/-! The actual channel on mean-zero functions. Restriction commutes with the
genuine Hilbert adjoint, allowing density estimates to control test observables. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
  {μ : Measure X} {ν : Measure Y} {η : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
  {p : Ω → X} {q : Ω → Y}

instance centered_completeSpace : CompleteSpace (centered μ) :=
  (centered_isClosed μ).completeSpace_coe

/-- Restriction of the actual reference channel, using proved mean preservation. -/
def centeredReferenceChannel (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η ν) : centered ν →L[ℝ] centered μ :=
  ((referenceChannel hp hq).comp (centered ν).subtypeL).codRestrict (centered μ) (by
    intro f
    change mean μ (referenceChannel hp hq f) = 0
    rw [referenceChannel_mean]
    exact f.property)

@[simp] theorem centeredReferenceChannel_coe (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η ν) (f : centered ν) :
    (centeredReferenceChannel hp hq f : Lp ℝ 2 μ) = referenceChannel hp hq f := rfl

/-- Centering does not change the adjoint relation of the actual joint law. -/
theorem centeredReferenceChannel_adjoint (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η ν) :
    (centeredReferenceChannel hp hq).adjoint = centeredReferenceChannel hq hp := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  change inner ℝ (referenceChannel hq hp (f : Lp ℝ 2 μ)) (g : Lp ℝ 2 ν) =
    inner ℝ (f : Lp ℝ 2 μ) (referenceChannel hp hq (g : Lp ℝ 2 ν))
  rw [← referenceChannel_adjoint hp hq, ContinuousLinearMap.adjoint_inner_left]

theorem centeredReferenceChannel_norm_le (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η ν) : ‖centeredReferenceChannel hp hq‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖referenceChannel hp hq (f : Lp ℝ 2 ν)‖ ≤ 1 * ‖(f : Lp ℝ 2 ν)‖
  exact ((referenceChannel hp hq).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (referenceChannel_norm_le hp hq) (norm_nonneg _))

end AcceleratedLogConcave.Kinetic
