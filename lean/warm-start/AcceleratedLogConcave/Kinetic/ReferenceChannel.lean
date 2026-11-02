import AcceleratedLogConcave.Analysis.Poisson.Centered
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# L2 operators of actual reference couplings

A joint reference law and its two marginal maps determine the test operator
and its density adjoint. No contraction, positivity, or preservation estimate
is supplied as operator data. Actual kernel/tape constructions provide the
marginal measure-preserving identities.
-/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
  {μ : Measure X} {ν : Measure Y} {η : Measure Ω}
  {p : Ω → X} {q : Ω → Y}

/-- Conditional test expectation for the actual joint reference law. -/
def referenceChannel (hp : MeasurePreserving p η μ) (hq : MeasurePreserving q η ν) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ p hp).toContinuousLinearMap.adjoint ∘L
    (Lp.compMeasurePreservingₗᵢ ℝ q hq).toContinuousLinearMap

/-- The density operator is the ordinary L2 adjoint, with the reversed coupling. -/
theorem referenceChannel_adjoint (hp : MeasurePreserving p η μ) (hq : MeasurePreserving q η ν) :
    (referenceChannel hp hq).adjoint = referenceChannel hq hp := by
  simp [referenceChannel, ContinuousLinearMap.adjoint_comp]

/-- Exact joint-integral pairing identifies the operator with the actual channel. -/
theorem referenceChannel_pairing (hp : MeasurePreserving p η μ) (hq : MeasurePreserving q η ν)
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    inner ℝ f (referenceChannel hp hq g) = ∫ ω, f (p ω) * g (q ω) ∂η := by
  unfold referenceChannel
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving f hp, Lp.coeFn_compMeasurePreserving g hq]
    with ω hf hg
  change inner ℝ (Lp.compMeasurePreserving p hp f ω) (Lp.compMeasurePreserving q hq g ω) = _
  rw [hf, hg]
  simp [mul_comm]

/-- Contraction follows from the two actual marginal pullback isometries. -/
theorem referenceChannel_norm_le (hp : MeasurePreserving p η μ) (hq : MeasurePreserving q η ν) :
    ‖referenceChannel hp hq‖ ≤ 1 := by
  let I : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 η := Lp.compMeasurePreservingₗᵢ ℝ p hp
  let J : Lp ℝ 2 ν →ₗᵢ[ℝ] Lp ℝ 2 η := Lp.compMeasurePreservingₗᵢ ℝ q hq
  change ‖I.toContinuousLinearMap.adjoint ∘L J.toContinuousLinearMap‖ ≤ 1
  have hi : ‖I.toContinuousLinearMap‖ ≤ 1 := I.norm_toContinuousLinearMap_le
  have hj : ‖J.toContinuousLinearMap‖ ≤ 1 := J.norm_toContinuousLinearMap_le
  calc
    _ ≤ ‖I.toContinuousLinearMap.adjoint‖ * ‖J.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖I.toContinuousLinearMap‖ * ‖J.toContinuousLinearMap‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * 1 := mul_le_mul hi hj (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η]

private theorem pullback_one (hp : MeasurePreserving p η μ) :
    Lp.compMeasurePreservingₗᵢ ℝ p hp (oneL2 μ) = oneL2 η := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (oneL2 μ) hp,
    hp.quasiMeasurePreserving.ae ((memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp),
    (memLp_const (1 : ℝ) (μ := η) (p := 2)).coeFn_toLp] with ω h hμ hη
  exact h.trans (hμ.trans hη.symm)

/-- Reference invariance implies preservation of the actual constant one. -/
theorem referenceChannel_one (hp : MeasurePreserving p η μ) (hq : MeasurePreserving q η ν) :
    referenceChannel hp hq (oneL2 ν) = oneL2 μ := by
  let I : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 η := Lp.compMeasurePreservingₗᵢ ℝ p hp
  let J : Lp ℝ 2 ν →ₗᵢ[ℝ] Lp ℝ 2 η := Lp.compMeasurePreservingₗᵢ ℝ q hq
  have hq1 : J (oneL2 ν) = oneL2 η := pullback_one hq
  have hp1 : I (oneL2 μ) = oneL2 η := pullback_one hp
  change I.toContinuousLinearMap.adjoint (J (oneL2 ν)) = _
  calc
    _ = I.toContinuousLinearMap.adjoint (oneL2 η) := congrArg _ hq1
    _ = I.toContinuousLinearMap.adjoint (I (oneL2 μ)) := congrArg _ hp1.symm
    _ = oneL2 μ := congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => L (oneL2 μ))
      I.adjoint_comp_self

/-- The channel preserves the integral and therefore mean-zero inputs. -/
theorem referenceChannel_mean (hp : MeasurePreserving p η μ) (hq : MeasurePreserving q η ν)
    (g : Lp ℝ 2 ν) : mean μ (referenceChannel hp hq g) = mean ν g := by
  change inner ℝ (oneL2 μ) (referenceChannel hp hq g) = inner ℝ (oneL2 ν) g
  rw [← ContinuousLinearMap.adjoint_inner_left, referenceChannel_adjoint,
    referenceChannel_one]

/-- The genuine density adjoint preserves the integral as well. -/
theorem referenceChannel_adjoint_mean (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η ν) (f : Lp ℝ 2 μ) :
    mean ν ((referenceChannel hp hq).adjoint f) = mean μ f := by
  rw [referenceChannel_adjoint]
  exact referenceChannel_mean hq hp f

end AcceleratedLogConcave.Kinetic
