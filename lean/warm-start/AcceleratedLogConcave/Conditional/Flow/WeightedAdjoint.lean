import AcceleratedLogConcave.Kinetic.ReferenceFlow.Divergence

/-!
# Positive weighted adjoint and the material-mean sign

The scalar row of the weighted adjoint is `-div U + ⟪score,U⟫`.
The two classical continuity equations imply the material-mean identity with
this positive adjoint. This file does not assume that material identity.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace AcceleratedLogConcave.Conditional
open Analysis.Poisson Kinetic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- One row of the positive adjoint of the weighted gradient. -/
def weightedAdjoint (score U : E → E) (y : E) : ℝ :=
  -fluxDivergence U y + inner ℝ (score y) (U y)

/-- The density score turns ordinary flux divergence into the negative
weighted adjoint. -/
theorem density_mul_weightedAdjoint {p : E → ℝ} {score U : E → E} {y : E}
    (hp : HasFDerivAt p ((-p y) • innerSL ℝ (score y)) y)
    (hU : DifferentiableAt ℝ U y) :
    p y * weightedAdjoint score U y =
      -fluxDivergence (fun z => p z • U z) y := by
  rw [fluxDivergence_smul hp.differentiableAt hU, hp.fderiv]
  simp only [smul_apply, innerSL_apply_apply]
  unfold weightedAdjoint
  ring

/-- Divergence is additive for genuinely differentiable vector fields. -/
theorem fluxDivergence_add {V W : E → E} {y : E}
    (hV : DifferentiableAt ℝ V y) (hW : DifferentiableAt ℝ W y) :
    fluxDivergence (fun z => V z + W z) y =
      fluxDivergence V y + fluxDivergence W y := by
  change fluxDivergence (V + W) y = _
  rw [fluxDivergence_eq_sum_basis (stdOrthonormalBasis ℝ E) (hV.add hW),
    fluxDivergence_eq_sum_basis (stdOrthonormalBasis ℝ E) hV,
    fluxDivergence_eq_sum_basis (stdOrthonormalBasis ℝ E) hW,
    (hV.hasFDerivAt.add hW.hasFDerivAt).fderiv]
  simp only [add_apply, inner_add_right, Finset.sum_add_distrib]

/-- Subtracting the ordinary density equation from the weighted equation
leaves the positive weighted adjoint. Here `mt` is the actual time derivative
of one component of the conditional mean and `U` is its excess current. -/
theorem materialMean_eq_weightedAdjoint_of_continuity
    {p m : E → ℝ} {score v U : E → E} {y : E} {pt mt : ℝ}
    (hpos : p y ≠ 0)
    (hp : HasFDerivAt p ((-p y) • innerSL ℝ (score y)) y)
    (hm : DifferentiableAt ℝ m y) (hv : DifferentiableAt ℝ v y)
    (hU : DifferentiableAt ℝ U y)
    (hCE : pt + fluxDivergence (fun z => p z • v z) y = 0)
    (hweighted : pt * m y + p y * mt +
      fluxDivergence (fun z => (p z * m z) • v z + p z • U z) y = 0) :
    mt + fderiv ℝ m y (v y) = weightedAdjoint score U y := by
  have hflux : fluxDivergence (fun z => (p z * m z) • v z) y =
      m y * fluxDivergence (fun z => p z • v z) y +
      p y * fderiv ℝ m y (v y) := by
    change fluxDivergence (fun z => (p * m) z • v z) y = _
    rw [fluxDivergence_smul (hp.differentiableAt.mul hm) hv,
      (hp.mul hm.hasFDerivAt).fderiv,
      fluxDivergence_smul hp.differentiableAt hv]
    simp only [add_apply, smul_apply, Pi.mul_apply, hp.fderiv]
    ring
  have hadd := fluxDivergence_add ((hp.differentiableAt.mul hm).smul hv)
    (hp.differentiableAt.smul hU)
  change fluxDivergence (fun z => (p z * m z) • v z + p z • U z) y =
    fluxDivergence (fun z => (p z * m z) • v z) y +
    fluxDivergence (fun z => p z • U z) y at hadd
  rw [hadd, hflux] at hweighted
  have hAdj := density_mul_weightedAdjoint hp hU
  apply (mul_left_cancel₀ hpos)
  linear_combination hweighted - m y * hCE - hAdj

variable [MeasurableSpace E] [BorelSpace E]

/-- Compact-test characterization fixes the sign of the adjoint independently
of the continuity equations. -/
theorem weightedAdjoint_compact_ibp (p : E → ℝ) (score U : E → E) (φ : E → ℝ)
    (hp : ContDiff ℝ 1 p) (hU : ContDiff ℝ 1 U)
    (hscore : ∀ y, HasFDerivAt p ((-p y) • innerSL ℝ (score y)) y)
    (hφ : ContDiff ℝ 1 φ) (hφK : HasCompactSupport φ) :
    (∫ y, p y * weightedAdjoint score U y * φ y) =
      ∫ y, p y * fderiv ℝ φ y (U y) := by
  have h := fluxDivergence_compact_ibp (fun y => p y • U y) φ
    (hp.smul hU) hφ hφK
  calc
    _ = -(∫ y, fluxDivergence (fun z => p z • U z) y * φ y) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only
        rw [density_mul_weightedAdjoint (hscore y) (hU.differentiable_one y)]
        ring
    _ = _ := by
      rw [h.2.2, neg_neg]
      simp only [map_smul, smul_eq_mul]

end AcceleratedLogConcave.Conditional
