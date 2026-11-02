import AcceleratedLogConcave.Conditional.Flow.MaterialCommutator
import AcceleratedLogConcave.Conditional.Flow.MaterialPointwise

/-! Actual score evolution along the probability material derivative. This
is the cancellation needed in the material/weighted-adjoint commutator. -/
noncomputable section
open Set
open scoped ContDiff RealInnerProductSpace
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis Analysis.CoupledVelocityPolynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (d : PositiveVarianceFlowData E)

def scoreField (p : ℝ × E) : E :=
  p.2 + (d.r*p.1) • conditionalMean d.F d.x d.r p.1 p.2

theorem contDiffOn_scoreField : ContDiffOn ℝ ∞ d.scoreField (openDomain E) :=
  contDiff_snd.contDiffOn.add ((contDiffOn_const.mul contDiff_fst.contDiffOn).smul
    (contDiffOn_conditionalMean d.hF d.hlo d.hhi d.x d.r))

/-- D(y+r t M)=r t D M: the two first-order r M terms cancel. -/
theorem material_scoreField {t : ℝ} (ht : -1 < t ∧ t < 1) (y : E) :
    materialDerivative d.materialVelocity d.scoreField (t,y) =
      (d.r*t) • conditionalMaterialMean d.F d.x d.r t y := by
  let M : ℝ × E → E := fun p => conditionalMean d.F d.x d.r p.1 p.2
  have hM : DifferentiableAt ℝ M (t,y) :=
    ((contDiffOn_conditionalMean d.hF d.hlo d.hhi d.x d.r).contDiffAt
      ((isOpen_openDomain E).mem_nhds (show (t,y) ∈ openDomain E from ht))).differentiableAt (by simp)
  have hh := (hasFDerivAt_snd (𝕜 := ℝ) (p := (t,y))).add
    (((hasFDerivAt_fst (𝕜 := ℝ) (p := (t,y))).const_mul d.r).smul hM.hasFDerivAt)
  change HasFDerivAt d.scoreField _ (t,y) at hh
  unfold materialDerivative
  rw [hh.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  change (-d.r) • M (t,y) +
    ((d.r*t) • fderiv ℝ M (t,y) (d.materialVelocity (t,y)) + (d.r * 1) • M (t,y)) = _
  simp only [mul_one]
  change (-d.r) • M (t,y) +
    ((d.r*t) • conditionalMaterialMean d.F d.x d.r t y + d.r • M (t,y)) = _
  rw [neg_smul]
  abel

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData

namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis Analysis.CoupledVelocityPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Actual score evolution equals the positive weighted adjoint row of U1,
with its exact r t factor. This includes the nonsingular time-zero identity. -/
theorem inner_material_scoreField (d : PositiveVarianceFlowData E)
    {t : ℝ} (ht : -1 < t ∧ t < 1) (y u : E) :
    inner ℝ u (materialDerivative d.materialVelocity d.scoreField (t,y)) =
      (d.r*t) * weightedAdjoint (fun z => d.scoreField (t,z))
        (firstScaledJetRow d.F d.x u d.r t) y := by
  rw [d.material_scoreField ht y, inner_smul_right,
    conditionalMaterialMean_eq_weightedAdjoint d.hF d.hlo d.hhi d.x u d.hr.ne' ht.1 ht.2 y]
  rfl

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
