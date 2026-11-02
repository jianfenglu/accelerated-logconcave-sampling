import AcceleratedLogConcave.Numerics.SmoothConditionalError
import AcceleratedLogConcave.Numerics.SmoothForwardWeightedBudget

/-! Conditional and forward budgets on one actual all-fields receiver.
Only the two proved components are replaced. All numerical mesh/order premises
remain explicit; kernel and angle terms remain unpaid. No rotation/row error
expansion, full Regularity or state residual is asserted. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph ConditionalSmoothing
variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- The two validated component updates on the same budget. -/
def withConditionalForwardCellBudget (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    AffineResidual.Mean.DerivativeBudget d.G :=
  withForwardCellBudget d (withConditionalCellBudget d D)

theorem conditional_forward_updates_commute (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    withForwardCellBudget d (withConditionalCellBudget d D) =
      withConditionalCellBudget d (withForwardCellBudget d D) := rfl

theorem withConditionalForwardCellBudget_conditional (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    (withConditionalForwardCellBudget d D).conditional =
      fun _ ρ => conditionalCellBudget d ρ := rfl

theorem withConditionalForwardCellBudget_forward (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    (withConditionalForwardCellBudget d D).forward =
      fun _ ρ _ => forwardCellBudget d ρ := rfl

/-- The five untouched fields remain arbitrary, with no sign or regularity premise. -/
theorem withConditionalForwardCellBudget_other_fields (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    (withConditionalForwardCellBudget d D).velocity = D.velocity ∧
    (withConditionalForwardCellBudget d D).center = D.center ∧
    (withConditionalForwardCellBudget d D).backward = D.backward ∧
    (withConditionalForwardCellBudget d D).angle = D.angle ∧
    (withConditionalForwardCellBudget d D).kernel = D.kernel :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The exact conditional local-radius factor survives the forward update. -/
theorem withConditionalForwardCellBudget_conditionalError_eq (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (j : Fin m) (ρ : d.G.Kernel) :
    (withConditionalForwardCellBudget d D).conditionalError d.G d.r j ρ =
      (d.r * Real.sqrt (d.G.variance ρ)) *
        AffineResidual.cellBudget (d.G.conditional ρ) m (conditionalCellBudget d ρ) :=
  withConditionalCellBudget_conditionalError_eq d D j ρ

/-- Updating the conditional component does not alter the existing velocityError
split. In that split the forward weighted sum is divided by sigma/2. -/
theorem withConditionalForwardCellBudget_velocityError_eq (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    (withConditionalForwardCellBudget d D).velocityError d.G =
      (withForwardCellBudget d D).velocityError d.G := rfl

theorem withConditionalForwardCellBudget_conditionalError_le (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (j : Fin m) (ρ : d.G.Kernel)
    (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (hconditional : d.G.conditional ρ = conditionalGeometricInterval h₀ hh) :
    (withConditionalForwardCellBudget d D).conditionalError d.G d.r j ρ ≤
      2^(m+1)*conditionalEnd*d.ell*d.r^2*d.G.variance ρ*
        Real.sqrt (Fintype.card ι)*conditionalOrderEnvelope m*h₀^m/(m.factorial:ℝ) :=
  withConditionalCellBudget_conditionalError_le d D j ρ h₀ hh hhalf hconditional

theorem withConditionalForwardCellBudget_weightedCellBudget_le (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (hm : 2 ≤ m)
    (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2) (j : Fin m)
    (hback : h₀/4 ≤ d.G.backward.length 0)
    (hforward : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ h₀ hh) :
    (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
      |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
        ((withConditionalForwardCellBudget d D).forward j ρ a)) ≤
      40*2^(m+1)*(m:ℝ)^5*forwardDerivativeBudget d m*h₀^(m-1)/
        (d.G.psi*(m.factorial:ℝ)) :=
  withForwardCellBudget_weightedCellBudget_le d D hm h₀ hh hhalf j hback hforward

theorem withConditionalForwardCellBudget_velocityForwardContribution_le (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (hm : 2 ≤ m)
    (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2) (j : Fin m)
    (hback : h₀/4 ≤ d.G.backward.length 0)
    (hforward : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ h₀ hh) :
    (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
      |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
        ((withConditionalForwardCellBudget d D).forward j ρ a)) / (d.sigma/2) ≤
      (40*2^(m+1)*(m:ℝ)^5*forwardDerivativeBudget d m*h₀^(m-1)/
        (d.G.psi*(m.factorial:ℝ))) / (d.sigma/2) :=
  withForwardCellBudget_velocityForwardContribution_le d D hm h₀ hh hhalf j hback hforward

variable [DecidableEq ι]

theorem withConditionalForwardCellBudget_conditionalCellRegularity (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) :
    AffineResidual.CellRegularity (d.G.conditional ρ) m
      ((curvesWithSmoothBranches d).conditionalMean d.G U 0 d.r j ρ)
      ((withConditionalForwardCellBudget d D).conditional j ρ) :=
  withConditionalCellBudget_cellRegularity d D U hu j ρ

theorem withConditionalForwardCellBudget_forwardCellRegularity (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (a : Fin m) :
    AffineResidual.CellRegularity (d.G.forward ρ) m
      ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j ρ (d.G.angleNode a))
      ((withConditionalForwardCellBudget d D).forward j ρ a) :=
  withForwardCellBudget_cellRegularity_actual d D U hu j ρ a

/-- Two actual Cell families and three numerical conclusions on one budget.
The common step, both prescribed mesh families and first-width premise remain
explicit. This conjunction certifies no other field of Regularity. -/
theorem conditionalForward_cellRegularity_and_bounds (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (hm : 2 ≤ m) (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2) (j : Fin m)
    (hback : h₀/4 ≤ d.G.backward.length 0)
    (hconditional : ∀ ρ, d.G.conditional ρ = conditionalGeometricInterval h₀ hh)
    (hforward : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ h₀ hh) :
    (∀ ρ, AffineResidual.CellRegularity (d.G.conditional ρ) m
      ((curvesWithSmoothBranches d).conditionalMean d.G U 0 d.r j ρ)
      ((withConditionalForwardCellBudget d D).conditional j ρ)) ∧
    (∀ (ρ : d.G.Kernel) (a : Fin m),
      AffineResidual.CellRegularity (d.G.forward ρ) m
        ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j ρ (d.G.angleNode a))
        ((withConditionalForwardCellBudget d D).forward j ρ a)) ∧
    (∀ ρ, (withConditionalForwardCellBudget d D).conditionalError d.G d.r j ρ ≤
      2^(m+1)*conditionalEnd*d.ell*d.r^2*d.G.variance ρ*
        Real.sqrt (Fintype.card ι)*conditionalOrderEnvelope m*h₀^m/(m.factorial:ℝ)) ∧
    (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
      |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
        ((withConditionalForwardCellBudget d D).forward j ρ a)) ≤
      40*2^(m+1)*(m:ℝ)^5*forwardDerivativeBudget d m*h₀^(m-1)/
        (d.G.psi*(m.factorial:ℝ)) ∧
    (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
      |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
        ((withConditionalForwardCellBudget d D).forward j ρ a)) / (d.sigma/2) ≤
      (40*2^(m+1)*(m:ℝ)^5*forwardDerivativeBudget d m*h₀^(m-1)/
        (d.G.psi*(m.factorial:ℝ))) / (d.sigma/2) :=
  ⟨fun ρ => withConditionalForwardCellBudget_conditionalCellRegularity d D U hu j ρ,
    fun ρ a => withConditionalForwardCellBudget_forwardCellRegularity d D U hu j ρ a,
    fun ρ => withConditionalForwardCellBudget_conditionalError_le d D j ρ h₀ hh hhalf (hconditional ρ),
    withConditionalForwardCellBudget_weightedCellBudget_le d D hm h₀ hh hhalf j hback hforward,
    withConditionalForwardCellBudget_velocityForwardContribution_le d D hm h₀ hh hhalf j hback hforward⟩

end AcceleratedLogConcave.Numerics.MeanResidualBridge
