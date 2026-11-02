import AcceleratedLogConcave.Numerics.SmoothConditionalForwardBudget

/-! Partial rotation and row envelopes for the paired conditional/forward budget.
The velocity, center, backward, kernel and angle fields remain explicit and may
be negative in the numerical statements. Only the final actual-graph corollary
uses full Regularity, through the existing meanResidual theorem. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry ConditionalSmoothing
variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- Kernel and angle terms are unpaid. The paid forward term divides by sigma/2. -/
def partialVelocityEnvelope (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (h₀ : ℝ) (b : Fin m) : ℝ :=
  ((16:ℝ)^m*D.kernel b*h₀^m/(m.factorial:ℝ) +
    ∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| *
      ((m:ℝ)^3*d.G.psi^(m-1)*D.angle b ρ/(m.factorial:ℝ))) / (d.r*(d.sigma/2)) +
  (40*2^(m+1)*(m:ℝ)^5*forwardDerivativeBudget d m*h₀^(m-1)/
    (d.G.psi*(m.factorial:ℝ))) / (d.sigma/2)

def partialPositionEnvelope (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (h₀ a : ℝ) : ℝ :=
  2*D.velocity/(m.factorial:ℝ) +
    ∑ b : Fin m, |centerRow a b| * partialVelocityEnvelope d D h₀ b

def partialBackwardEnvelope (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (h₀ : ℝ) (b : Fin m) : ℝ :=
  partialPositionEnvelope d D h₀ (centerNode b) +
    d.r * AffineResidual.cellBudget d.G.backward m (D.backward b)

/-- The proved conditional error scale, with positive variance in the numerator. -/
def partialConditionalEnvelope (d : MeanFlowLp.Data ι m) (h₀ : ℝ) (ρ : d.G.Kernel) : ℝ :=
  2^(m+1)*conditionalEnd*d.ell*d.r^2*d.G.variance ρ*
    Real.sqrt (Fintype.card ι)*conditionalOrderEnvelope m*h₀^m/(m.factorial:ℝ)

/-- Keep the exact forward interval-length factor before any coarse estimate. -/
def partialForwardCellEnvelope (d : MeanFlowLp.Data ι m) (h₀ : ℝ) (ρ : d.G.Kernel) : ℝ :=
  2^(m+1)*(backwardEnd d.G.R-d.G.rho ρ)*forwardDerivativeBudget d m*h₀^m/(m.factorial:ℝ)

def partialRotationEnvelope (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (h₀ : ℝ)
    (b : Fin m) (ρ : d.G.Kernel) (z : ℝ) : ℝ :=
  |1-(d.G.rotationScale ρ)^2*(1-Real.cos (z/d.G.rotationScale ρ))| *
    partialBackwardEnvelope d D h₀ b +
  |d.G.rho ρ * Real.sqrt (d.G.variance ρ) / (conditionalEnd*(1+(d.G.rho ρ)^2)) *
      (1-Real.cos (z/d.G.rotationScale ρ))| * partialConditionalEnvelope d h₀ ρ +
  |d.G.rotationScale ρ * Real.sin (z/d.G.rotationScale ρ)| *
    (2*D.center/((d.sigma/2)*(m.factorial:ℝ)))

/-- Literal physical row scales, with only conditional/forward budgets paid. -/
def partialRowEnvelope (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (h₀ : ℝ) : d.G.MeanNode → ℝ
  | .inl _ => 0
  | .inr (.inl b) => d.r * backwardEnd d.G.R * partialPositionEnvelope d D h₀ (centerNode b)
  | .inr (.inr (.inl (b,j))) =>
      d.r * d.G.backward.location m j * partialBackwardEnvelope d D h₀ b
  | .inr (.inr (.inr (.inl (b,⟨ρ,j⟩)))) =>
      d.r * d.G.rho ρ * partialBackwardEnvelope d D h₀ b +
        d.r * Real.sqrt (d.G.variance ρ) * (d.G.conditional ρ).location m j *
          partialConditionalEnvelope d h₀ ρ
  | .inr (.inr (.inr (.inr (b,⟨ρ,z,j⟩)))) =>
      d.r * (d.G.forward ρ).location m j *
        (partialRotationEnvelope d D h₀ b ρ (d.G.angleNode z) +
          d.r * partialForwardCellEnvelope d h₀ ρ)

variable (d : MeanFlowLp.Data ι m) (D : AffineResidual.Mean.DerivativeBudget d.G)
variable (hm : 2 ≤ m) (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
variable (hback : h₀/4 ≤ d.G.backward.length 0)
variable (hforward : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ h₀ hh)
include hm hh hhalf hback hforward

theorem paired_velocityError_le_partial (b : Fin m) :
    (withConditionalForwardCellBudget d D).velocityError d.G d.r d.sigma h₀ b ≤
      partialVelocityEnvelope d D h₀ b :=
  withForwardCellBudget_velocityError_le_with_unpaid_terms d D hm h₀ hh hhalf b hback hforward

theorem paired_positionError_le_partial (a : ℝ) :
    (withConditionalForwardCellBudget d D).positionError d.G d.r d.sigma h₀ a ≤
      partialPositionEnvelope d D h₀ a := by
  apply add_le_add le_rfl
  exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
    (paired_velocityError_le_partial d D hm h₀ hh hhalf hback hforward b) (abs_nonneg _)

theorem paired_backwardError_le_partial (b : Fin m) :
    (withConditionalForwardCellBudget d D).backwardError d.G d.r d.sigma h₀ b ≤
      partialBackwardEnvelope d D h₀ b :=
  add_le_add (paired_positionError_le_partial d D hm h₀ hh hhalf hback hforward _) le_rfl

omit hm hback hforward in
/-- This estimate needs only the local prescribed forward mesh, not first width. -/
theorem paired_forwardCellBudget_le_partial (b : Fin m) (ρ : d.G.Kernel) (z : Fin m)
    (hmesh : d.G.forward ρ = forwardGeometricInterval d.G ρ h₀ hh) :
    AffineResidual.cellBudget (d.G.forward ρ) m
      ((withConditionalForwardCellBudget d D).forward b ρ z) ≤ partialForwardCellEnvelope d h₀ ρ :=
  withForwardCellBudget_cellBudget_le_geometric d D b ρ z h₀ hh hhalf hmesh

variable (hconditional : ∀ ρ, d.G.conditional ρ = conditionalGeometricInterval h₀ hh)
include hconditional

/-- A pointwise numerical bound, valid even when unpaid budget fields are negative. -/
theorem paired_rotationError_le_partial (b : Fin m) (ρ : d.G.Kernel) (z : ℝ) :
    (withConditionalForwardCellBudget d D).rotationError d.G d.r d.sigma h₀ b ρ z ≤
      partialRotationEnvelope d D h₀ b ρ z := by
  apply add_le_add _ le_rfl
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (paired_backwardError_le_partial d D hm h₀ hh hhalf hback hforward b) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left
      (withConditionalForwardCellBudget_conditionalError_le d D b ρ h₀ hh hhalf
        (hconditional ρ)) (abs_nonneg _))

/-- Pointwise row comparison; no norm monotonicity or unpaid positivity is used. -/
theorem paired_rowError_le_partial (i : d.G.MeanNode) :
    (withConditionalForwardCellBudget d D).rowError d.G d.r d.sigma h₀ i ≤
      partialRowEnvelope d D h₀ i := by
  rcases i with ⟨⟩ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left
      (paired_positionError_le_partial d D hm h₀ hh hhalf hback hforward _)
      (mul_nonneg d.hr.le d.G.backwardEnd_pos.le)
  · exact mul_le_mul_of_nonneg_left
      (paired_backwardError_le_partial d D hm h₀ hh hhalf hback hforward b)
      (mul_nonneg d.hr.le (d.G.backward.location_mem_interval m j).1.le)
  · exact add_le_add
      (mul_le_mul_of_nonneg_left
        (paired_backwardError_le_partial d D hm h₀ hh hhalf hback hforward b)
        (mul_nonneg d.hr.le (d.G.rho_mem ρ).1))
      (mul_le_mul_of_nonneg_left
        (withConditionalForwardCellBudget_conditionalError_le d D b ρ h₀ hh hhalf (hconditional ρ))
        (mul_nonneg (mul_nonneg d.hr.le (Real.sqrt_nonneg _))
          ((d.G.conditional ρ).location_mem_interval m j).1.le))
  · exact mul_le_mul_of_nonneg_left
      (add_le_add
        (paired_rotationError_le_partial d D hm h₀ hh hhalf hback hforward hconditional b ρ _)
        (mul_le_mul_of_nonneg_left
          (paired_forwardCellBudget_le_partial d D h₀ hh hhalf b ρ z (hforward ρ)) d.hr.le))
      (mul_nonneg d.hr.le ((d.G.rho_mem ρ).1.trans
        ((d.G.forward ρ).location_mem_interval m j).1.le))

variable [DecidableEq ι]

/-- Existing meanResidual followed by the new pointwise envelope. Full Regularity,
the backward step and the open slab are explicit unpaid premises. The reference
is the original actual common-seed reference, via smoothBranches_reference_eq. -/
theorem actualGraph_residual_le_partialRow
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (l v : ℝ) (hl : l < 0) (hv : backwardEnd d.G.R < v)
    (hgeom : ∀ c, d.G.backward.length c ≤ 2*h₀*(1-(d.G.backward.right c)^2))
    (reg : AffineResidual.Mean.Regularity d.G (curvesWithSmoothBranches d)
      U 0 d.r l v (withConditionalForwardCellBudget d D)) (i : d.G.MeanNode) :
    ‖(d.G.graph d.r d.sigma 0 (initialPosition d) (initialScore d) (initialNoise d)).step U
        ((curves d).reference d.G 0 d.r) i - (curves d).reference d.G 0 d.r i‖ ≤
      partialRowEnvelope d D h₀ i := by
  have h := AffineResidual.Mean.meanResidual d.G hm d.r d.sigma h₀ l v d.hr d.hsigma
    hh.le hl hv hgeom U 0 (initialPosition d) (initialScore d) (initialNoise d)
    (curvesWithSmoothBranches d) (withConditionalForwardCellBudget d D)
    (smoothBranches_equations d U hu) reg i
  rw [smoothBranches_reference_eq] at h
  exact h.trans (paired_rowError_le_partial d D hm h₀ hh hhalf hback hforward hconditional i)

end AcceleratedLogConcave.Numerics.MeanResidualBridge
