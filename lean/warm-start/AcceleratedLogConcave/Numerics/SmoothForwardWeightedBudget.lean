import AcceleratedLogConcave.Numerics.SmoothForwardBudget
import AcceleratedLogConcave.Numerics.ForwardMeshBudget

/-! Actual weighted forward AF budget. The historical finite-sum theorem is
instantiated with the proved forward component; all other budget fields remain
arbitrary. The forward contribution in velocityError is divided by sigma/2.
No analytic angle bound, full velocity budget or global residual is supplied. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph
variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- Literal kernel/angle weighted forward sum, with the original geometric and
first-width premises retained. The AF envelope is proved, not assumed. -/
theorem withForwardCellBudget_weightedCellBudget_le (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (hm : 2 ≤ m)
    (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2) (j : Fin m)
    (hback : h₀/4 ≤ d.G.backward.length 0)
    (hforward : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ h₀ hh) :
    (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
      |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
        ((withForwardCellBudget d D).forward j ρ a)) ≤
      40*2^(m+1)*(m:ℝ)^5*forwardDerivativeBudget d m*h₀^(m-1)/
        (d.G.psi*(m.factorial:ℝ)) :=
  AffineResidual.Mean.DerivativeBudget.forward_weighted_cellBudget_le
    d.G (withForwardCellBudget d D) hm h₀ (forwardDerivativeBudget d m)
    hh hhalf (forwardDerivativeBudget_nonneg d m) j hback hforward (fun _ _ _ => le_rfl)

/-- Exact receiver split. Kernel and angle budgets are the original unpaid
fields; the forward term has denominator sigma/2, not multiplier sigma/2. -/
theorem withForwardCellBudget_velocityError_eq (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (h₀ : ℝ) (j : Fin m) :
    (withForwardCellBudget d D).velocityError d.G d.r d.sigma h₀ j =
      ((16:ℝ)^m * D.kernel j * h₀^m/(m.factorial:ℝ) +
        ∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| *
          ((m:ℝ)^3*d.G.psi^(m-1)*D.angle j ρ/(m.factorial:ℝ))) / (d.r*(d.sigma/2)) +
      (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
        |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
          ((withForwardCellBudget d D).forward j ρ a)) / (d.sigma/2) := rfl

/-- Normalize only the forward contribution. Positivity of sigma is already
part of original Data; no extra sign assumption is introduced. -/
theorem withForwardCellBudget_velocityForwardContribution_le (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (hm : 2 ≤ m)
    (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2) (j : Fin m)
    (hback : h₀/4 ≤ d.G.backward.length 0)
    (hforward : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ h₀ hh) :
    (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
      |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
        ((withForwardCellBudget d D).forward j ρ a)) / (d.sigma/2) ≤
      (40*2^(m+1)*(m:ℝ)^5*forwardDerivativeBudget d m*h₀^(m-1)/
        (d.G.psi*(m.factorial:ℝ))) / (d.sigma/2) :=
  div_le_div_of_nonneg_right
    (withForwardCellBudget_weightedCellBudget_le d D hm h₀ hh hhalf j hback hforward)
    (half_pos d.hsigma).le

/-- A partial receiver bound with the kernel/angle terms left exactly explicit.
This does not pay those terms or assert a complete velocity-error estimate. -/
theorem withForwardCellBudget_velocityError_le_with_unpaid_terms (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (hm : 2 ≤ m)
    (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2) (j : Fin m)
    (hback : h₀/4 ≤ d.G.backward.length 0)
    (hforward : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ h₀ hh) :
    (withForwardCellBudget d D).velocityError d.G d.r d.sigma h₀ j ≤
      ((16:ℝ)^m * D.kernel j * h₀^m/(m.factorial:ℝ) +
        ∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| *
          ((m:ℝ)^3*d.G.psi^(m-1)*D.angle j ρ/(m.factorial:ℝ))) / (d.r*(d.sigma/2)) +
      (40*2^(m+1)*(m:ℝ)^5*forwardDerivativeBudget d m*h₀^(m-1)/
        (d.G.psi*(m.factorial:ℝ))) / (d.sigma/2) := by
  rw [withForwardCellBudget_velocityError_eq]
  exact add_le_add le_rfl
    (withForwardCellBudget_velocityForwardContribution_le d D hm h₀ hh hhalf j hback hforward)

variable [DecidableEq ι]

/-- Actual all-fields forward Cell family at every finite angle node, joined
to the literal weighted sum. No full Regularity premise or conclusion occurs. -/
theorem withForwardCellBudget_forward_family_and_weightedCellBudget_le
    (d : MeanFlowLp.Data ι m) (D : AffineResidual.Mean.DerivativeBudget d.G)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (hm : 2 ≤ m) (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2) (j : Fin m)
    (hback : h₀/4 ≤ d.G.backward.length 0)
    (hforward : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ h₀ hh) :
    (∀ (ρ : d.G.Kernel) (a : Fin m),
      AffineResidual.CellRegularity (d.G.forward ρ) m
        ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j ρ (d.G.angleNode a))
        ((withForwardCellBudget d D).forward j ρ a)) ∧
    (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
      |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
        ((withForwardCellBudget d D).forward j ρ a)) ≤
      40*2^(m+1)*(m:ℝ)^5*forwardDerivativeBudget d m*h₀^(m-1)/
        (d.G.psi*(m.factorial:ℝ)) :=
  ⟨fun ρ a => withForwardCellBudget_cellRegularity_actual d D U hu j ρ a,
    withForwardCellBudget_weightedCellBudget_le d D hm h₀ hh hhalf j hback hforward⟩

end AcceleratedLogConcave.Numerics.MeanResidualBridge
