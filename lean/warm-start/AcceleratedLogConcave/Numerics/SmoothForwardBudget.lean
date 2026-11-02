import AcceleratedLogConcave.Numerics.SmoothForwardCell
import AcceleratedLogConcave.Numerics.ProbabilityGeometricMesh

/-! Forward-only composition of the actual fixed-angle Cell supplier with the
published probability mesh bound. The other budget components remain arbitrary.
The per-cell step or exact prescribed-mesh equality is an explicit premise;
no weighted forward sum, partition count or global residual is asserted. -/
noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph
variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- Replace only the forward component by the proved angle-independent envelope. -/
def withForwardCellBudget (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    AffineResidual.Mean.DerivativeBudget d.G :=
  { D with forward := fun _ ρ _ => forwardCellBudget d ρ }

theorem withForwardCellBudget_forward (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    (withForwardCellBudget d D).forward = fun _ ρ _ => forwardCellBudget d ρ := rfl

/-- These six fields are preserved without any positivity or regularity premise. -/
theorem withForwardCellBudget_other_fields (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    (withForwardCellBudget d D).velocity = D.velocity ∧
    (withForwardCellBudget d D).center = D.center ∧
    (withForwardCellBudget d D).backward = D.backward ∧
    (withForwardCellBudget d D).conditional = D.conditional ∧
    (withForwardCellBudget d D).angle = D.angle ∧
    (withForwardCellBudget d D).kernel = D.kernel :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem withForwardCellBudget_cellBudget_eq (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (j : Fin m)
    (ρ : d.G.Kernel) (a : Fin m) :
    AffineResidual.cellBudget (d.G.forward ρ) m ((withForwardCellBudget d D).forward j ρ a) =
      AffineResidual.cellBudget (d.G.forward ρ) m (forwardCellBudget d ρ) := rfl

/-- Exact interval-length factor from the generic published probability bound. -/
theorem withForwardCellBudget_cellBudget_le_of_step (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (j : Fin m)
    (ρ : d.G.Kernel) (a : Fin m) (h₀ : ℝ) (hh : 0 ≤ h₀)
    (hstep : ∀ c, (d.G.forward ρ).length c ≤ 2*h₀*(1-((d.G.forward ρ).right c)^2)) :
    AffineResidual.cellBudget (d.G.forward ρ) m ((withForwardCellBudget d D).forward j ρ a) ≤
      2^(m+1)*(backwardEnd d.G.R-d.G.rho ρ)*forwardDerivativeBudget d m*h₀^m/(m.factorial:ℝ) :=
  AffineResidual.probability_cellBudget_le (d.G.forward ρ) (d.G.rho_mem ρ).1
    d.G.backwardEnd_lt_one m ((withForwardCellBudget d D).forward j ρ a)
    (forwardDerivativeBudget d m) h₀ (forwardDerivativeBudget_nonneg d m) hh hstep
    (fun _ => le_rfl)

/-- The coarser bound uses only 0 ≤ rho and backwardEnd < 1. -/
theorem withForwardCellBudget_cellBudget_le_coarse_of_step (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (j : Fin m)
    (ρ : d.G.Kernel) (a : Fin m) (h₀ : ℝ) (hh : 0 ≤ h₀)
    (hstep : ∀ c, (d.G.forward ρ).length c ≤ 2*h₀*(1-((d.G.forward ρ).right c)^2)) :
    AffineResidual.cellBudget (d.G.forward ρ) m ((withForwardCellBudget d D).forward j ρ a) ≤
      2^(m+1)*forwardDerivativeBudget d m*h₀^m/(m.factorial:ℝ) := by
  refine (withForwardCellBudget_cellBudget_le_of_step d D j ρ a h₀ hh hstep).trans ?_
  have hlen : backwardEnd d.G.R-d.G.rho ρ ≤ 1 := by
    linarith [(d.G.rho_mem ρ).1, d.G.backwardEnd_lt_one]
  have hmul : (2:ℝ)^(m+1)*(backwardEnd d.G.R-d.G.rho ρ) ≤ 2^(m+1)*1 :=
    mul_le_mul_of_nonneg_left hlen (by positivity)
  have hAF := mul_le_mul_of_nonneg_right hmul (forwardDerivativeBudget_nonneg d m)
  have hpow := mul_le_mul_of_nonneg_right hAF (pow_nonneg hh m)
  simpa only [mul_one] using div_le_div_of_nonneg_right hpow (by positivity : 0 ≤ (m.factorial:ℝ))

/-- Consume the existing generic schedule; do not infer it from arbitrary Data. -/
theorem withForwardCellBudget_cellBudget_le_geometric (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (j : Fin m)
    (ρ : d.G.Kernel) (a : Fin m) (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (hmesh : d.G.forward ρ = probabilityGeometricInterval (d.G.rho ρ) (backwardEnd d.G.R)
      h₀ (d.G.rho_mem ρ).2 d.G.backwardEnd_lt_one hh) :
    AffineResidual.cellBudget (d.G.forward ρ) m ((withForwardCellBudget d D).forward j ρ a) ≤
      2^(m+1)*(backwardEnd d.G.R-d.G.rho ρ)*forwardDerivativeBudget d m*h₀^m/(m.factorial:ℝ) := by
  apply withForwardCellBudget_cellBudget_le_of_step d D j ρ a h₀ hh.le
  rw [hmesh]
  exact probabilityGeometricInterval_step _ _ _ (d.G.rho_mem ρ).2
    d.G.backwardEnd_lt_one hh hhalf (d.G.rho_mem ρ).1

theorem withForwardCellBudget_cellBudget_le_coarse_geometric (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (j : Fin m)
    (ρ : d.G.Kernel) (a : Fin m) (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (hmesh : d.G.forward ρ = probabilityGeometricInterval (d.G.rho ρ) (backwardEnd d.G.R)
      h₀ (d.G.rho_mem ρ).2 d.G.backwardEnd_lt_one hh) :
    AffineResidual.cellBudget (d.G.forward ρ) m ((withForwardCellBudget d D).forward j ρ a) ≤
      2^(m+1)*forwardDerivativeBudget d m*h₀^m/(m.factorial:ℝ) := by
  apply withForwardCellBudget_cellBudget_le_coarse_of_step d D j ρ a h₀ hh.le
  rw [hmesh]
  exact probabilityGeometricInterval_step _ _ _ (d.G.rho_mem ρ).2
    d.G.backwardEnd_lt_one hh hhalf (d.G.rho_mem ρ).1

variable [DecidableEq ι]

/-- Any fixed deterministic real angle uses the same updated envelope. The
budget slot a is finite; it does not impose a random-angle independence premise. -/
theorem withForwardCellBudget_cellRegularity (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (a : Fin m) (z : ℝ) :
    AffineResidual.CellRegularity (d.G.forward ρ) m
      ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j ρ z)
      ((withForwardCellBudget d D).forward j ρ a) :=
  smoothBranches_forwardMean_cellRegularity_explicit d U hu j ρ z

/-- The literal forward field of the actual all-fields receiver. -/
theorem withForwardCellBudget_cellRegularity_actual (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (a : Fin m) :
    AffineResidual.CellRegularity (d.G.forward ρ) m
      ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j ρ (d.G.angleNode a))
      ((withForwardCellBudget d D).forward j ρ a) :=
  withForwardCellBudget_cellRegularity d D U hu j ρ a (d.G.angleNode a)

/-- Scoped analytic/numerical join with the literal per-cell step premise. -/
theorem withForwardCellBudget_cellRegularity_and_cellBudget_le_of_step
    (d : MeanFlowLp.Data ι m) (D : AffineResidual.Mean.DerivativeBudget d.G)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (a : Fin m) (z : ℝ) (h₀ : ℝ) (hh : 0 ≤ h₀)
    (hstep : ∀ c, (d.G.forward ρ).length c ≤ 2*h₀*(1-((d.G.forward ρ).right c)^2)) :
    AffineResidual.CellRegularity (d.G.forward ρ) m
      ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j ρ z)
      ((withForwardCellBudget d D).forward j ρ a) ∧
    AffineResidual.cellBudget (d.G.forward ρ) m ((withForwardCellBudget d D).forward j ρ a) ≤
      2^(m+1)*(backwardEnd d.G.R-d.G.rho ρ)*forwardDerivativeBudget d m*h₀^m/(m.factorial:ℝ) :=
  ⟨withForwardCellBudget_cellRegularity d D U hu j ρ a z,
    withForwardCellBudget_cellBudget_le_of_step d D j ρ a h₀ hh hstep⟩

/-- Scoped join on the prescribed mesh. No other Regularity field is certified. -/
theorem withForwardCellBudget_cellRegularity_and_cellBudget_le_geometric
    (d : MeanFlowLp.Data ι m) (D : AffineResidual.Mean.DerivativeBudget d.G)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (a : Fin m) (z : ℝ)
    (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (hmesh : d.G.forward ρ = probabilityGeometricInterval (d.G.rho ρ) (backwardEnd d.G.R)
      h₀ (d.G.rho_mem ρ).2 d.G.backwardEnd_lt_one hh) :
    AffineResidual.CellRegularity (d.G.forward ρ) m
      ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j ρ z)
      ((withForwardCellBudget d D).forward j ρ a) ∧
    AffineResidual.cellBudget (d.G.forward ρ) m ((withForwardCellBudget d D).forward j ρ a) ≤
      2^(m+1)*(backwardEnd d.G.R-d.G.rho ρ)*forwardDerivativeBudget d m*h₀^m/(m.factorial:ℝ) :=
  ⟨withForwardCellBudget_cellRegularity d D U hu j ρ a z,
    withForwardCellBudget_cellBudget_le_geometric d D j ρ a h₀ hh hhalf hmesh⟩

end AcceleratedLogConcave.Numerics.MeanResidualBridge
