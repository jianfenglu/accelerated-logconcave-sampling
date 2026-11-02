import AcceleratedLogConcave.Numerics.SmoothConditionalAllReceiver
import AcceleratedLogConcave.Numerics.ConditionalGeometricMesh

/-! Conditional-only composition of the actual all-fields cell supplier with
the prescribed geometric mesh estimate. The mesh equality and step hypotheses
remain explicit. Updating this one budget field certifies no other branch. -/
noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph ConditionalSmoothing
variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- Replace only the conditional component of an otherwise arbitrary budget. -/
def withConditionalCellBudget (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    AffineResidual.Mean.DerivativeBudget d.G :=
  { D with conditional := fun _ ρ => conditionalCellBudget d ρ }

theorem withConditionalCellBudget_conditional (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    (withConditionalCellBudget d D).conditional = fun _ ρ => conditionalCellBudget d ρ := rfl

/-- No positivity or regularity of the other six components is required. -/
theorem withConditionalCellBudget_other_fields (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) :
    (withConditionalCellBudget d D).velocity = D.velocity ∧
    (withConditionalCellBudget d D).center = D.center ∧
    (withConditionalCellBudget d D).backward = D.backward ∧
    (withConditionalCellBudget d D).forward = D.forward ∧
    (withConditionalCellBudget d D).angle = D.angle ∧
    (withConditionalCellBudget d D).kernel = D.kernel :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The exact local-radius factor before any mesh estimate. -/
theorem withConditionalCellBudget_conditionalError_eq (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (j : Fin m) (ρ : d.G.Kernel) :
    (withConditionalCellBudget d D).conditionalError d.G d.r j ρ =
      (d.r * Real.sqrt (d.G.variance ρ)) *
        AffineResidual.cellBudget (d.G.conditional ρ) m (conditionalCellBudget d ρ) := by
  rw [AffineResidual.Mean.DerivativeBudget.conditionalError_eq_localRadius]
  rfl

/-- An exact component identity suffices; the desired error estimate is proved,
not assumed. Neither a primitive nor full Regularity enters this numerical fact. -/
theorem conditionalError_le_explicit_of_component (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (j : Fin m) (ρ : d.G.Kernel)
    (hcomponent : D.conditional j ρ = conditionalCellBudget d ρ)
    (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (hmesh : d.G.conditional ρ = conditionalGeometricInterval h₀ hh) :
    D.conditionalError d.G d.r j ρ ≤
      2^(m+1)*conditionalEnd*d.ell*d.r^2*d.G.variance ρ*
        Real.sqrt (Fintype.card ι)*conditionalOrderEnvelope m*h₀^m/(m.factorial:ℝ) := by
  apply conditionalGeometricInterval_conditionalError_le d.G D d.r d.ell
    (conditionalOrderEnvelope m) h₀ (Fintype.card ι) d.hr.le d.hell
    (conditionalOrderEnvelope_nonneg m) hh hhalf j ρ hmesh
  intro c
  rw [hcomponent]
  exact le_rfl

theorem withConditionalCellBudget_conditionalError_le (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G) (j : Fin m) (ρ : d.G.Kernel)
    (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (hmesh : d.G.conditional ρ = conditionalGeometricInterval h₀ hh) :
    (withConditionalCellBudget d D).conditionalError d.G d.r j ρ ≤
      2^(m+1)*conditionalEnd*d.ell*d.r^2*d.G.variance ρ*
        Real.sqrt (Fintype.card ι)*conditionalOrderEnvelope m*h₀^m/(m.factorial:ℝ) :=
  conditionalError_le_explicit_of_component d (withConditionalCellBudget d D)
    j ρ rfl h₀ hh hhalf hmesh

variable [DecidableEq ι]

/-- The actual all-fields conditional cell property for the updated component. -/
theorem withConditionalCellBudget_cellRegularity (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) :
    AffineResidual.CellRegularity (d.G.conditional ρ) m
      ((curvesWithSmoothBranches d).conditionalMean d.G U 0 d.r j ρ)
      ((withConditionalCellBudget d D).conditional j ρ) :=
  smoothBranches_conditionalMean_cellRegularity_explicit d U hu j ρ

/-- Scoped analytic and numerical conclusion. The prescribed-mesh identity is
an independent premise, not a consequence of original Data. -/
theorem withConditionalCellBudget_cellRegularity_and_error_le (d : MeanFlowLp.Data ι m)
    (D : AffineResidual.Mean.DerivativeBudget d.G)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (ρ : d.G.Kernel) (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (hmesh : d.G.conditional ρ = conditionalGeometricInterval h₀ hh) :
    AffineResidual.CellRegularity (d.G.conditional ρ) m
      ((curvesWithSmoothBranches d).conditionalMean d.G U 0 d.r j ρ)
      ((withConditionalCellBudget d D).conditional j ρ) ∧
    (withConditionalCellBudget d D).conditionalError d.G d.r j ρ ≤
      2^(m+1)*conditionalEnd*d.ell*d.r^2*d.G.variance ρ*
        Real.sqrt (Fintype.card ι)*conditionalOrderEnvelope m*h₀^m/(m.factorial:ℝ) :=
  ⟨withConditionalCellBudget_cellRegularity d D U hu j ρ,
    withConditionalCellBudget_conditionalError_le d D j ρ h₀ hh hhalf hmesh⟩

end AcceleratedLogConcave.Numerics.MeanResidualBridge
