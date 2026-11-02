import AcceleratedLogConcave.Tensor.ForwardDisplacementBudget
import AcceleratedLogConcave.Numerics.AngleSourceChain

/-! Actual fixed-common-seed angle endpoint adapter.
Only original MeanFlowLp.Data enters. The historical Gaussian Lp receiver is
separate and is not silently claimed as an imported or compiled dependency. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff Classical
namespace AcceleratedLogConcave.Tensor.ForwardFlow
open Conditional ActualCoefficient Numerics.MeanFlowLp
variable {D m : ℕ}

/-- This packages original fields, not desired regularity or jet estimates. -/
def anglePositiveVarianceData (d : Data (Fin D) m) : PositiveVarianceFlowData (Space D) :=
  ⟨d.F,d.hF,d.ell,d.hell,d.hlo,d.hup,d.x,d.r,d.hr,
    Numerics.AffineGraph.backwardEnd d.G.R,d.G.backwardEnd_pos.le,d.G.backwardEnd_lt_one⟩

def angleInitialTime (d : Data (Fin D) m) (k : d.G.Kernel) :
    Icc (0:ℝ) (anglePositiveVarianceData d).b :=
  ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩

/-- Pays the actual forward orientation and the clipping identity at b. -/
theorem angleEndpoint_eq_forwardY (d : Data (Fin D) m) (k : d.G.Kernel) :
    angleEndpoint d k = forwardY (anglePositiveVarianceData d) (angleInitialTime d k)
      (anglePositiveVarianceData d).b := by
  funext y
  exact Numerics.TransportFlowLp.flow_eq (transportData d) d.x _
    ⟨d.G.backwardEnd_pos.le,le_rfl⟩ y

theorem angleEndpoint_eq_forwardProbabilityTransport (d : Data (Fin D) m)
    (k : d.G.Kernel) :
    angleEndpoint d k = forwardProbabilityTransport d.hF d.hell d.hlo d.hup d.x
      d.hr d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one (d.G.rho k) := by
  rw [angleEndpoint_eq_forwardY,forwardY_terminal]
  rfl

/-- Exact original-data supplier for all angle displacement gradient jets.
The dimensions remain only in the coefficient type, never in the scalar bound. -/
theorem meanFlow_angle_physicalDisplacement_budget (d : Data (Fin D) m)
    (k : d.G.Kernel) (j : ℕ) (y : Space D)
    (S : Finset (Fin j ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm D S (physicalDisplacementCoeff (angleEndpoint d k) j y) ≤
      2*(d.r^2*d.ell)*(256:ℝ)^(j+1)*((j+1).factorial : ℝ)*
        d.G.R^((1:ℝ)-((j+1:ℕ):ℝ)) := by
  rw [angleEndpoint_eq_forwardProbabilityTransport]
  have h := original_data_physicalDisplacement_budget
    (anglePositiveVarianceData d) d.hsmall (angleInitialTime d k) j y S hS
  simpa only [anglePositiveVarianceData,angleInitialTime,sqrt_backward_variance d] using h

/-- Finite order receiver with no order-dependent extra assumption. -/
theorem meanFlow_angle_finiteDisplacement_budgets (d : Data (Fin D) m)
    (k : d.G.Kernel) (N : ℕ) :
    ∀ j ≤ N, ∀ (y : Space D) (S : Finset (Fin j ⊕ Fin 2)), NontrivialSplit S →
      splitNorm D S (physicalDisplacementCoeff (angleEndpoint d k) j y) ≤
        2*(d.r^2*d.ell)*(256:ℝ)^(j+1)*((j+1).factorial : ℝ)*
          d.G.R^((1:ℝ)-((j+1:ℕ):ℝ)) := by
  intro j _ y S hS
  exact meanFlow_angle_physicalDisplacement_budget d k j y S hS

/-- Zero curvature is not normalized away: all positive displacement jets vanish. -/
theorem meanFlow_angle_displacement_zero_curvature (d : Data (Fin D) m)
    (hell : d.ell = 0) (k : d.G.Kernel) (j : ℕ) (y : Space D)
    (S : Finset (Fin j ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm D S (physicalDisplacementCoeff (angleEndpoint d k) j y) = 0 := by
  apply le_antisymm _ (splitNorm_nonneg D S _)
  simpa [hell] using meanFlow_angle_physicalDisplacement_budget d k j y S hS
end AcceleratedLogConcave.Tensor.ForwardFlow
