import AcceleratedLogConcave.Tensor.MeanFlowAngleDisplacementBudget
import AcceleratedLogConcave.Analysis.AnglePhysicalBudgets

/-! New integration of the accepted actual forward supplier with the recovered physical receiver. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.ActualCoefficient Tensor.ForwardFlow
open Tensor.AdjointReduction Tensor.CoordinateReduction Tensor.Ordered.Graph
variable {D m : ℕ}

private theorem actual_basis_eq_coordinate (i : Fin D) :
    basis D i = coordinateDirection D i := by
  simp [basis,EuclideanSpace.basisFun_apply,coordinateDirection,EuclideanSpace.single]

/-- Equality with the literal pre-existing consumer tensor, not a replacement. -/
theorem physicalDisplacementJet_eq_actual_coeff (T : Space D → Space D)
    (hT : ContDiff ℝ ∞ T) (j : ℕ) (y : Space D) :
    physicalDisplacementJet T j y = physicalDisplacementCoeff T j y := by
  rw [physicalDisplacementCoeff_eq_ordered T hT]
  have he : (basis D : Fin D → Space D) = coordinateDirection D := funext actual_basis_eq_coordinate
  ext a
  simp only [physicalDisplacementJet,he]

/-- Discharges the historical hphysical premise from actual original data. -/
theorem actual_angle_physicalDisplacement_splits
    (d : Numerics.MeanFlowLp.Data (Fin D) m) (k : d.G.Kernel)
    (j : ℕ) (y : Space D) (S : Finset (Fin j ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm D S (physicalDisplacementJet (Numerics.MeanFlowLp.angleEndpoint d k) j y) ≤
      2*(d.r^2*d.ell)*(256:ℝ)^(j+1)*((j+1).factorial : ℝ)*
        d.G.R^((1:ℝ)-((j+1:ℕ):ℝ)) := by
  rw [physicalDisplacementJet_eq_actual_coeff _
    (Numerics.MeanFlowLp.contDiff_angleEndpoint d k)]
  exact meanFlow_angle_physicalDisplacement_budget d k j y S hS

/-- Only positivity needed for normalization is retained explicitly.
The ell=0 branch is separately zero-safe in the original-data supplier. -/
theorem actual_anglePrimitiveBudgets
    (d : Numerics.MeanFlowLp.Data (Fin D) m) (k : d.G.Kernel)
    (hell : 0 < d.ell) (q : ℝ) (hq : 0 < q) (M : Space D) :
    PhasePrimitiveBudgets
      (angleCoefficients (Numerics.MeanFlowLp.angleEndpoint d k) M q
        (2*(d.r^2*d.ell)*d.G.R)) Kinetic.Reheating.gaussianPotential 256 (radius d.G.R q) := by
  apply anglePrimitiveBudgets_of_physicalSplits _
    (Numerics.MeanFlowLp.contDiff_angleEndpoint d k) d.G.R q (d.r^2*d.ell)
    d.G.R_pos hq (mul_pos (sq_pos_of_pos d.hr) hell)
  · exact actual_angle_physicalDisplacement_splits d k
end AcceleratedLogConcave.Analysis.AnglePhase
