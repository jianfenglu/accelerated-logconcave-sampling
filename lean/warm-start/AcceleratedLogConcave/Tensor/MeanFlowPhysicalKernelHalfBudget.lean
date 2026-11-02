import AcceleratedLogConcave.Tensor.PhysicalKernelHalfBudget
import AcceleratedLogConcave.Numerics.MeanFlowLp

/-! NEW original-data adapter, not recovered historical text.
This file uses only the closed original-data kernel budget and accepted
MeanFlowLp definitions. It does not import the incomplete historical phase chain.
-/
noncomputable section
set_option autoImplicit false
open scoped Classical
namespace AcceleratedLogConcave.Tensor.PhysicalKernelBudget
open Conditional
variable {D m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

/-- Copy only the existing original fields. Smallness remains the existing
separate proof d.hsmall and no regularity or desired bound is packaged here. -/
def positiveVarianceData (d : Numerics.KernelFlowLp.Data (Fin D)) :
    PositiveVarianceFlowData E :=
  ⟨d.F, d.hF, d.ell, d.hell, d.hlo, d.hup, d.x, d.r, d.hr, d.b, d.hb, d.hb1⟩

/-- Literal equality with the original transported Stein kernel transpose. -/
theorem actualK_positiveVarianceData (d : Numerics.KernelFlowLp.Data (Fin D)) :
    QuantitativeKernel.actualK (positiveVarianceData d) =
      transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup
        d.x d.hr d.hb d.hb1 := rfl

/-- Every physical spatial order for the actual existing KernelFlowLp.Data. -/
theorem kernelFlow_physical_halfBudget (d : Numerics.KernelFlowLp.Data (Fin D))
    {c : ℝ} (hc : 128 ≤ c) (n : ℕ) (y : E)
    (S : Finset (Fin n ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm D S (physicalOperatorJetCoeff n
      (transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup
        d.x d.hr d.hb d.hb1) y) ≤
      (d.r*d.ell)*(c^(2+n)*((2+n).factorial : ℝ)*
        (Real.sqrt (1-d.b^2))^(-(n : ℝ)))/2 :=
  original_data_physicalKernel_halfBudget (positiveVarianceData d) d.hsmall hc n y S hS

/-- The physical radius is exactly G.R, not a new or smaller radius. -/
theorem meanFlow_physical_halfBudget (d : Numerics.MeanFlowLp.Data (Fin D) m)
    {c : ℝ} (hc : 128 ≤ c) (n : ℕ) (y : E)
    (S : Finset (Fin n ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm D S (physicalOperatorJetCoeff n
      (transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup d.x d.hr
        d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one) y) ≤
      (d.r*d.ell)*(c^(2+n)*((2+n).factorial : ℝ)*d.G.R^(-(n : ℝ)))/2 := by
  have h := kernelFlow_physical_halfBudget (Numerics.MeanFlowLp.kernelData d) hc n y S hS
  simpa only [Numerics.MeanFlowLp.kernelData,
    Numerics.MeanFlowLp.sqrt_backward_variance d] using h

/-- A finite-order physical primitive supplier for the actual common-seed data.
Its premises contain neither the target tensor bound nor any moment estimate. -/
theorem meanFlow_physical_finiteHalfBudgets
    (d : Numerics.MeanFlowLp.Data (Fin D) m) {c : ℝ} (hc : 128 ≤ c) (N : ℕ) :
    ∀ n ≤ N, ∀ (y : E) (S : Finset (Fin n ⊕ Fin 2)), NontrivialSplit S →
      splitNorm D S (physicalOperatorJetCoeff n
        (transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup d.x d.hr
          d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one) y) ≤
        (d.r*d.ell)*(c^(2+n)*((2+n).factorial : ℝ)*d.G.R^(-(n : ℝ)))/2 := by
  intro n _ y S hS
  exact meanFlow_physical_halfBudget d hc n y S hS

/-- Order zero has the expected beta*c² normalization, with no radius factor. -/
theorem meanFlow_physical_zero_halfBudget
    (d : Numerics.MeanFlowLp.Data (Fin D) m) {c : ℝ} (hc : 128 ≤ c)
    (y : E) (S : Finset (Fin 0 ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm D S (physicalOperatorJetCoeff 0
      (transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup d.x d.hr
        d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one) y) ≤ (d.r*d.ell)*c^2 := by
  have h := meanFlow_physical_halfBudget d hc 0 y S hS
  norm_num at h ⊢
  nlinarith

end AcceleratedLogConcave.Tensor.PhysicalKernelBudget
