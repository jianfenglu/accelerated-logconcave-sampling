import AcceleratedLogConcave.Numerics.CenterMeanPhysicalTransportBudget
import AcceleratedLogConcave.Tensor.OrderedPhysicalKernelHalfBudget

/-! NEW reconstruction; SOURCE ONLY until independent compiler verification.
Closes the literal transport primitive from accepted original-data half budgets.
Does not import the missing primitive assembly or claim full Regularity. -/
noncomputable section
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.Ordered.Graph Tensor.PhysicalKernelBudget
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

/-- Definitional identification of the physical tensor, with all derivative
slots and both terminal matrix slots unchanged. -/
theorem physicalTransportJet_eq_ordered (d : Data (Fin D)) (j : ℕ) (y : E) :
    physicalTransportJet d j y =
      orderedPhysicalKernelJet (positiveVarianceData d) j y := rfl

/-- Original-data phase transport budget, no tensor-bound premise.
The two mixed blocks consume exactly the two physical half budgets. -/
theorem phaseTransportJet_original_data_budget (d : Data (Fin D))
    (hell : d.ell ≠ 0) {c : ℝ} (hc : 128 ≤ c) (j : ℕ) (z : EP)
    (S : Finset (Fin j ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S
      (phaseCoefficientJet (phaseCoefficients d (d.r*d.ell) (d.r*d.ell))
        .transport j z) ≤
      c^(2+j)*((2+j).factorial : ℝ)*
        (Real.sqrt (1-d.b^2))^(-(j : ℝ)) := by
  apply phaseTransportJet_budget_of_physical d (d.r*d.ell) (d.r*d.ell) c
    (Real.sqrt (1-d.b^2))
    (mul_pos d.hr (lt_of_le_of_ne d.hell (Ne.symm hell))) ?_ j z S hS
  intro n y A hA
  rw [physicalTransportJet_eq_ordered]
  exact original_data_orderedPhysicalKernel_halfBudget
    (positiveVarianceData d) d.hsmall hc n y A hA

/-- At zero curvature the normalized transport entries vanish by their literal
inverse-zero definition. This does not assert that the nonzero-scale ODE join
can be invoked with scale zero. -/
theorem phaseTransportEntry_zero_curvature (d : Data (Fin D)) (hell : d.ell = 0)
    (i k : Fin (D+D)) (z : EP) :
    phaseTransportEntry d (d.r*d.ell) i k z = 0 := by
  simp [phaseTransportEntry, hell]

/-- All normalized transport jets vanish at ell=0, including order zero.
This is a statement about the literal inverse-zero primitive environment only. -/
theorem phaseTransportJet_zero_curvature (d : Data (Fin D)) (hell : d.ell = 0)
    (j : ℕ) (z : EP) :
    phaseCoefficientJet (phaseCoefficients d (d.r*d.ell) (d.r*d.ell))
      .transport j z = 0 := by
  ext a
  simp [phaseCoefficientJet, phaseCoefficients, phaseTransportEntry, hell,
    Tensor.ActualCoefficientIntegrability.partialAlong_eq_jet, JetCalculus.jet_const]

/-- Primitive-only all-curvature version; the zero-scale ODE join is NOT used. -/
theorem phaseTransportJet_original_data_budget_all (d : Data (Fin D))
    {c : ℝ} (hc : 128 ≤ c) (j : ℕ) (z : EP)
    (S : Finset (Fin j ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S
      (phaseCoefficientJet (phaseCoefficients d (d.r*d.ell) (d.r*d.ell))
        .transport j z) ≤
      c^(2+j)*((2+j).factorial : ℝ)*
        (Real.sqrt (1-d.b^2))^(-(j : ℝ)) := by
  by_cases hell : d.ell = 0
  · rw [phaseTransportJet_zero_curvature d hell]
    change splitNorm (D+D) S (0 : Coeff (Fin j ⊕ Fin 2) (D+D)) ≤ _
    rw [splitNorm_zero]
    have hc0 : 0 ≤ c := by linarith
    positivity
  · exact phaseTransportJet_original_data_budget d hell hc j z S hS

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource

namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional Tensor Tensor.Ordered.Graph CenterMeanSecondJetSource
variable {D m : ℕ}

/-- Radius is exactly G.R and both normalization scales are exactly r*ell. -/
theorem center_transport_original_data_budget (d : Data (Fin D) m)
    (hell : (kernelData d).ell ≠ 0) {c : ℝ} (hc : 128 ≤ c)
    (j : ℕ) (z : EuclideanSpace ℝ (Fin (D+D)))
    (S : Finset (Fin j ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S
      (phaseCoefficientJet (phaseCoefficients (kernelData d)
        ((kernelData d).r*(kernelData d).ell)
        ((kernelData d).r*(kernelData d).ell)) .transport j z) ≤
      c^(2+j)*((2+j).factorial : ℝ)*d.G.R^(-(j : ℝ)) := by
  have h := phaseTransportJet_original_data_budget (kernelData d) hell hc j z S hS
  simpa only [kernelData, sqrt_backward_variance d] using h

end AcceleratedLogConcave.Numerics.MeanFlowLp
