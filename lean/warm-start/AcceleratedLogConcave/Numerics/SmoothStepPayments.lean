import AcceleratedLogConcave.Numerics.SmoothQuadraturePayments

/-! Geometric-mesh payments for the actual explicit smooth receiver budget.
The source powers are exposed exactly, including the forward loss 4*t and the
complete signed kernel inventory. No final row error is an input hypothesis. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SmoothStepPayments
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph AffineGraph.MeanGeometry
open SmoothQuantitativeAssembly ConditionalSmoothing
variable {D m : ℕ}

/-- Natural quadrature powers of the source step, as real powers of resolution. -/
theorem step_power {δ : ℝ} (hδ : 0 < δ) (w : ℝ) (n : ℕ) :
    (δ^w)^n = δ^(w*(n:ℝ)) :=
  (Real.rpow_mul_natCast hδ.le w n).symm

/-- The forward row's precise source exponent; no order or loss is suppressed. -/
theorem forward_power {δ : ℝ} (hδ : 0 < δ) (w t : ℝ) (n : ℕ) :
    (δ^w)^n / δ^(4*t) = δ^(w*(n:ℝ)-4*t) := by
  rw [step_power hδ, Real.rpow_sub hδ]

/-- First-cell lower bound from the actual backward mesh, not an extra premise. -/
theorem first_width (d : Data (Fin D) m) (h₀ : ℝ) (hmesh : MeshConditions d h₀) :
    h₀/4 ≤ d.G.backward.length 0 := by
  rw [hmesh.backward]
  exact actualKernelInterval_firstCell_lower d.G.R_pos d.G.R_le_half
    hmesh.step_pos hmesh.step_upper

/-- Backward value quadrature for the actual proved component. -/
theorem backward_cellBudget_le (d : Data (Fin D) m) (h₀ : ℝ)
    (hmesh : MeshConditions d h₀) (j : Fin m) :
    AffineResidual.cellBudget d.G.backward m ((budget d).backward j) ≤
      2^(m+1)*(backwardEnd d.G.R)*materialBackwardDerivativeBudget d (m-1)*h₀^m /
        (m.factorial:ℝ) := by
  simpa only [sub_zero] using AffineResidual.probability_cellBudget_le d.G.backward
    (by norm_num) d.G.backwardEnd_lt_one m ((budget d).backward j)
    (materialBackwardDerivativeBudget d (m-1)) h₀
    (materialBackwardDerivativeBudget_nonneg d (m-1)) hmesh.step_pos.le
    (cell_bound d h₀ hmesh) (fun _ => le_rfl)

/-- The source h0=delta^w gives exactly the manuscript's wm power. -/
theorem backward_payment (d : Data (Fin D) m) {δ w : ℝ} (hδ : 0 < δ)
    (hmesh : MeshConditions d (δ^w)) (j : Fin m) :
    AffineResidual.cellBudget d.G.backward m ((budget d).backward j) ≤
      (2^(m+1)*(backwardEnd d.G.R)*materialBackwardDerivativeBudget d (m-1) /
        (m.factorial:ℝ)) * δ^(w*(m:ℝ)) := by
  have h := backward_cellBudget_le d (δ^w) hmesh j
  rw [step_power hδ] at h
  exact h.trans_eq (by ring)

/-- Exact paid kernel-value term in the velocity defect. -/
theorem kernel_value_payment (d : Data (Fin D) m) {δ w : ℝ} (hδ : 0 < δ)
    (j : Fin m) :
    (16:ℝ)^m*(budget d).kernel j*(δ^w)^m/(m.factorial:ℝ) =
      ((16:ℝ)^m*materialKernelDerivativeBudget d (m+2)/(m.factorial:ℝ)) *
        δ^(w*(m:ℝ)) := by
  rw [step_power hδ]
  change (16:ℝ)^m * materialKernelDerivativeBudget d (m+2) * _ / _ = _
  ring

/-- The local conditional row is paid with its actual variance, not a global
inverse-variance overestimate. -/
theorem conditional_payment (d : Data (Fin D) m) {δ w : ℝ} (hδ : 0 < δ)
    (hmesh : MeshConditions d (δ^w)) (j : Fin m) (ρ : d.G.Kernel)
    (hc : d.G.conditional ρ = conditionalGeometricInterval (δ^w) hmesh.step_pos) :
    (budget d).conditionalError d.G d.r j ρ ≤
      (2^(m+1)*conditionalEnd*d.ell*d.r^2*d.G.variance ρ*
        Real.sqrt (Fintype.card (Fin D))*conditionalOrderEnvelope m/(m.factorial:ℝ)) *
          δ^(w*(m:ℝ)) := by
  have h := conditionalError_le_explicit_of_component d (budget d) j ρ rfl
    (δ^w) hmesh.step_pos hmesh.step_upper hc
  rw [step_power hδ] at h
  exact h.trans_eq (by ring)

/-- The full weighted forward inventory is charged, with exponent w(m-1)-4t.
The conditional mesh is irrelevant to this particular contribution. -/
theorem forward_payment (d : Data (Fin D) m) {δ w t : ℝ} (hδ : 0 < δ)
    (hmesh : MeshConditions d (δ^w)) (hpsi : d.G.psi = δ^(4*t)) (j : Fin m)
    (hf : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ (δ^w) hmesh.step_pos) :
    (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
      |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
        ((budget d).forward j ρ a)) ≤
      (40*2^(m+1)*(m:ℝ)^5*forwardDerivativeBudget d m/(m.factorial:ℝ)) *
        δ^(w*((m-1:ℕ):ℝ)-4*t) := by
  have h := withForwardCellBudget_weightedCellBudget_le d (budget d) hmesh.order
    (δ^w) hmesh.step_pos hmesh.step_upper j (first_width d (δ^w) hmesh) hf
  change (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
    |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
      ((budget d).forward j ρ a)) ≤ _ at h
  rw [hpsi] at h
  apply h.trans_eq
  rw [← forward_power hδ]
  ring

/-- Exact scaling of the velocity budget by the same physical centering speed. -/
theorem velocityBudget_eq (d : Data (Fin D) m) :
    velocityBudget d = d.G.R *
      Real.sqrt ((D+D:ℕ) * Tensor.AdjointReduction.PhaseBudget.Q auxiliaryConstant
        (5*(m+1)+1)) * SmoothQuadraturePayments.centerSpeed d^(m+1) := by
  have hR := d.G.R_pos.ne'
  have hs := d.hsigma.ne'
  unfold velocityBudget SmoothQuadraturePayments.centerSpeed
  simp only [div_pow, pow_add, pow_mul, pow_one]
  field_simp

/-- Centering-state quadrature carries the advertised (m+1)/3 power once the
actual scalar resolution pays the physical speed. -/
theorem velocity_payment (d : Data (Fin D) m) {δ : ℝ} (hδ : 0 < δ)
    (hspeed : SmoothQuadraturePayments.centerSpeed d ≤ δ^((1:ℝ)/3)) :
    2*(budget d).velocity/(m.factorial:ℝ) ≤
      (2*d.G.R*Real.sqrt ((D+D:ℕ)*Tensor.AdjointReduction.PhaseBudget.Q
        auxiliaryConstant (5*(m+1)+1))/(m.factorial:ℝ))*δ^(((m:ℝ)+1)/3) := by
  have hp := pow_le_pow_left₀ (SmoothQuadraturePayments.centerSpeed_nonneg d) hspeed (m+1)
  rw [step_power hδ] at hp
  have he : (1:ℝ)/3*((m+1:ℕ):ℝ) = ((m:ℝ)+1)/3 := by push_cast; ring
  rw [he] at hp
  change 2*velocityBudget d/(m.factorial:ℝ) ≤ _
  rw [velocityBudget_eq]
  calc
    _ = (2*d.G.R*Real.sqrt ((D+D:ℕ)*Tensor.AdjointReduction.PhaseBudget.Q
      auxiliaryConstant (5*(m+1)+1))/(m.factorial:ℝ))*
        SmoothQuadraturePayments.centerSpeed d^(m+1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by have := d.G.R_pos.le; positivity)

end AcceleratedLogConcave.Numerics.SmoothStepPayments
