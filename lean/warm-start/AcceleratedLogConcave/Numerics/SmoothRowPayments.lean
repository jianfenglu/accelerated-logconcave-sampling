import AcceleratedLogConcave.Numerics.SmoothAnglePayment
import AcceleratedLogConcave.Numerics.SmoothPartialRowBudget

/-! Physical row coefficients for the actual seven-component budget. These
retain all node-dependent transport and rotation factors. No dimension-uniform
majorant for their inventory norm is asserted here. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SmoothRowPayments
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph AffineGraph.MeanGeometry
open SmoothQuantitativeAssembly SmoothQuadraturePayments SmoothStepPayments
open ConditionalSmoothing
variable {D m : ℕ}

def stateCoefficient (d : Data (Fin D) m) : ℝ :=
  2*d.G.R*Real.sqrt ((D+D:ℕ)*Tensor.AdjointReduction.PhaseBudget.Q
    auxiliaryConstant (5*(m+1)+1))/(m.factorial:ℝ)
def positionCoefficient (d : Data (Fin D) m) (a : ℝ) : ℝ :=
  stateCoefficient d + ∑ b : Fin m, |centerRow a b| *SmoothAnglePayment.velocityCoefficient d
def backwardCoefficient (d : Data (Fin D) m) (j : Fin m) : ℝ :=
  positionCoefficient d (centerNode j) + d.r*
    (2^(m+1)*backwardEnd d.G.R*materialBackwardDerivativeBudget d (m-1)/(m.factorial:ℝ))
def conditionalCoefficient (d : Data (Fin D) m) (ρ : d.G.Kernel) : ℝ :=
  2^(m+1)*conditionalEnd*d.ell*d.r^2*d.G.variance ρ*
    Real.sqrt (Fintype.card (Fin D))*conditionalOrderEnvelope m/(m.factorial:ℝ)
def forwardCoefficient (d : Data (Fin D) m) (ρ : d.G.Kernel) : ℝ :=
  2^(m+1)*(backwardEnd d.G.R-d.G.rho ρ)*forwardDerivativeBudget d m/(m.factorial:ℝ)
def scoreCoefficient (d : Data (Fin D) m) : ℝ :=
  2*centerCoefficient d/((d.sigma/2)*(m.factorial:ℝ))
def rotationCoefficient (d : Data (Fin D) m) (j : Fin m) (ρ : d.G.Kernel) (z : ℝ) : ℝ :=
  |1-(d.G.rotationScale ρ)^2*(1-Real.cos (z/d.G.rotationScale ρ))| *
    backwardCoefficient d j +
  |d.G.rho ρ * Real.sqrt (d.G.variance ρ) / (conditionalEnd*(1+(d.G.rho ρ)^2)) *
    (1-Real.cos (z/d.G.rotationScale ρ))| * conditionalCoefficient d ρ +
  |d.G.rotationScale ρ * Real.sin (z/d.G.rotationScale ρ)| * scoreCoefficient d

def rowCoefficient (d : Data (Fin D) m) : d.G.MeanNode → ℝ
  | .inl _ => 0
  | .inr (.inl b) => d.r*backwardEnd d.G.R*positionCoefficient d (centerNode b)
  | .inr (.inr (.inl (b,j))) =>
      d.r*d.G.backward.location m j*backwardCoefficient d b
  | .inr (.inr (.inr (.inl (b,⟨ρ,j⟩)))) =>
      d.r*d.G.rho ρ*backwardCoefficient d b +
      d.r*Real.sqrt (d.G.variance ρ)*(d.G.conditional ρ).location m j*conditionalCoefficient d ρ
  | .inr (.inr (.inr (.inr (b,⟨ρ,z,j⟩)))) =>
      d.r*(d.G.forward ρ).location m j*
        (rotationCoefficient d b ρ (d.G.angleNode z)+d.r*forwardCoefficient d ρ)

def exponent (m : ℕ) (w t : ℝ) : ℝ := w*((m-1:ℕ):ℝ)-4*t

theorem power_wm {δ w t : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hw : 0 ≤ w) (ht : 0 ≤ t) : δ^(w*(m:ℝ)) ≤ δ^(exponent m w t) := by
  apply Real.rpow_le_rpow_of_exponent_ge hδ hδone
  unfold exponent
  have hm : ((m-1:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.sub_le m 1
  nlinarith

theorem power_center {δ w t : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hw : 0 ≤ w) (hwt : w ≤ t) (ht : t ≤ (1:ℝ)/60) :
    δ^((m:ℝ)/3) ≤ δ^(exponent m w t) := by
  apply Real.rpow_le_rpow_of_exponent_ge hδ hδone
  unfold exponent
  have hm : ((m-1:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.sub_le m 1
  have hn : (0:ℝ) ≤ ((m-1:ℕ):ℝ) := Nat.cast_nonneg _
  nlinarith

theorem power_state {δ w t : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hw : 0 ≤ w) (hwt : w ≤ t) (ht : t ≤ (1:ℝ)/60) :
    δ^(((m:ℝ)+1)/3) ≤ δ^(exponent m w t) :=
  (Real.rpow_le_rpow_of_exponent_ge hδ hδone (by linarith : (m:ℝ)/3 ≤ ((m:ℝ)+1)/3)).trans
    (power_center hδ hδone hw hwt ht)

variable (d : Data (Fin D) m) {δ w t : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
  (hw : 0 ≤ w) (hwt : w ≤ t) (ht : t ≤ (1:ℝ)/60)
  (hmesh : MeshConditions d (δ^w))
  (hspeed : centerSpeed d ≤ δ^((1:ℝ)/3))
include hδ hδone hw hwt ht hspeed

theorem state_payment :
    2*(budget d).velocity/(m.factorial:ℝ) ≤ stateCoefficient d*δ^(exponent m w t) := by
  exact (velocity_payment d hδ hspeed).trans
    (mul_le_mul_of_nonneg_left (power_state hδ hδone hw hwt ht)
      (by have := d.G.R_pos.le; positivity))

theorem score_payment (hm : 1 ≤ m) :
    (budget d).scoreError d.G d.sigma ≤ scoreCoefficient d*δ^(exponent m w t) := by
  have hc := centering_defect_le d hm hδ hspeed
  have hp := hc.trans (mul_le_mul_of_nonneg_left
    (power_center hδ hδone hw hwt ht) (by positivity [centerCoefficient_nonneg d]))
  have hdiv := div_le_div_of_nonneg_right hp (by have := d.hsigma.le; positivity : 0 ≤ d.sigma/2)
  convert hdiv using 1 <;> simp only [AffineResidual.Mean.DerivativeBudget.scoreError,
    scoreCoefficient] <;> ring

omit hspeed ht in
theorem conditional_payment (j : Fin m) (ρ : d.G.Kernel)
    (hc : d.G.conditional ρ = conditionalGeometricInterval (δ^w) hmesh.step_pos) :
    (budget d).conditionalError d.G d.r j ρ ≤ conditionalCoefficient d ρ*δ^(exponent m w t) := by
  have h := SmoothStepPayments.conditional_payment d hδ hmesh j ρ hc
  apply h.trans
  apply mul_le_mul_of_nonneg_left (power_wm hδ hδone hw (hw.trans hwt))
  have := d.hell
  have := d.G.variance_pos ρ
  have := conditionalOrderEnvelope_nonneg m
  have : 0 ≤ conditionalEnd := by norm_num [conditionalEnd]
  positivity

omit hspeed ht in
theorem forward_payment (j : Fin m) (ρ : d.G.Kernel) (z : Fin m)
    (hf : d.G.forward ρ = forwardGeometricInterval d.G ρ (δ^w) hmesh.step_pos) :
    AffineResidual.cellBudget (d.G.forward ρ) m ((budget d).forward j ρ z) ≤
      forwardCoefficient d ρ*δ^(exponent m w t) := by
  have h := withForwardCellBudget_cellBudget_le_geometric d (budget d) j ρ z
    (δ^w) hmesh.step_pos hmesh.step_upper hf
  change AffineResidual.cellBudget (d.G.forward ρ) m ((budget d).forward j ρ z) ≤ _ at h
  rw [step_power hδ] at h
  apply h.trans
  calc
    _ = forwardCoefficient d ρ*δ^(w*(m:ℝ)) := by unfold forwardCoefficient; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (power_wm hδ hδone hw (hw.trans hwt)) (by
      unfold forwardCoefficient
      have := sub_nonneg.mpr (d.G.rho_mem ρ).2.le
      have := forwardDerivativeBudget_nonneg d m
      positivity)

variable (hR : d.G.R = δ^t) (hpsi : d.G.psi = δ^(4*t))
  (hf : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ (δ^w) hmesh.step_pos)
include hmesh hR hpsi hf

theorem position_payment (a : ℝ) :
    (budget d).positionError d.G d.r d.sigma (δ^w) a ≤
      positionCoefficient d a*δ^(exponent m w t) := by
  unfold AffineResidual.Mean.DerivativeBudget.positionError
  calc
    _ ≤ stateCoefficient d*δ^(exponent m w t) +
        ∑ j : Fin m, |centerRow a j| *(SmoothAnglePayment.velocityCoefficient d*δ^(exponent m w t)) := by
      apply add_le_add (state_payment d hδ hδone hw hwt ht hspeed)
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (SmoothAnglePayment.velocity_common_payment d hδ hδone hw hwt ht hmesh hR hpsi hf j)
        (abs_nonneg _)
    _ = _ := by unfold positionCoefficient; simp only [add_mul, Finset.sum_mul]; congr 1; apply Finset.sum_congr rfl; intro j _; ring

theorem backward_payment (j : Fin m) :
    (budget d).backwardError d.G d.r d.sigma (δ^w) j ≤
      backwardCoefficient d j*δ^(exponent m w t) := by
  have hb := SmoothStepPayments.backward_payment d hδ hmesh j
  have hb' := hb.trans (mul_le_mul_of_nonneg_left
    (power_wm hδ hδone hw (hw.trans hwt)) (by
      have := d.G.backwardEnd_pos.le
      have := materialBackwardDerivativeBudget_nonneg d (m-1)
      positivity))
  unfold AffineResidual.Mean.DerivativeBudget.backwardError
  calc
    _ ≤ positionCoefficient d (centerNode j)*δ^(exponent m w t) + d.r*
        ((2^(m+1)*backwardEnd d.G.R*materialBackwardDerivativeBudget d (m-1)/(m.factorial:ℝ))*δ^(exponent m w t)) :=
      add_le_add (position_payment d hδ hδone hw hwt ht hmesh hspeed hR hpsi hf _)
        (mul_le_mul_of_nonneg_left hb' d.hr.le)
    _ = _ := by unfold backwardCoefficient; ring

variable (hc : ∀ ρ, d.G.conditional ρ = conditionalGeometricInterval (δ^w) hmesh.step_pos)
include hc

theorem rotation_payment (j : Fin m) (ρ : d.G.Kernel) (z : ℝ) :
    (budget d).rotationError d.G d.r d.sigma (δ^w) j ρ z ≤
      rotationCoefficient d j ρ z*δ^(exponent m w t) := by
  unfold AffineResidual.Mean.DerivativeBudget.rotationError
  have hm : 1 ≤ m := by have := hmesh.order; omega
  calc
    _ ≤ |1-(d.G.rotationScale ρ)^2*(1-Real.cos (z/d.G.rotationScale ρ))| *
        (backwardCoefficient d j*δ^(exponent m w t)) +
      |d.G.rho ρ * Real.sqrt (d.G.variance ρ) / (conditionalEnd*(1+(d.G.rho ρ)^2)) *
        (1-Real.cos (z/d.G.rotationScale ρ))| * (conditionalCoefficient d ρ*δ^(exponent m w t)) +
      |d.G.rotationScale ρ*Real.sin (z/d.G.rotationScale ρ)| *(scoreCoefficient d*δ^(exponent m w t)) := by
        apply add_le_add
        · exact add_le_add
            (mul_le_mul_of_nonneg_left (backward_payment d hδ hδone hw hwt ht hmesh hspeed hR hpsi hf j) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (conditional_payment d hδ hδone hw hwt hmesh j ρ (hc ρ)) (abs_nonneg _))
        · exact mul_le_mul_of_nonneg_left (score_payment d hδ hδone hw hwt ht hspeed hm) (abs_nonneg _)
    _ = _ := by unfold rotationCoefficient; ring

/-- Every actual row is paid at the same source exponent, retaining its
physical scale, local variance and rotation coefficients. -/
theorem row_payment (i : d.G.MeanNode) :
    (budget d).rowError d.G d.r d.sigma (δ^w) i ≤
      rowCoefficient d i*δ^(exponent m w t) := by
  rcases i with ⟨⟩ | j | ⟨j,k⟩ | ⟨j,ρ,k⟩ | ⟨j,ρ,z,k⟩
  · simp [AffineResidual.Mean.DerivativeBudget.rowError, rowCoefficient]
  · have hp := mul_le_mul_of_nonneg_left
      (position_payment d hδ hδone hw hwt ht hmesh hspeed hR hpsi hf (centerNode j))
      (mul_nonneg d.hr.le d.G.backwardEnd_pos.le)
    convert hp using 1 <;> simp only [AffineResidual.Mean.DerivativeBudget.rowError, rowCoefficient]; ring
  · have hp := mul_le_mul_of_nonneg_left
      (backward_payment d hδ hδone hw hwt ht hmesh hspeed hR hpsi hf j)
      (mul_nonneg d.hr.le (d.G.backward.location_mem_interval m k).1.le)
    convert hp using 1 <;> simp only [AffineResidual.Mean.DerivativeBudget.rowError, rowCoefficient]; ring
  · have hp := add_le_add
      (mul_le_mul_of_nonneg_left
        (backward_payment d hδ hδone hw hwt ht hmesh hspeed hR hpsi hf j)
        (mul_nonneg d.hr.le (d.G.rho_mem ρ).1))
      (mul_le_mul_of_nonneg_left
        (conditional_payment d hδ hδone hw hwt hmesh j ρ (hc ρ))
        (mul_nonneg (mul_nonneg d.hr.le (Real.sqrt_nonneg (d.G.variance ρ)))
          ((d.G.conditional ρ).location_mem_interval m k).1.le))
    convert hp using 1 <;> simp only [AffineResidual.Mean.DerivativeBudget.rowError, rowCoefficient]; ring
  · have hp := mul_le_mul_of_nonneg_left
      (add_le_add
        (rotation_payment d hδ hδone hw hwt ht hmesh hspeed hR hpsi hf hc j ρ (d.G.angleNode z))
        (mul_le_mul_of_nonneg_left
          (forward_payment d hδ hδone hw hwt hmesh j ρ z (hf ρ)) d.hr.le))
      (mul_nonneg d.hr.le ((d.G.rho_mem ρ).1.trans
        ((d.G.forward ρ).location_mem_interval m k).1.le))
    convert hp using 1 <;> simp only [AffineResidual.Mean.DerivativeBudget.rowError, rowCoefficient]; ring

/-- The norm of the explicit seven-component row budget is paid. Positivity of
its rows follows from the actual smooth residual theorem, so this norm step
never discards a possibly negative scalar bound. -/
theorem residual_payment (hv : VelocityBounds d) (ha : AngleBounds d) :
    residualBudget d (δ^w) (budget d) ≤ ‖rowCoefficient d‖*δ^(exponent m w t) := by
  have hm : 1 ≤ m := by have := hmesh.order; omega
  have hr := regularity d hm hv ha
  have hactual := AffineResidual.Mean.meanResidual d.G hmesh.order d.r d.sigma (δ^w)
    (Analysis.PositiveVarianceSlab.left (backwardEnd d.G.R))
    (Analysis.PositiveVarianceSlab.right (backwardEnd d.G.R)) d.hr d.hsigma
    hmesh.step_pos.le (left_margin d) (right_margin d) (cell_bound d (δ^w) hmesh)
    (operator d) 0 (initialPosition d) (initialScore d) (initialNoise d)
    (curvesWithSmoothBranches d) (budget d) (smoothBranches_canonical_equations d) hr
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg hδ.le _))).mpr
  intro i
  have hn : 0 ≤ (budget d).rowError d.G d.r d.sigma (δ^w) i :=
    (norm_nonneg _).trans (hactual i)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact (row_payment d hδ hδone hw hwt ht hmesh hspeed hR hpsi hf hc i).trans
    (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (norm_le_pi_norm (rowCoefficient d) i)) (Real.rpow_nonneg hδ.le _))

end AcceleratedLogConcave.Numerics.SmoothRowPayments
