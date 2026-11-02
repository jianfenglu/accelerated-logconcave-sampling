import AcceleratedLogConcave.Numerics.SmoothStepPayments

/-! The complete Gaussian-angle term in the actual smooth mean receiver.
The kernel coefficient mass is paid by the first cell of the prescribed
backward partition, and the physical action's angle budget is retained. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.SmoothAnglePayment
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph AffineGraph.MeanGeometry
open SmoothQuantitativeAssembly SmoothStepPayments
variable {D m : ℕ}

/-- The real-power identity left after dropping the harmless factor `R≤1`.
Its exponent is precisely the manuscript's Gaussian-angle exponent. -/
theorem angle_power {δ : ℝ} (hδ : 0 < δ) (t w : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    (δ ^ (4 * t)) ^ (m - 1) * (2 / (δ ^ t) ^ 2) ^ m / δ ^ w =
      2 ^ m * δ ^ (2 * t * (m : ℝ) - 4 * t - w) := by
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm]
    norm_num
  have hden : ((δ ^ t) ^ 2) ^ m = δ ^ (2 * t * (m : ℝ)) := by
    rw [step_power hδ t 2]
    norm_num only [Nat.cast_ofNat]
    rw [step_power hδ (t * 2) m]
    congr 1
    ring
  rw [div_pow, step_power hδ (4 * t) (m - 1), hden]
  calc
    _ = 2 ^ m * (δ ^ (4 * t * ((m - 1 : ℕ) : ℝ)) /
      δ ^ (2 * t * (m : ℝ)) / δ ^ w) := by ring
    _ = 2 ^ m * δ ^ (2 * t * (m : ℝ) - 4 * t - w) := by
      rw [← Real.rpow_sub hδ, ← Real.rpow_sub hδ, hcast]
      congr 1
      ring_nf

/-- The full signed-kernel inventory in the velocity defect is bounded from
the actual angle derivative budget and the actual first-cell width. -/
theorem angle_weighted_payment (d : Data (Fin D) m) {δ t w : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 ≤ t)
    (hmesh : MeshConditions d (δ ^ w))
    (hR : d.G.R = δ ^ t) (hpsi : d.G.psi = δ ^ (4 * t))
    (j : Fin m) :
    (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| *
      ((m : ℝ) ^ 3 * d.G.psi ^ (m - 1) * (budget d).angle j ρ /
        (m.factorial : ℝ))) ≤
      (80 * (m : ℝ) ^ 5 * 2 ^ m * (d.r ^ 2 * d.ell) *
        Real.sqrt ((D + D : ℕ) * Tensor.AdjointReduction.PhaseBudget.Q
          (2 * auxiliaryConstant) (5 * m + 1)) / (m.factorial : ℝ)) *
        δ ^ (2 * t * (m : ℝ) - 4 * t - w) := by
  have h := (budget d).angle_weighted_budget_le d.G hmesh.order (δ ^ w)
    (angleBudget d) hmesh.step_pos (angleBudget_nonneg d) j
    (first_width d (δ ^ w) hmesh) (fun _ => le_rfl)
  change (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| *
    ((m : ℝ) ^ 3 * d.G.psi ^ (m - 1) * (budget d).angle j ρ /
      (m.factorial : ℝ))) ≤ _ at h
  have hRle : d.G.R ≤ 1 := by
    rw [hR]
    exact Real.rpow_le_one hδ.le hδ1 ht
  let Q : ℝ := Real.sqrt ((D + D : ℕ) * Tensor.AdjointReduction.PhaseBudget.Q
    (2 * auxiliaryConstant) (5 * m + 1))
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hAngle : angleBudget d ≤ 2 * (d.r ^ 2 * d.ell) * Q *
      (2 / d.G.R ^ 2) ^ m := by
    unfold angleBudget
    calc
      _ = d.G.R * (2 * (d.r ^ 2 * d.ell) * Q * (2 / d.G.R ^ 2) ^ m) := by
        dsimp [Q]
        ring
      _ ≤ 1 * (2 * (d.r ^ 2 * d.ell) * Q * (2 / d.G.R ^ 2) ^ m) :=
        mul_le_mul_of_nonneg_right hRle (by
          have : 0 ≤ d.ell := d.hell
          have : 0 ≤ 2 / d.G.R ^ 2 := by positivity
          positivity)
      _ = _ := one_mul _
  have hden : 0 < δ ^ w * (m.factorial : ℝ) := by positivity
  have hfactor : 0 ≤ 40 * (m : ℝ) ^ 5 := by positivity
  have hpsi0 : 0 ≤ d.G.psi ^ (m - 1) := pow_nonneg d.G.psi_pos.le _
  have hpaid :
      40 * (m : ℝ) ^ 5 * angleBudget d * d.G.psi ^ (m - 1) /
        (δ ^ w * (m.factorial : ℝ)) ≤
      40 * (m : ℝ) ^ 5 *
        (2 * (d.r ^ 2 * d.ell) * Q * (2 / d.G.R ^ 2) ^ m) *
        d.G.psi ^ (m - 1) / (δ ^ w * (m.factorial : ℝ)) := by
    gcongr
  calc
    _ ≤ 40 * (m : ℝ) ^ 5 * angleBudget d * d.G.psi ^ (m - 1) /
      (δ ^ w * (m.factorial : ℝ)) := h
    _ ≤ 40 * (m : ℝ) ^ 5 *
      (2 * (d.r ^ 2 * d.ell) * Q * (2 / d.G.R ^ 2) ^ m) *
      d.G.psi ^ (m - 1) / (δ ^ w * (m.factorial : ℝ)) := hpaid
    _ = (80 * (m : ℝ) ^ 5 * 2 ^ m * (d.r ^ 2 * d.ell) * Q /
          (m.factorial : ℝ)) * δ ^ (2 * t * (m : ℝ) - 4 * t - w) := by
      rw [hR, hpsi]
      have hp := angle_power hδ t w m (le_trans (by decide : 1 ≤ 2) hmesh.order)
      calc
        _ = (80 * (m : ℝ) ^ 5 * (d.r ^ 2 * d.ell) * Q /
          (m.factorial : ℝ)) *
          ((δ ^ (4 * t)) ^ (m - 1) * (2 / (δ ^ t) ^ 2) ^ m / δ ^ w) := by ring
        _ = _ := by rw [hp]; ring
    _ = _ := rfl

def kernelCoefficient (d : Data (Fin D) m) : ℝ :=
  (16 : ℝ) ^ m * materialKernelDerivativeBudget d (m + 2) / (m.factorial : ℝ)

def angleCoefficient (d : Data (Fin D) m) : ℝ :=
  80 * (m : ℝ) ^ 5 * 2 ^ m * (d.r ^ 2 * d.ell) *
    Real.sqrt ((D + D : ℕ) * Tensor.AdjointReduction.PhaseBudget.Q
      (2 * auxiliaryConstant) (5 * m + 1)) / (m.factorial : ℝ)

def forwardCoefficient (d : Data (Fin D) m) : ℝ :=
  40 * 2 ^ (m + 1) * (m : ℝ) ^ 5 * forwardDerivativeBudget d m /
    (m.factorial : ℝ)

/-- Entire actual velocity defect, including kernel values, the signed
Gaussian-angle inventory, and the signed forward inventory. -/
def velocityCoefficient (d : Data (Fin D) m) : ℝ :=
  (kernelCoefficient d + angleCoefficient d) / (d.r * (d.sigma / 2)) +
    forwardCoefficient d / (d.sigma / 2)

theorem kernelCoefficient_nonneg (d : Data (Fin D) m) :
    0 ≤ kernelCoefficient d := by
  unfold kernelCoefficient
  have := materialKernelDerivativeBudget_nonneg d (m + 2)
  positivity

theorem angleCoefficient_nonneg (d : Data (Fin D) m) :
    0 ≤ angleCoefficient d := by
  unfold angleCoefficient
  have := d.hell
  positivity

theorem forwardCoefficient_nonneg (d : Data (Fin D) m) :
    0 ≤ forwardCoefficient d := by
  unfold forwardCoefficient
  have := forwardDerivativeBudget_nonneg d m
  positivity

theorem velocityCoefficient_nonneg (d : Data (Fin D) m) :
    0 ≤ velocityCoefficient d := by
  unfold velocityCoefficient
  have hk := kernelCoefficient_nonneg d
  have ha := angleCoefficient_nonneg d
  have hf := forwardCoefficient_nonneg d
  have hr := d.hr.le
  have hs := d.hsigma.le
  positivity

/-- All three velocity-component powers dominate the common forward power. -/
theorem component_exponents (m : ℕ) (hm : 2 ≤ m) {t w : ℝ}
    (hw : 0 ≤ w) (hwt : w ≤ t) (ht60 : t ≤ 1 / 60) :
    w * ((m - 1 : ℕ) : ℝ) - 4 * t ≤ w * (m : ℝ) ∧
    w * ((m - 1 : ℕ) : ℝ) - 4 * t ≤
      2 * t * (m : ℝ) - 4 * t - w ∧
    w * ((m - 1 : ℕ) : ℝ) - 4 * t ≤ ((m : ℝ) + 1) / 3 := by
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := hw.trans hwt
  have hgap : 0 ≤ 2 * t - w := by linarith
  have hangle := mul_nonneg hgap hm0
  have htm := mul_le_mul_of_nonneg_right ht60 hm0
  have hwm := mul_le_mul_of_nonneg_right hwt hm0
  rw [hcast]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- All terms in the actual `DerivativeBudget.velocityError` share the
manuscript's weakest exponent `β=w(m-1)-4t`. -/
theorem velocity_common_payment (d : Data (Fin D) m) {δ t w : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ w) (hwt : w ≤ t)
    (ht60 : t ≤ 1 / 60)
    (hmesh : MeshConditions d (δ ^ w))
    (hR : d.G.R = δ ^ t) (hpsi : d.G.psi = δ ^ (4 * t))
    (hf : ∀ ρ, d.G.forward ρ = forwardGeometricInterval d.G ρ
      (δ ^ w) hmesh.step_pos) (j : Fin m) :
    (budget d).velocityError d.G d.r d.sigma (δ ^ w) j ≤
      velocityCoefficient d * δ ^ (w * ((m - 1 : ℕ) : ℝ) - 4 * t) := by
  let β : ℝ := w * ((m - 1 : ℕ) : ℝ) - 4 * t
  have he := component_exponents m hmesh.order hw hwt ht60
  have hpK : δ ^ (w * (m : ℝ)) ≤ δ ^ β :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 he.1
  have hpA : δ ^ (2 * t * (m : ℝ) - 4 * t - w) ≤ δ ^ β :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 he.2.1
  have hpF : δ ^ (w * ((m - 1 : ℕ) : ℝ) - 4 * t) = δ ^ β := rfl
  have hk :
      (16 : ℝ) ^ m * (budget d).kernel j * (δ ^ w) ^ m /
        (m.factorial : ℝ) ≤ kernelCoefficient d * δ ^ β := by
    rw [kernel_value_payment d hδ j]
    exact mul_le_mul_of_nonneg_left hpK (kernelCoefficient_nonneg d)
  have ha :
      (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| *
        ((m : ℝ) ^ 3 * d.G.psi ^ (m - 1) * (budget d).angle j ρ /
          (m.factorial : ℝ))) ≤ angleCoefficient d * δ ^ β := by
    have h := angle_weighted_payment d hδ hδ1 (hw.trans hwt) hmesh hR hpsi j
    change _ ≤ angleCoefficient d * δ ^ (2 * t * (m : ℝ) - 4 * t - w) at h
    exact h.trans (mul_le_mul_of_nonneg_left hpA (angleCoefficient_nonneg d))
  have hfwd :
      (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
        |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
          ((budget d).forward j ρ a)) ≤ forwardCoefficient d * δ ^ β := by
    have h := forward_payment d hδ hmesh hpsi j hf
    change _ ≤ forwardCoefficient d * δ ^ β at h
    exact h
  have hsum :
      (16 : ℝ) ^ m * (budget d).kernel j * (δ ^ w) ^ m /
        (m.factorial : ℝ) +
      (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| *
        ((m : ℝ) ^ 3 * d.G.psi ^ (m - 1) * (budget d).angle j ρ /
          (m.factorial : ℝ))) ≤
      (kernelCoefficient d + angleCoefficient d) * δ ^ β := by
    calc
      _ ≤ kernelCoefficient d * δ ^ β + angleCoefficient d * δ ^ β := add_le_add hk ha
      _ = _ := by ring
  have hden1 : 0 < d.r * (d.sigma / 2) := by
    exact mul_pos d.hr (div_pos d.hsigma (by norm_num))
  have hden2 : 0 < d.sigma / 2 := by
    exact div_pos d.hsigma (by norm_num)
  change ((16 : ℝ) ^ m * (budget d).kernel j * (δ ^ w) ^ m /
      (m.factorial : ℝ) +
      (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| *
        ((m : ℝ) ^ 3 * d.G.psi ^ (m - 1) * (budget d).angle j ρ /
          (m.factorial : ℝ)))) / (d.r * (d.sigma / 2)) +
    (∑ ρ : d.G.Kernel, |d.G.kernelCoeff ρ| * ∑ a : Fin m,
      |d.G.angleDerivative a| * AffineResidual.cellBudget (d.G.forward ρ) m
        ((budget d).forward j ρ a)) / (d.sigma / 2) ≤ _
  calc
    _ ≤ ((kernelCoefficient d + angleCoefficient d) * δ ^ β) /
        (d.r * (d.sigma / 2)) +
      (forwardCoefficient d * δ ^ β) / (d.sigma / 2) := by
        exact add_le_add (div_le_div_of_nonneg_right hsum hden1.le)
          (div_le_div_of_nonneg_right hfwd hden2.le)
    _ = velocityCoefficient d * δ ^ β := by
      unfold velocityCoefficient
      ring

end AcceleratedLogConcave.Numerics.SmoothAnglePayment
