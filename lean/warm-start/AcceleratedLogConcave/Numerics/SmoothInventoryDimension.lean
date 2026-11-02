import AcceleratedLogConcave.Numerics.NumericalCoefficientGrowth
import AcceleratedLogConcave.Numerics.SmoothRowInventory

/-! Factor the dimension dependence of the actual coefficient inventory. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SmoothInventoryDimension
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph AffineGraph.MeanGeometry
open SmoothQuantitativeAssembly SmoothQuadraturePayments SmoothRowPayments SmoothRowInventory
open SmoothAnglePayment Tensor.ActualCoefficientIntegrability
open ConditionalSmoothing
variable {D m : ℕ}

private theorem rms_factor (D s : ℕ) :
    materialRmsNumeric D s = (D : ℝ) * materialRmsNumeric 1 s := by
  unfold materialRmsNumeric
  push_cast
  ring

private theorem sqrt_rms_factor (D s : ℕ) :
    Real.sqrt (materialRmsNumeric D s) =
      Real.sqrt (D : ℝ) * Real.sqrt (materialRmsNumeric 1 s) := by
  rw [rms_factor, Real.sqrt_mul (Nat.cast_nonneg D)]

private theorem sqrt_phase_factor (D : ℕ) (c : ℝ) (n : ℕ) :
    Real.sqrt (((D + D : ℕ) : ℝ) * Tensor.AdjointReduction.PhaseBudget.Q c n) =
      Real.sqrt (D : ℝ) *
        Real.sqrt (2 * Tensor.AdjointReduction.PhaseBudget.Q c n) := by
  have he : (((D + D : ℕ) : ℝ) : ℝ) * Tensor.AdjointReduction.PhaseBudget.Q c n =
      (D : ℝ) * (2 * Tensor.AdjointReduction.PhaseBudget.Q c n) := by
    push_cast
    ring
  rw [he, Real.sqrt_mul (Nat.cast_nonneg D)]

def kernelUnit (k : ℕ) : ℝ :=
  Real.exp (1/2:ℝ) * (k.factorial : ℝ) *
    (Tensor.ActualCoefficientIntegrability.materialWordMassBase k)^k *
      Real.sqrt (materialRmsNumeric 1 (3*k-1))

def backwardUnit (k : ℕ) : ℝ :=
  (3*(3+3*(k:ℝ)+1)^2)^k *
    Real.sqrt (materialRmsNumeric 1 (3+3*k))

theorem kernel_budget_factor (d : Data (Fin D) m) (k : ℕ) :
    materialKernelDerivativeBudget d k =
      (d.ell*d.r^2)*Real.sqrt (D : ℝ)*kernelUnit k := by
  unfold materialKernelDerivativeBudget kernelUnit
  rw [sqrt_rms_factor]
  dsimp [kernelData]
  ring

theorem backward_budget_factor (d : Data (Fin D) m) (k : ℕ) :
    materialBackwardDerivativeBudget d k =
      (d.ell*d.r)*Real.sqrt (D : ℝ)*backwardUnit k := by
  unfold materialBackwardDerivativeBudget backwardUnit
  rw [sqrt_rms_factor]
  ring


def stateUnit (m : ℕ) : ℝ :=
  2 * Real.sqrt (2 * Tensor.AdjointReduction.PhaseBudget.Q 128 (5*(m+1)+1)) /
    (m.factorial : ℝ)
def scoreUnit (m : ℕ) : ℝ :=
  4 * Real.sqrt (2 * Tensor.AdjointReduction.PhaseBudget.Q 128 (5*m+1)) /
    (m.factorial : ℝ)
def kernelVelocityUnit (m : ℕ) : ℝ :=
  2 * 16^m * kernelUnit (m+2) / (m.factorial : ℝ)
def angleVelocityUnit (m : ℕ) : ℝ :=
  160 * (m : ℝ)^5 * 2^m *
    Real.sqrt (2 * Tensor.AdjointReduction.PhaseBudget.Q 256 (5*m+1)) /
      (m.factorial : ℝ)
def forwardVelocityUnit (m : ℕ) : ℝ :=
  80 * 2^(m+1) * (m : ℝ)^5 * conditionalOrderEnvelope m /
    (m.factorial : ℝ)
def velocityUnit (m : ℕ) : ℝ :=
  kernelVelocityUnit m + angleVelocityUnit m + forwardVelocityUnit m
def backwardRowUnit (m : ℕ) : ℝ :=
  2^(m+1) * backwardUnit (m-1) / (m.factorial : ℝ)
def conditionalRowUnit (m : ℕ) : ℝ :=
  2^(m+1) * conditionalEnd * conditionalOrderEnvelope m /
    (m.factorial : ℝ)
def forwardRowUnit (m : ℕ) : ℝ :=
  2^(m+1) * conditionalOrderEnvelope m / (m.factorial : ℝ)

/-- Explicit m-only majorant. Every term comes from a literal row component. -/
def A (m : ℕ) : ℝ :=
  3*(stateUnit m+velocityUnit m+backwardRowUnit m)+
    4*conditionalRowUnit m+scoreUnit m+forwardRowUnit m

private theorem units_nonneg (m : ℕ) :
    0 ≤ stateUnit m ∧ 0 ≤ scoreUnit m ∧ 0 ≤ velocityUnit m ∧
    0 ≤ backwardRowUnit m ∧ 0 ≤ conditionalRowUnit m ∧
    0 ≤ forwardRowUnit m := by
  have hk : 0 ≤ kernelUnit (m+2) := by
    unfold kernelUnit
    have := Tensor.ActualCoefficientIntegrability.materialWordMassBase_one_le (m+2)
    positivity
  have hb : 0 ≤ backwardUnit (m-1) := by
    unfold backwardUnit
    positivity
  have hc : 0 ≤ conditionalEnd := by norm_num [conditionalEnd]
  have he := conditionalOrderEnvelope_nonneg m
  have hq128a := Tensor.AdjointReduction.PhaseBudget.Q_nonneg
    (by norm_num : (0:ℝ) ≤ 128) (5*(m+1)+1)
  have hq128b := Tensor.AdjointReduction.PhaseBudget.Q_nonneg
    (by norm_num : (0:ℝ) ≤ 128) (5*m+1)
  have hq256 := Tensor.AdjointReduction.PhaseBudget.Q_nonneg
    (by norm_num : (0:ℝ) ≤ 256) (5*m+1)
  unfold stateUnit scoreUnit velocityUnit kernelVelocityUnit angleVelocityUnit
    forwardVelocityUnit backwardRowUnit conditionalRowUnit forwardRowUnit
  constructor <;> [positivity; constructor <;> [positivity; constructor <;>
    [positivity; constructor <;> [positivity; constructor <;> [positivity; positivity]]]]]

theorem state_factor (d : Data (Fin D) m) :
    stateCoefficient d = d.G.R * Real.sqrt (D : ℝ) * stateUnit m := by
  unfold stateCoefficient stateUnit
  rw [sqrt_phase_factor]
  dsimp [auxiliaryConstant]
  ring

theorem score_factor (d : Data (Fin D) m) :
    scoreCoefficient d =
      (d.ell*d.r/d.sigma)*Real.sqrt (D : ℝ)*scoreUnit m := by
  unfold scoreCoefficient centerCoefficient scoreUnit
  have hq : Real.sqrt (2*(D:ℝ)*Tensor.AdjointReduction.PhaseBudget.Q
      auxiliaryConstant (5*m+1)) =
      Real.sqrt (D:ℝ)*Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q
        auxiliaryConstant (5*m+1)) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg D)]
    ring
  rw [hq]
  dsimp [auxiliaryConstant]
  field_simp [d.hsigma.ne']
  ring

theorem kernel_velocity_factor (d : Data (Fin D) m) :
    kernelCoefficient d / (d.r*(d.sigma/2)) =
      (d.ell*d.r/d.sigma)*Real.sqrt (D : ℝ)*kernelVelocityUnit m := by
  unfold kernelCoefficient kernelVelocityUnit
  rw [kernel_budget_factor]
  field_simp [d.hr.ne', d.hsigma.ne']

theorem angle_velocity_factor (d : Data (Fin D) m) :
    angleCoefficient d / (d.r*(d.sigma/2)) =
      (d.ell*d.r/d.sigma)*Real.sqrt (D : ℝ)*angleVelocityUnit m := by
  unfold angleCoefficient angleVelocityUnit
  rw [sqrt_phase_factor]
  dsimp [auxiliaryConstant]
  field_simp [d.hr.ne', d.hsigma.ne']
  all_goals ring

theorem forward_velocity_factor (d : Data (Fin D) m) :
    SmoothAnglePayment.forwardCoefficient d / (d.sigma/2) =
      (d.ell*d.r/d.sigma)*Real.sqrt (D : ℝ)*forwardVelocityUnit m := by
  unfold SmoothAnglePayment.forwardCoefficient forwardVelocityUnit forwardDerivativeBudget
  field_simp [d.hsigma.ne']
  simp only [Fintype.card_fin]
  ring

theorem velocity_factor (d : Data (Fin D) m) :
    velocityCoefficient d =
      (d.ell*d.r/d.sigma)*Real.sqrt (D : ℝ)*velocityUnit m := by
  unfold velocityCoefficient velocityUnit
  rw [add_div, kernel_velocity_factor, angle_velocity_factor,
    forward_velocity_factor]
  all_goals ring

theorem backward_row_factor (d : Data (Fin D) m) :
    d.r*(2^(m+1)*backwardEnd d.G.R*
      materialBackwardDerivativeBudget d (m-1)/(m.factorial:ℝ)) =
      (d.ell*d.r^2)*backwardEnd d.G.R*
        Real.sqrt (D:ℝ)*backwardRowUnit m := by
  rw [backward_budget_factor]
  unfold backwardRowUnit
  ring

theorem conditional_row_factor (d : Data (Fin D) m) :
    conditionalBound d =
      (d.ell*d.r^2)*Real.sqrt (D:ℝ)*conditionalRowUnit m := by
  unfold conditionalBound conditionalRowUnit
  simp only [Fintype.card_fin]
  ring

theorem forward_row_factor (d : Data (Fin D) m) :
    d.r*forwardBound d =
      (d.ell*d.r^2)*backwardEnd d.G.R*
        Real.sqrt (D:ℝ)*forwardRowUnit m := by
  unfold forwardBound forwardRowUnit forwardDerivativeBudget
  simp only [Fintype.card_fin]
  ring


/-- Exact factoring of every physical row component before using the two
smallness inequalities. This identity keeps the signed geometry coefficients
inside the already-proved inventory estimate. -/
theorem inventory_factor (d : Data (Fin D) m) :
    inventoryBound d = Real.sqrt (D : ℝ) *
      (3*(d.G.R*stateUnit m+
          (d.ell*d.r/d.sigma)*velocityUnit m+
          (d.ell*d.r^2)*backwardEnd d.G.R*backwardRowUnit m)+
       4*(d.ell*d.r^2)*conditionalRowUnit m+
       (d.ell*d.r/d.sigma)*scoreUnit m+
       (d.ell*d.r^2)*backwardEnd d.G.R*forwardRowUnit m) := by
  unfold inventoryBound backwardBound positionBound
  rw [state_factor, velocity_factor, backward_row_factor,
    conditional_row_factor, score_factor, forward_row_factor]
  ring

/-- The scalar inventory is controlled by a dimension factor and a fully
explicit order-only coefficient. The radius factor remains outside in
`SmoothRowInventory.norm_rowCoefficient_le`. -/
theorem inventory_le_dimension (d : Data (Fin D) m)
    (hR : d.G.R ≤ 1) (hscale : d.ell*d.r/d.sigma ≤ 1) :
    inventoryBound d ≤ Real.sqrt (D : ℝ) * A m := by
  have hsize : d.ell*d.r^2 ≤ 1 := by
    have hs := d.hsmall
    nlinarith
  have hsize0 : 0 ≤ d.ell*d.r^2 := by positivity [d.hell, d.hr.le]
  have hscale0 : 0 ≤ d.ell*d.r/d.sigma := by positivity [d.hell, d.hr.le, d.hsigma.le]
  have hB : 0 ≤ backwardEnd d.G.R := d.G.backwardEnd_pos.le
  have hB1 : backwardEnd d.G.R ≤ 1 := d.G.backwardEnd_lt_one.le
  have hRB : d.ell*d.r^2*backwardEnd d.G.R ≤ 1 := by
    nlinarith [mul_nonneg hsize0 (sub_nonneg.mpr hB1),
      mul_nonneg (sub_nonneg.mpr hsize) hB]
  obtain ⟨hstate, hscore, hvelocity, hbackward, hconditional, hforward⟩ :=
    units_nonneg m
  have hs : d.G.R*stateUnit m ≤ stateUnit m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) hstate]
  have hv : (d.ell*d.r/d.sigma)*velocityUnit m ≤ velocityUnit m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale) hvelocity]
  have hb : (d.ell*d.r^2)*backwardEnd d.G.R*backwardRowUnit m ≤
      backwardRowUnit m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hRB) hbackward]
  have hc : (d.ell*d.r^2)*conditionalRowUnit m ≤ conditionalRowUnit m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsize) hconditional]
  have hsc : (d.ell*d.r/d.sigma)*scoreUnit m ≤ scoreUnit m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale) hscore]
  have hf : (d.ell*d.r^2)*backwardEnd d.G.R*forwardRowUnit m ≤
      forwardRowUnit m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hRB) hforward]
  rw [inventory_factor]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  unfold A
  nlinarith


theorem A_nonneg (m : ℕ) : 0 ≤ A m := by
  obtain ⟨hs,hsc,hv,hb,hc,hf⟩ := units_nonneg m
  unfold A
  positivity

/-- Final reusable radius and dimension bound for the actual row norm. -/
theorem norm_rowCoefficient_le_dimension (d : Data (Fin D) m)
    (hm : 0 < m) (hR : d.G.R ≤ 1)
    (hscale : d.ell*d.r/d.sigma ≤ 1) :
    ‖rowCoefficient d‖ ≤ d.r*Real.sqrt (D : ℝ)*A m := by
  calc
    ‖rowCoefficient d‖ ≤ d.r*inventoryBound d := norm_rowCoefficient_le d hm
    _ ≤ d.r*(Real.sqrt (D : ℝ)*A m) :=
      mul_le_mul_of_nonneg_left (inventory_le_dimension d hR hscale) d.hr.le
    _ = d.r*Real.sqrt (D : ℝ)*A m := by ring


end AcceleratedLogConcave.Numerics.SmoothInventoryDimension
