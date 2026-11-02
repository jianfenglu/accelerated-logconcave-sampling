import AcceleratedLogConcave.Numerics.SmoothAllReceiver
import AcceleratedLogConcave.Analysis.FiniteDerivativeLadder

/-! Exact harmonic angle jets in the actual common L² space.
This pays the rotation-input side of angle regularity, not the higher
spatial variations of the nonlinear endpoint transport. -/
noncomputable section
open Set
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace AcceleratedLogConcave.Analysis.AngleRotation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Coefficient recursion differentiates a harmonic curve without derivative norms. -/
def coefficients (q : ℝ) (A B : E) : ℕ → E × E
  | 0 => (A,B)
  | n+1 => (q⁻¹ • (coefficients q A B n).2, -q⁻¹ • (coefficients q A B n).1)

def harmonic (q : ℝ) (A B : E) (z : ℝ) : E :=
  Real.cos (z/q) • A + Real.sin (z/q) • B

def jet (q : ℝ) (A B : E) (n : ℕ) : ℝ → E :=
  harmonic q (coefficients q A B n).1 (coefficients q A B n).2

theorem hasDerivAt_harmonic (q : ℝ) (A B : E) (z : ℝ) :
    HasDerivAt (harmonic q A B)
      (harmonic q (q⁻¹ • B) (-q⁻¹ • A) z) z := by
  have hc := (((hasDerivAt_id z).div_const q).cos).smul_const A
  have hs := (((hasDerivAt_id z).div_const q).sin).smul_const B
  convert hc.add hs using 1
  · rfl
  · simp [harmonic, div_eq_mul_inv, smul_smul, add_comm, mul_comm]

theorem hasDerivAt_jet (q : ℝ) (A B : E) (n : ℕ) (z : ℝ) :
    HasDerivAt (jet q A B n) (jet q A B (n+1) z) z :=
  hasDerivAt_harmonic q _ _ z

theorem iteratedDeriv_harmonic (q : ℝ) (A B : E) (n : ℕ) (z : ℝ) :
    iteratedDeriv n (harmonic q A B) z = jet q A B n z := by
  exact Analysis.iteratedDeriv_eq_of_finite_ladder n (jet q A B) isOpen_univ
    (fun k _ t _ => hasDerivAt_jet q A B k t) (mem_univ z)

theorem coefficients_norm_le {q : ℝ} (hq : 0 ≤ q) (A B : E) (n : ℕ) :
    ‖(coefficients q A B n).1‖ + ‖(coefficients q A B n).2‖ =
      (q⁻¹)^n * (‖A‖+‖B‖) := by
  induction n with
  | zero => simp [coefficients]
  | succ n ih =>
    simp only [coefficients, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (inv_nonneg.mpr hq)]
    rw [← mul_add, add_comm ‖(coefficients q A B n).2‖, ih, pow_succ]
    ring

theorem norm_harmonic_le (q : ℝ) (A B : E) (z : ℝ) :
    ‖harmonic q A B z‖ ≤ ‖A‖+‖B‖ := by
  calc
    _ ≤ ‖Real.cos (z/q) • A‖ + ‖Real.sin (z/q) • B‖ := norm_add_le _ _
    _ = |Real.cos (z/q)| *‖A‖ + |Real.sin (z/q)| *‖B‖ := by simp [norm_smul]
    _ ≤ 1*‖A‖ + 1*‖B‖ := add_le_add
      (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (norm_nonneg _))
    _ = _ := by ring

theorem norm_iteratedDeriv_harmonic_le {q : ℝ} (hq : 0 ≤ q)
    (A B : E) (n : ℕ) (z : ℝ) :
    ‖iteratedDeriv n (harmonic q A B) z‖ ≤ (q⁻¹)^n*(‖A‖+‖B‖) := by
  rw [iteratedDeriv_harmonic]
  exact (norm_harmonic_le q _ _ z).trans_eq (coefficients_norm_le hq A B n)

/-- The fixed midpoint disappears at every positive order. -/
theorem iteratedDeriv_shift_harmonic_succ (q : ℝ) (mid A B : E) (n : ℕ) (z : ℝ) :
    iteratedDeriv (n+1) (fun t => mid+harmonic q A B t) z = jet q A B (n+1) z := by
  rw [iteratedDeriv_succ']
  have he : deriv (fun t => mid+harmonic q A B t) = jet q A B 1 := by
    funext t
    simpa only [zero_add, Pi.add_def, jet, coefficients] using ((hasDerivAt_const t mid).add
      (hasDerivAt_harmonic q A B t)).deriv
  rw [he]
  exact Analysis.iteratedDeriv_eq_of_finite_ladder n (fun k => jet q A B (k+1))
    isOpen_univ (fun k _ t _ => hasDerivAt_jet q A B (k+1) t) (mem_univ z)

theorem norm_iteratedDeriv_shift_harmonic_succ_le {q : ℝ} (hq : 0 ≤ q)
    (mid A B : E) (n : ℕ) (z : ℝ) :
    ‖iteratedDeriv (n+1) (fun t => mid+harmonic q A B t) z‖ ≤
      (q⁻¹)^(n+1)*(‖A‖+‖B‖) := by
  rw [iteratedDeriv_shift_harmonic_succ]
  exact (norm_harmonic_le q _ _ z).trans_eq (coefficients_norm_le hq A B (n+1))
end AcceleratedLogConcave.Analysis.AngleRotation

namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Analysis.AngleRotation AffineGraph AffineGraph.MeanGeometry MeanResidualBridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- Literal common-space midpoint, not an independent replacement random variable. -/
def rotationMidpointLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) : H d :=
  let B := backwardLp d j (d.G.rho k)
  let H := d.G.rho k • B+(Real.sqrt (d.G.variance k)/conditionalEnd) • conditionalLp d j k conditionalEnd
  (d.G.rho k/(1+(d.G.rho k)^2)) • (H+d.G.rho k • B)

theorem rotationLp_eq_harmonic (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    rotationLp d j k = fun z => rotationMidpointLp d j k +
      harmonic (d.G.rotationScale k)
        (backwardLp d j (d.G.rho k)-rotationMidpointLp d j k)
        (d.G.rotationScale k • scoreLp d (centerNode j)) z := by
  funext z
  rw [rotationLp_eq]
  simp only [rotationMidpointLp, harmonic, smul_smul, mul_comm, add_assoc]

/-- Explicit all-order bound for the actual rotation input. The remaining endpoint
transport composition is not asserted by this theorem. -/
theorem norm_iteratedDeriv_rotationLp_succ_le (d : Data ι m)
    (j : Fin m) (k : d.G.Kernel) (n : ℕ) (z : ℝ) :
    ‖iteratedDeriv (n+1) (rotationLp d j k) z‖ ≤
      ((d.G.rotationScale k)⁻¹)^(n+1) *
        (‖backwardLp d j (d.G.rho k)-rotationMidpointLp d j k‖+
          d.G.rotationScale k * ‖scoreLp d (centerNode j)‖) := by
  rw [rotationLp_eq_harmonic]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (d.G.rotationScale_pos k)] using
    norm_iteratedDeriv_shift_harmonic_succ_le (d.G.rotationScale_pos k).le
      (rotationMidpointLp d j k)
      (backwardLp d j (d.G.rho k)-rotationMidpointLp d j k)
      (d.G.rotationScale k • scoreLp d (centerNode j)) n z
end AcceleratedLogConcave.Numerics.MeanFlowLp
