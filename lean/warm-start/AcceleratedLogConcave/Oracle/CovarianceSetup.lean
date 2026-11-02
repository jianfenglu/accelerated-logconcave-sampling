import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Prescribed public covariance roots for the noisy compiler layer.
These mathematical real coefficients do not implement a finite-bit root algorithm. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.CovarianceSetup
open scoped BigOperators MatrixOrder
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def sigma (n : ℕ) (rho rowBound : ℝ) : ℝ :=
  rho / (2 * (Real.sqrt (n : ℝ) * rowBound))
def residualCovariance (A : Mat n) (rho rowBound : ℝ) : Mat n :=
  rho^2 • (1 : Mat n) - (sigma n rho rowBound)^2 • (A * A.transpose)
noncomputable def residualRoot (A : Mat n) (rho rowBound : ℝ) : Mat n :=
  CFC.sqrt (residualCovariance A rho rowBound)
def shiftSq (v : Fin N → ℝ) : ℝ := ∑ k, (v k)^2
def scaledShift (rho radius : ℝ) (v : Fin N → ℝ) : Fin N → ℝ :=
  fun k => (rho/radius) * v k
def childCovariance (rho radius : ℝ) (v : Fin N → ℝ) : Mat N :=
  1 - Matrix.vecMulVec (scaledShift rho radius v) (scaledShift rho radius v)
noncomputable def childRoot (rho radius : ℝ) (v : Fin N → ℝ) : Mat N :=
  CFC.sqrt (childCovariance rho radius v)


/-- Absolute row mass controls the actual Euclidean quadratic form. -/
theorem row_mass_quadratic (A : Mat n) {a : ℝ} (ha : 0 ≤ a)
    (hA : ∀ i, ∑ j, |A i j| ≤ a) (z : Fin n → ℝ) :
    dotProduct z ((A * A.transpose) *ᵥ z) ≤ (n : ℝ)*a^2*(∑ i, (z i)^2) := by
  have hrow (i : Fin n) : (∑ j, (A i j)^2) ≤ a^2 := by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun j => |A i j|) (fun _ _ => abs_nonneg _)
    simp only [sq_abs] at h
    exact h.trans ((sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) ha).2 (hA i))
  have hF : (∑ i, ∑ j, (A i j)^2) ≤ (n : ℝ)*a^2 := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  have hquad : dotProduct z ((A * A.transpose) *ᵥ z) =
      ∑ j, (∑ i, A i j*z i)^2 := by
    rw [← mulVec_mulVec]
    have h := dotProduct_transpose_mulVec A.transpose z (A.transpose *ᵥ z)
    rw [transpose_transpose] at h
    rw [h]
    simp [dotProduct,mulVec,transpose_apply,pow_two]
  rw [hquad]
  calc
    (∑ j, (∑ i, A i j*z i)^2) ≤
        ∑ j, (∑ i, (A i j)^2)*(∑ i, (z i)^2) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => A i j) z
    _ = (∑ i, ∑ j, (A i j)^2)*(∑ i, (z i)^2) := by
      rw [← Finset.sum_mul,Finset.sum_comm]
    _ ≤ (n : ℝ)*a^2*(∑ i, (z i)^2) :=
      mul_le_mul_of_nonneg_right hF (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Real symmetric matrix roots are the prescribed positive root. -/
theorem root_transpose_mul (S : Mat n) (hS : S.PosSemidef) :
    (CFC.sqrt S).PosSemidef ∧ CFC.sqrt S * (CFC.sqrt S).transpose = S := by
  have hp : (CFC.sqrt S).PosSemidef := (CFC.sqrt_nonneg S).posSemidef
  refine ⟨hp, ?_⟩
  have ht : (CFC.sqrt S).transpose = CFC.sqrt S := by
    simpa only [IsHermitian,conjTranspose_eq_transpose_of_trivial] using hp.isHermitian
  rw [ht]
  exact CFC.sqrt_mul_sqrt_self S hS.nonneg

theorem sigma_pos (hn : 0 < n) {rho a : ℝ} (hrho : 0 < rho) (ha : 0 < a) :
    0 < sigma n rho a := by
  unfold sigma
  exact div_pos hrho (mul_pos (by norm_num) (mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hn)) ha))

/-- The source completion covariance has its explicit three-quarter floor. -/
theorem residual_floor (A : Mat n) {rho a : ℝ} (_hrho : 0 ≤ rho) (ha : 0 < a)
    (hA : ∀ i, ∑ j, |A i j| ≤ a) :
    (residualCovariance A rho a - ((3:ℝ)/4*rho^2) • (1 : Mat n)).PosSemidef := by
  by_cases hn : n = 0
  · subst n
    have hz : residualCovariance A rho a - ((3:ℝ)/4*rho^2) • (1 : Mat 0) = 0 := by
      ext i
      exact i.elim0
    rw [hz]
    exact PosSemidef.zero
  have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hscale : (sigma n rho a)^2*((n:ℝ)*a^2) = rho^2/4 := by
    unfold sigma
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hnR.le]
    field_simp
    ring
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · simp [IsHermitian,residualCovariance,conjTranspose_eq_transpose_of_trivial,
      transpose_sub,transpose_smul,transpose_mul]
  intro z
  have hpay := mul_le_mul_of_nonneg_left (row_mass_quadratic A ha.le hA z)
    (sq_nonneg (sigma n rho a))
  rw [← mul_assoc,hscale] at hpay
  simp only [residualCovariance,sub_mulVec,smul_mulVec,one_mulVec,
    dotProduct_sub,dotProduct_smul,star_trivial,smul_eq_mul]
  have hz : dotProduct z z = ∑ i, (z i)^2 := by simp [dotProduct,pow_two]
  rw [hz]
  nlinarith

/-- The actual prescribed positive root, not an existential replacement. -/
theorem residual_root_identity (A : Mat n) {rho a : ℝ} (hrho : 0 ≤ rho) (ha : 0 < a)
    (hA : ∀ i, ∑ j, |A i j| ≤ a) :
    (residualRoot A rho a).PosSemidef ∧
    residualRoot A rho a * (residualRoot A rho a).transpose = residualCovariance A rho a := by
  apply root_transpose_mul
  have h := residual_floor A hrho ha hA
  have h0 : (((3:ℝ)/4*rho^2) • (1 : Mat n)).PosSemidef :=
    PosSemidef.one.smul (by positivity)
  simpa using h.add h0

theorem shiftSq_scaled (rho radius : ℝ) (v : Fin N → ℝ) :
    shiftSq (scaledShift rho radius v) = (rho/radius)^2*shiftSq v := by
  simp [shiftSq,scaledShift,mul_pow,Finset.mul_sum]

/-- The source radius/shift bound yields the required strict covariance margin. -/
theorem child_shift_quarter {rho radius Ds : ℝ} (v : Fin N → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : shiftSq v ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds)) :
    shiftSq (scaledShift rho radius v) ≤ (1:ℝ)/4 := by
  have hb : rho*Ds/radius ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ hr).2
    have h := (le_div_iff₀ (show 0 < 2*Ds by positivity)).1 hsmall
    nlinarith
  have hb2 := (sq_le_sq₀ (show 0 ≤ rho*Ds/radius by positivity)
    (show (0:ℝ) ≤ 1/2 by norm_num)).2 hb
  rw [shiftSq_scaled]
  calc
    (rho/radius)^2*shiftSq v ≤ (rho/radius)^2*Ds^2 :=
      mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    _ = (rho*Ds/radius)^2 := by ring
    _ ≤ (1:ℝ)/4 := by nlinarith

/-- Rank-one subtraction uses the actual finite shift vector. -/
theorem child_floor {rho radius Ds : ℝ} (v : Fin N → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : shiftSq v ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds)) :
    (childCovariance rho radius v - ((3:ℝ)/4) • (1 : Mat N)).PosSemidef := by
  let u := scaledShift rho radius v
  have hu : shiftSq u ≤ (1:ℝ)/4 := child_shift_quarter v hrho hr hDs hv hsmall
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · simp [IsHermitian,childCovariance,conjTranspose_eq_transpose_of_trivial,
      transpose_sub,transpose_smul,transpose_vecMulVec]
  intro z
  have hc : (dotProduct u z)^2 ≤ shiftSq u * (∑ i, (z i)^2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u z
  have hq : dotProduct z (vecMulVec u u *ᵥ z) = (dotProduct u z)^2 := by
    simp [vecMulVec_mulVec,dotProduct,Finset.mul_sum,pow_two,
      mul_comm,mul_left_comm,mul_assoc]
  have hp := mul_le_mul_of_nonneg_right hu (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (z i)))
  simp only [childCovariance,sub_mulVec,one_mulVec,smul_mulVec,dotProduct_sub,
    dotProduct_smul,star_trivial,smul_eq_mul]
  change 0 ≤ dotProduct z z - dotProduct z (vecMulVec u u *ᵥ z) - (3/4)*dotProduct z z
  rw [hq]
  have hz : dotProduct z z = ∑ i, (z i)^2 := by simp [dotProduct,pow_two]
  rw [hz]
  nlinarith

theorem child_root_identity {rho radius Ds : ℝ} (v : Fin N → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : shiftSq v ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds)) :
    (childRoot rho radius v).PosSemidef ∧
    childRoot rho radius v * (childRoot rho radius v).transpose = childCovariance rho radius v := by
  apply root_transpose_mul
  have h := child_floor v hrho hr hDs hv hsmall
  have h0 : (((3:ℝ)/4) • (1 : Mat N)).PosSemidef := PosSemidef.one.smul (by norm_num)
  simpa using h.add h0

/-- Literal source noise scale, using the actual child radius lower bound. -/
theorem source_radius_adapter {r R Ds radius : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hDs : 0 < Ds) (hlower : r*R/Real.sqrt 5 ≤ radius) :
    0 < r*R/(2*Real.sqrt 5*Ds) ∧ r*R/(2*Real.sqrt 5*Ds) ≤ radius/(2*Ds) := by
  constructor
  · positivity
  · have h := div_le_div_of_nonneg_right hlower (show 0 ≤ 2*Ds by positivity)
    convert h using 1
    field_simp

end AcceleratedLogConcave.Oracle.CovarianceSetup
