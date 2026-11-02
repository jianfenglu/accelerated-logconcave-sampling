import AcceleratedLogConcave.Oracle.RecursiveStabilityEnvelope
import AcceleratedLogConcave.Oracle.RecursiveSizeBound
import Mathlib.Algebra.Order.Ring.Finset

/-! Division-free row supremum and scalar height consequences of the existing
root resolution cap. No descendant stability or height bound is assumed. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open Numerics.AffineGraph RecursiveExecutable RecursiveSize
open scoped BigOperators NNReal

/-- Multiplication commutes with finite NNReal suprema, including empty rows
and zero multiplier. No division by the oracle constant is used. -/
theorem scaled_sup_le {ι : Type*} [Fintype ι] (f : ι → ℝ≥0) (L : ℝ≥0)
    {η : ℝ} (hη : 0 ≤ η) (hf : ∀ i, (L : ℝ)*f i ≤ η) :
    (L : ℝ)*(Finset.univ.sup f : ℝ≥0) ≤ η := by
  have h : L * Finset.univ.sup f ≤ (⟨η, hη⟩ : ℝ≥0) := by
    rw [Finset.mul_sup₀]
    exact Finset.sup_le fun i _ => hf i
  exact h

/-- Pointwise bounds on 2L times the actual rows pay L times their maximum. -/
theorem actualRowMass_small_of_rows {m : ℕ} (M : MeanGeometry m) (r σ : ℝ)
    (L : ℝ≥0) {η : ℝ} (hη : 0 ≤ η)
    (hrows : ∀ i : M.MeanNode, 2*(L : ℝ)*(∑ j, |M.matrix r σ i j|) ≤ η) :
    (L : ℝ)*actualRowMass M r σ ≤ η := by
  apply scaled_sup_le _ L hη
  intro i
  change (L : ℝ)*(∑ j, |M.matrix r σ i j|) ≤ η
  have hn : 0 ≤ (L : ℝ)*(∑ j, |M.matrix r σ i j|) :=
    mul_nonneg L.coe_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  nlinarith [hrows i]

/-- The existing resolution coefficient dominates both 520 and 40 times the
root height. Bernoulli handles H=0 without dividing by H. -/
theorem resolution_coefficient_lower {m : ℕ} (hm : 2 ≤ m) (B : ℝ) (hB : 1 ≤ B)
    (H : ℕ) :
    520 ≤ 520*(m : ℝ)^5*(stepFactor m B)^H ∧
      40*(H : ℝ) ≤ 520*(m : ℝ)^5*(stepFactor m B)^H := by
  have hS : 3 ≤ stepFactor m B := stepFactor_ge_three m B (by linarith)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm5 : (1 : ℝ) ≤ (m : ℝ)^5 := one_le_pow₀ hm1
  have hpow : (1 : ℝ) ≤ (stepFactor m B)^H := one_le_pow₀ (by linarith)
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ stepFactor m B - 1 by linarith) H
  have hSH : (H : ℝ) ≤ (stepFactor m B)^H := by
    have he : 1 + (stepFactor m B - 1) = stepFactor m B := by ring
    rw [he] at hbern
    nlinarith [Nat.cast_nonneg (α := ℝ) H]
  constructor
  · calc
      520 = 520*1*1 := by ring
      _ ≤ 520*(m : ℝ)^5*(stepFactor m B)^H := by gcongr
  · calc
      40*(H : ℝ) ≤ (520*(m : ℝ)^5)*(H : ℝ) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg H)
      _ ≤ _ := mul_le_mul_of_nonneg_left hSH (by positivity)

/-- The unchanged root resolution cap pays both requirements of height
absorption at eta = delta^(1/3). No additional smallness cap is needed. -/
theorem resolution_pays_height {m : ℕ} (hm : 2 ≤ m) (B : ℝ) (hB : 1 ≤ B)
    (H : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hres : δ ≤ (520*(m : ℝ)^5*(stepFactor m B)^H)^(-12 : ℝ)) :
    0 ≤ δ^((1 : ℝ)/3) ∧ δ^((1 : ℝ)/3) ≤ 1/100 ∧
      20*(H : ℝ)*δ^((1 : ℝ)/3) ≤ 1/2 := by
  let Q : ℝ := 520*(m : ℝ)^5*(stepFactor m B)^H
  have hQ := resolution_coefficient_lower hm B hB H
  have heta : 0 ≤ δ^((1 : ℝ)/3) := Real.rpow_nonneg hδ.le _
  have hpow : δ^((1 : ℝ)/3) ≤ δ^((1 : ℝ)/12) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ.1
  have hprod : Q*δ^((1 : ℝ)/3) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow hQpos.le).trans
      (rpow_resolution_mul_le_one hδ hQpos hres)
  have h100 : 100*δ^((1 : ℝ)/3) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (show 100 ≤ Q from le_trans (by norm_num) hQ.1) heta).trans hprod
  have h40 : 40*(H : ℝ)*δ^((1 : ℝ)/3) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hQ.2 heta).trans hprod
  exact ⟨heta, by linarith, by linarith⟩

end AcceleratedLogConcave.Oracle.RecursiveCall
