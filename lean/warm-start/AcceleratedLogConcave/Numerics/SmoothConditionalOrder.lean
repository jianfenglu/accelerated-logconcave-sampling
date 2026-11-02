import AcceleratedLogConcave.Numerics.SmoothConditionalMaterial

/-! Visible dimension dependence and universal exp(O(m log m)) growth of
the conditional material budget. No compactness-selected constants occur. -/
noncomputable section
open Set MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.ConditionalSmoothing
open Tensor.ActualCoefficientIntegrability

def conditionalOrderEnvelope (m : ℕ) : ℝ := (12*(m:ℝ))^(12*m)

theorem conditionalOrderEnvelope_nonneg (m : ℕ) : 0 ≤ conditionalOrderEnvelope m := by
  unfold conditionalOrderEnvelope
  positivity

theorem materialOrderFactor_dimension (D k : ℕ) :
    materialOrderFactor D k = Real.sqrt (D:ℝ)*materialOrderFactor 1 k := by
  have he : materialRmsNumeric D (3+3*k) = (D:ℝ)*materialRmsNumeric 1 (3+3*k) := by
    simp only [materialRmsNumeric, Nat.cast_one, one_mul]
    ring
  unfold materialOrderFactor
  rw [he, Real.sqrt_mul (by positivity)]
  ring

/-- A numerical universal envelope with C=12. -/
theorem materialOrderFactor_one_le (k : ℕ) :
    materialOrderFactor 1 k ≤ conditionalOrderEnvelope (k+1) := by
  let m := k+1
  let B : ℝ := 12*(m:ℝ)
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have h6 : ((2*(3+3*k):ℕ):ℝ) ≤ B := by dsimp [B,m]; push_cast; linarith
  have hexp : 2*(3+3*k) = 6*m := by dsimp [m]; omega
  have hp : (((2*(3+3*k):ℕ):ℝ)^(2*(3+3*k))) ≤ B^(6*m) := by
    rw [hexp]
    exact pow_le_pow_left₀ (by positivity) (by simpa only [hexp] using h6) _
  have htwo : (2:ℝ)^(2*(3+3*k)) ≤ B^(6*m) := by
    rw [hexp]
    apply pow_le_pow_left₀ (by norm_num)
    dsimp [B]
    linarith
  have hfac : ((2*(3+3*k)).factorial:ℝ) ≤ B^(6*m) := by
    have hf : ((2*(3+3*k)).factorial:ℝ) ≤ ((2*(3+3*k):ℕ):ℝ)^(2*(3+3*k)) := by
      exact_mod_cast Nat.factorial_le_pow (2*(3+3*k))
    exact hf.trans hp
  have hnum : materialRmsNumeric 1 (3+3*k) ≤ (B^(9*m))^2 := by
    simp only [materialRmsNumeric, Nat.cast_one, one_mul]
    calc
      _ ≤ B^(6*m)*B^(6*m)*B^(6*m) :=
        mul_le_mul (mul_le_mul hp htwo (by positivity) (by positivity)) hfac
          (by positivity) (by positivity)
      _ = _ := by rw [← pow_add, ← pow_add, ← pow_mul]; congr 1; omega
  have hsqrt : Real.sqrt (materialRmsNumeric 1 (3+3*k)) ≤ B^(9*m) :=
    (Real.sqrt_le_iff).2 ⟨by positivity,hnum⟩
  have hbase : 3*(3+3*(k:ℝ)+1)^2 ≤ B^2 := by
    dsimp [B,m]
    push_cast
    nlinarith [sq_nonneg (k:ℝ), Nat.cast_nonneg (α := ℝ) k]
  have hmass : (3*(3+3*(k:ℝ)+1)^2)^k ≤ B^(2*m) := by
    calc
      _ ≤ (B^2)^k := pow_le_pow_left₀ (by positivity) hbase _
      _ = B^(2*k) := by rw [pow_mul]
      _ ≤ B^(2*m) := pow_le_pow_right₀ hB (by dsimp [m]; omega)
  unfold materialOrderFactor conditionalOrderEnvelope
  calc
    _ ≤ B^(2*m)*B^(9*m) := mul_le_mul hmass hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = B^(11*m) := by rw [←pow_add]; congr 1; omega
    _ ≤ B^(12*m) := pow_le_pow_right₀ hB (by omega)

theorem materialOrderFactor_le (D k : ℕ) :
    materialOrderFactor D k ≤ Real.sqrt (D:ℝ)*conditionalOrderEnvelope (k+1) := by
  rw [materialOrderFactor_dimension]
  exact mul_le_mul_of_nonneg_left (materialOrderFactor_one_le k) (Real.sqrt_nonneg _)

end AcceleratedLogConcave.Numerics.ConditionalSmoothing
