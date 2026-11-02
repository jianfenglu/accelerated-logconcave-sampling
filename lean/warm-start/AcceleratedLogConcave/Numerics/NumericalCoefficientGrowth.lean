import AcceleratedLogConcave.Numerics.SmoothConditionalOrder
import AcceleratedLogConcave.Tensor.PhaseBudgetAggregation

/-! Elementary growth bounds for the literal tensor and conditional-material
coefficients. The factorial is bounded by its defining order raised to that
order, so no asymptotic assumption on the row coefficients is introduced. -/
noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.NumericalCoefficientGrowth
open Tensor.AdjointReduction.PhaseBudget Tensor.ActualCoefficientIntegrability
open ConditionalSmoothing

/-- The factorial in the actual phase budget is absorbed into a second copy
of its elementary base. -/
theorem phaseQ_le_power {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    Q c n ≤ (c * (((16 * (n + 1) : ℕ) : ℝ) ^ 2)) ^ (16 * (n + 1)) := by
  let N : ℕ := 16 * (n + 1)
  have hf : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by
    exact_mod_cast Nat.factorial_le_pow N
  change (N : ℝ) ^ N * c ^ N * (N.factorial : ℝ) ≤
    (c * (N : ℝ) ^ 2) ^ N
  calc
    _ ≤ (N : ℝ) ^ N * c ^ N * (N : ℝ) ^ N :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by rw [mul_pow, pow_mul]; ring

/-- Explicit specialization of the only two phase budgets occurring in the
smooth row and angle payments. -/
theorem phaseQ_128_le (n : ℕ) :
    Q 128 n ≤ (128 * (((16 * (n + 1) : ℕ) : ℝ) ^ 2)) ^ (16 * (n + 1)) :=
  phaseQ_le_power (by norm_num) n

theorem phaseQ_256_le (n : ℕ) :
    Q 256 n ≤ (256 * (((16 * (n + 1) : ℕ) : ℝ) ^ 2)) ^ (16 * (n + 1)) :=
  phaseQ_le_power (by norm_num) n

/-- Exact RMS budget with its factorial replaced by an elementary power. -/
theorem materialRmsNumeric_le_power (D s : ℕ) :
    materialRmsNumeric D s ≤
      (D : ℝ) * (2 * (((2 * s : ℕ) : ℝ) ^ 2)) ^ (2 * s) := by
  have hf : (((2 * s).factorial : ℝ)) ≤ (((2 * s : ℕ) : ℝ)) ^ (2 * s) := by
    exact_mod_cast Nat.factorial_le_pow (2 * s)
  unfold materialRmsNumeric
  calc
    _ ≤ (D : ℝ) * (((2 * s : ℕ) : ℝ)) ^ (2 * s) * 2 ^ (2 * s) *
        (((2 * s : ℕ) : ℝ)) ^ (2 * s) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by rw [mul_pow, pow_mul]; ring


theorem log_two_le_log_succ (n : ℕ) :
    Real.log 2 ≤ Real.log ((n + 2 : ℕ) : ℝ) := by
  apply Real.log_le_log (by norm_num)
  exact_mod_cast (show 2 ≤ n + 2 by omega)

theorem log_succ_pos (n : ℕ) :
    0 < Real.log ((n + 2 : ℕ) : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < n + 2 by omega)

private theorem log_256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
  conv_lhs => rw [show (256 : ℝ) = 2 ^ 8 by norm_num]
  rw [Real.log_pow]
  norm_num

private theorem log_16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
  conv_lhs => rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
  rw [Real.log_pow]
  norm_num

/-- The literal phase factor has an explicit logarithmic growth bound,
uniform over both constants 128 and 256 that occur in the smooth row. -/
theorem phaseQ_log_le {c : ℝ} (hc : 1 ≤ c) (hc256 : c ≤ 256) (n : ℕ) :
    Real.log (Q c n) ≤
      288 * ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) := by
  let N : ℕ := 16 * (n + 1)
  let M : ℝ := ((n + 2 : ℕ) : ℝ)
  have hN : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by dsimp [N]; omega)
  have hM : 0 < M := by dsimp [M]; positivity
  have hcpos : 0 < c := by linarith
  have hbase : 0 < c * (N : ℝ) ^ 2 := by positivity
  have hQ : 0 < Q c n := by unfold Q; positivity
  have hlogM : 0 < Real.log M := by exact log_succ_pos n
  have hlog2 : Real.log 2 ≤ Real.log M := log_two_le_log_succ n
  have hlogc : Real.log c ≤ 8 * Real.log M := by
    calc
      Real.log c ≤ Real.log (256 : ℝ) := Real.log_le_log hcpos hc256
      _ = 8 * Real.log 2 := log_256
      _ ≤ 8 * Real.log M := by gcongr
  have hNle : (N : ℝ) ≤ 16 * M := by
    dsimp [N, M]
    push_cast
    nlinarith
  have hlogN : Real.log (N : ℝ) ≤ 5 * Real.log M := by
    calc
      Real.log (N : ℝ) ≤ Real.log (16 * M) := Real.log_le_log hN hNle
      _ = Real.log 16 + Real.log M := Real.log_mul (by norm_num) hM.ne'
      _ = 4 * Real.log 2 + Real.log M := by rw [log_16]
      _ ≤ 5 * Real.log M := by linarith
  have hbaseLog : Real.log (c * (N : ℝ) ^ 2) ≤ 18 * Real.log M := by
    rw [Real.log_mul hcpos.ne' (pow_ne_zero _ hN.ne'), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have h := Real.log_le_log hQ (phaseQ_le_power hcpos.le n)
  change Real.log (Q c n) ≤ Real.log ((c * (N : ℝ) ^ 2) ^ N) at h
  rw [Real.log_pow] at h
  have hN0 : 0 ≤ (N : ℝ) := hN.le
  have hmul := mul_le_mul_of_nonneg_left hbaseLog hN0
  have hNcast : (N : ℝ) = 16 * ((n + 1 : ℕ) : ℝ) := by dsimp [N]; push_cast; ring
  calc
    Real.log (Q c n) ≤ (N : ℝ) * Real.log (c * (N : ℝ) ^ 2) := h
    _ ≤ (N : ℝ) * (18 * Real.log M) := hmul
    _ = 288 * ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) := by
      rw [hNcast]
      dsimp [M]
      ring

theorem phaseQ_128_log_le (n : ℕ) :
    Real.log (Q 128 n) ≤
      288 * ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) :=
  phaseQ_log_le (by norm_num) (by norm_num) n

theorem phaseQ_256_log_le (n : ℕ) :
    Real.log (Q 256 n) ≤
      288 * ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) :=
  phaseQ_log_le (by norm_num) (by norm_num) n


/-- Logarithmic growth of the literal conditional-order envelope. -/
theorem conditionalOrderEnvelope_log_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (conditionalOrderEnvelope m) ≤
      60 * (m : ℝ) * Real.log ((m + 2 : ℕ) : ℝ) := by
  let M : ℝ := ((m + 2 : ℕ) : ℝ)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlog2 : Real.log 2 ≤ Real.log M := log_two_le_log_succ m
  have h12 : Real.log (12 : ℝ) ≤ 4 * Real.log M := by
    calc
      Real.log (12 : ℝ) ≤ Real.log 16 :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 4 * Real.log 2 := log_16
      _ ≤ 4 * Real.log M := by gcongr
  have hmM : (m : ℝ) ≤ M := by dsimp [M]; push_cast; linarith
  have hlogm : Real.log (m : ℝ) ≤ Real.log M := Real.log_le_log hmpos hmM
  unfold conditionalOrderEnvelope
  rw [Real.log_pow, Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) hmpos.ne']
  have hcast : ((12 * m : ℕ) : ℝ) = 12 * (m : ℝ) := by push_cast; ring
  rw [hcast]
  nlinarith

/-- The actual one-dimensional RMS coefficient has logarithm at most
`10s log(s+2)`. Dimension enters the exact budget as a separate factor. -/
theorem materialRmsNumeric_one_log_le (s : ℕ) :
    Real.log (materialRmsNumeric 1 s) ≤
      10 * (s : ℝ) * Real.log ((s + 2 : ℕ) : ℝ) := by
  rcases eq_or_lt_of_le (Nat.zero_le s) with hs | hs
  · subst s
    norm_num [materialRmsNumeric]
  let N : ℕ := 2 * s
  let M : ℝ := ((s + 2 : ℕ) : ℝ)
  have hN : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by dsimp [N]; omega)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlog2 : Real.log 2 ≤ Real.log M := log_two_le_log_succ s
  have hNle : (N : ℝ) ≤ 2 * M := by dsimp [N, M]; push_cast; linarith
  have hlogN : Real.log (N : ℝ) ≤ 2 * Real.log M := by
    calc
      Real.log (N : ℝ) ≤ Real.log (2 * M) := Real.log_le_log hN hNle
      _ = Real.log 2 + Real.log M := Real.log_mul (by norm_num) hM.ne'
      _ ≤ 2 * Real.log M := by linarith
  have hbase : 0 < 2 * (N : ℝ) ^ 2 := by positivity
  have hnum : 0 < materialRmsNumeric 1 s := by
    unfold materialRmsNumeric
    positivity
  have h := Real.log_le_log hnum (materialRmsNumeric_le_power 1 s)
  simp only [Nat.cast_one, one_mul] at h
  change Real.log (materialRmsNumeric 1 s) ≤ Real.log ((2 * (N : ℝ) ^ 2) ^ N) at h
  rw [Real.log_pow] at h
  have hbaselog : Real.log (2 * (N : ℝ) ^ 2) ≤ 5 * Real.log M := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hN.ne'),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hbaselog hN.le
  have hNcast : (N : ℝ) = 2 * (s : ℝ) := by dsimp [N]; push_cast; ring
  calc
    Real.log (materialRmsNumeric 1 s) ≤ (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2) := h
    _ ≤ (N : ℝ) * (5 * Real.log M) := hmul
    _ = 10 * (s : ℝ) * Real.log ((s + 2 : ℕ) : ℝ) := by
      rw [hNcast]
      dsimp [M]
      ring


/-- Dimension is exactly a multiplicative factor in the material RMS budget;
its logarithm is the only dimension dependence of this numerical factor. -/
theorem materialRmsNumeric_log_le (D s : ℕ) (hD : 1 ≤ D) :
    Real.log (materialRmsNumeric D s) ≤
      Real.log (D : ℝ) +
        10 * (s : ℝ) * Real.log ((s + 2 : ℕ) : ℝ) := by
  have hDpos : (D : ℝ) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 by omega)
  have hunit : materialRmsNumeric 1 s ≠ 0 := by
    cases s with
    | zero => norm_num [materialRmsNumeric]
    | succ s =>
      unfold materialRmsNumeric
      simp only [Nat.cast_one, one_mul]
      positivity
  have hfactor : materialRmsNumeric D s =
      (D : ℝ) * materialRmsNumeric 1 s := by
    unfold materialRmsNumeric
    push_cast
    ring
  rw [hfactor, Real.log_mul hDpos hunit]
  linarith [materialRmsNumeric_one_log_le s]


private theorem log_eight : Real.log (8 : ℝ) = 3 * Real.log 2 := by
  conv_lhs => rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
  rw [Real.log_pow]
  norm_num

private theorem row_log_argument (m : ℕ) {a : ℕ}
    (ha : a ≤ 5 * m + 8) :
    Real.log (a : ℝ) ≤
      4 * Real.log ((m + 2 : ℕ) : ℝ) := by
  let M : ℝ := ((m + 2 : ℕ) : ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlog2 := log_two_le_log_succ m
  have ha8 : (a : ℝ) ≤ 8 * M := by
    dsimp [M]
    exact_mod_cast (show a ≤ 8 * (m + 2) by omega)
  by_cases ha0 : a = 0
  · subst a
    simp only [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (by norm_num) (log_succ_pos m).le
  have hapos : 0 < (a : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero ha0)
  calc
    Real.log (a : ℝ) ≤ Real.log (8 * M) := Real.log_le_log hapos ha8
    _ = Real.log 8 + Real.log M := Real.log_mul (by norm_num) hM.ne'
    _ = 3 * Real.log 2 + Real.log M := by rw [log_eight]
    _ ≤ 4 * Real.log M := by linarith

/-- The angle coefficient uses the literal index `5m+1`. -/
theorem phaseQ_angle_log_le {c : ℝ} (hc : 1 ≤ c) (hc256 : c ≤ 256)
    (m : ℕ) :
    Real.log (Q c (5 * m + 1)) ≤
      5760 * ((m + 1 : ℕ) : ℝ) * Real.log ((m + 2 : ℕ) : ℝ) := by
  have h := phaseQ_log_le hc hc256 (5 * m + 1)
  have hlog := row_log_argument m (show (5 * m + 1) + 2 ≤ 5 * m + 8 by omega)
  have hN : (((5 * m + 1) + 1 : ℕ) : ℝ) ≤ 5 * ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show (5 * m + 1) + 1 ≤ 5 * (m + 1) by omega)
  have hlog0 : 0 ≤ Real.log ((m + 2 : ℕ) : ℝ) :=
    (log_succ_pos m).le
  have hNm : 0 ≤ (((5 * m + 1) + 1 : ℕ) : ℝ) := by positivity
  calc
    Real.log (Q c (5 * m + 1)) ≤
      288 * (((5 * m + 1) + 1 : ℕ) : ℝ) *
        Real.log (((5 * m + 1) + 2 : ℕ) : ℝ) := h
    _ ≤ 288 * (((5 * m + 1) + 1 : ℕ) : ℝ) *
        (4 * Real.log ((m + 2 : ℕ) : ℝ)) := by gcongr
    _ ≤ 288 * (5 * ((m + 1 : ℕ) : ℝ)) *
        (4 * Real.log ((m + 2 : ℕ) : ℝ)) := by gcongr
    _ = _ := by ring

/-- The state coefficient uses the literal index `5(m+1)+1`. -/
theorem phaseQ_state_log_le {c : ℝ} (hc : 1 ≤ c) (hc256 : c ≤ 256)
    (m : ℕ) :
    Real.log (Q c (5 * (m + 1) + 1)) ≤
      8064 * ((m + 1 : ℕ) : ℝ) * Real.log ((m + 2 : ℕ) : ℝ) := by
  have h := phaseQ_log_le hc hc256 (5 * (m + 1) + 1)
  have hlog := row_log_argument m
    (show (5 * (m + 1) + 1) + 2 ≤ 5 * m + 8 by omega)
  have hN : (((5 * (m + 1) + 1) + 1 : ℕ) : ℝ) ≤
      7 * ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show (5 * (m + 1) + 1) + 1 ≤ 7 * (m + 1) by omega)
  calc
    Real.log (Q c (5 * (m + 1) + 1)) ≤
      288 * (((5 * (m + 1) + 1) + 1 : ℕ) : ℝ) *
        Real.log (((5 * (m + 1) + 1) + 2 : ℕ) : ℝ) := h
    _ ≤ 288 * (((5 * (m + 1) + 1) + 1 : ℕ) : ℝ) *
        (4 * Real.log ((m + 2 : ℕ) : ℝ)) := by gcongr
    _ ≤ 288 * (7 * ((m + 1 : ℕ) : ℝ)) *
        (4 * Real.log ((m + 2 : ℕ) : ℝ)) := by gcongr
    _ = _ := by ring

end AcceleratedLogConcave.Numerics.NumericalCoefficientGrowth
