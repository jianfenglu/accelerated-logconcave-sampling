import AcceleratedLogConcave.Numerics.SmoothInventoryDimension
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-! Explicit logarithmic growth of the literal m-only row inventory. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SmoothInventoryDimension
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph AffineGraph.MeanGeometry
open SmoothQuantitativeAssembly SmoothQuadraturePayments SmoothRowPayments SmoothRowInventory
open SmoothAnglePayment Tensor.ActualCoefficientIntegrability ConditionalSmoothing


private theorem rms_one_pos (s : ℕ) : 0 < materialRmsNumeric 1 s := by
  cases s with
  | zero => norm_num [materialRmsNumeric]
  | succ s =>
    unfold materialRmsNumeric
    simp only [Nat.cast_one, one_mul]
    positivity

private theorem factorial_log_le (k : ℕ) :
    Real.log (k.factorial : ℝ) ≤
      (k : ℝ)*Real.log ((k+2 : ℕ) : ℝ) := by
  have hf : (0:ℝ) < (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hpow : (k.factorial:ℝ) ≤ (k:ℝ)^k := by
    exact_mod_cast Nat.factorial_le_pow k
  have hk : Real.log (k:ℝ) ≤ Real.log ((k+2:ℕ):ℝ) := by
    by_cases h0 : k = 0
    · subst k
      simpa using (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    · apply Real.log_le_log
      · exact_mod_cast Nat.pos_of_ne_zero h0
      · exact_mod_cast (show k ≤ k+2 by omega)
  calc
    Real.log (k.factorial : ℝ) ≤ Real.log ((k:ℝ)^k) :=
      Real.log_le_log hf hpow
    _ = (k:ℝ)*Real.log (k:ℝ) := by rw [Real.log_pow]
    _ ≤ (k:ℝ)*Real.log ((k+2:ℕ):ℝ) :=
      mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg k)

private theorem wordMass_log_le (k : ℕ) :
    Real.log (materialWordMassBase k) ≤
      7*Real.log ((k+2:ℕ):ℝ) := by
  let M : ℝ := ((k+2:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlog2 : Real.log 2 ≤ Real.log M :=
    NumericalCoefficientGrowth.log_two_le_log_succ k
  have h27 : Real.log (27:ℝ) ≤ 5*Real.log M := by
    calc
      Real.log (27:ℝ) ≤ Real.log (32:ℝ) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 5*Real.log 2 := by
        conv_lhs => rw [show (32:ℝ)=2^5 by norm_num]
        rw [Real.log_pow]
        norm_num
      _ ≤ 5*Real.log M := by gcongr
  have hkp : 0 < (k:ℝ)+1 := by positivity
  have hkm : (k:ℝ)+1 ≤ M := by dsimp [M]; push_cast; linarith
  have hlogk := Real.log_le_log hkp hkm
  unfold materialWordMassBase
  rw [Real.log_mul (by norm_num : (27:ℝ) ≠ 0) (pow_ne_zero _ hkp.ne'),
    Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- The factorial, literal word mass, and RMS factor in the actual kernel
coefficient together grow at most exponentially in `k log(k+2)`. -/
theorem kernelUnit_log_le (k : ℕ) :
    Real.log (kernelUnit k) ≤
      54*((k+1:ℕ):ℝ)*Real.log ((k+2:ℕ):ℝ) := by
  let s : ℕ := 3*k-1
  let M : ℝ := ((k+2:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlogM : 0 < Real.log M := by
    exact NumericalCoefficientGrowth.log_succ_pos k
  have hlog2 : Real.log 2 ≤ Real.log M :=
    NumericalCoefficientGrowth.log_two_le_log_succ k
  have hfac : 0 < (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hword : 0 < materialWordMassBase k :=
    lt_of_lt_of_le (by norm_num) (materialWordMassBase_one_le k)
  have hrms := rms_one_pos s
  have hsqrt : 0 < Real.sqrt (materialRmsNumeric 1 s) := Real.sqrt_pos.2 hrms
  have hlogS : Real.log ((s+2:ℕ):ℝ) ≤ 3*Real.log M := by
    have hsM : ((s+2:ℕ):ℝ) ≤ 4*M := by
      dsimp [s,M]
      exact_mod_cast (show (3*k-1)+2 ≤ 4*(k+2) by omega)
    calc
      Real.log ((s+2:ℕ):ℝ) ≤ Real.log (4*M) :=
        Real.log_le_log (by positivity) hsM
      _ = Real.log 4 + Real.log M := Real.log_mul (by norm_num) hM.ne'
      _ = 2*Real.log 2 + Real.log M := by
        conv_lhs => rw [show (4:ℝ)=2^2 by norm_num]
        rw [Real.log_pow]
        ring
      _ ≤ 3*Real.log M := by linarith
  have hsM : (s:ℝ) ≤ 3*((k+1:ℕ):ℝ) := by
    exact_mod_cast (show s ≤ 3*(k+1) by dsimp [s]; omega)
  have hlogS0 : 0 ≤ Real.log ((s+2:ℕ):ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ s+2 by omega)
  have hrmslog := NumericalCoefficientGrowth.materialRmsNumeric_one_log_le s
  have hrmsBound : Real.log (materialRmsNumeric 1 s) ≤
      90*((k+1:ℕ):ℝ)*Real.log M := by
    calc
      _ ≤ 10*(s:ℝ)*Real.log ((s+2:ℕ):ℝ) := hrmslog
      _ ≤ 10*(s:ℝ)*(3*Real.log M) := by gcongr
      _ ≤ 10*(3*((k+1:ℕ):ℝ))*(3*Real.log M) := by gcongr
      _ = _ := by ring
  have hexp : Real.log (Real.exp (1/2:ℝ)) = 1/2 := Real.log_exp _
  have hunitpos : 0 < kernelUnit k := by
    unfold kernelUnit
    positivity
  unfold kernelUnit
  rw [show Real.exp (1/2:ℝ) * (k.factorial:ℝ) *
      materialWordMassBase k ^ k * Real.sqrt (materialRmsNumeric 1 s) =
      Real.exp (1/2:ℝ) * ((k.factorial:ℝ) *
        (materialWordMassBase k ^ k * Real.sqrt (materialRmsNumeric 1 s))) by ring,
    Real.log_mul (Real.exp_pos _).ne'
      (mul_ne_zero hfac.ne' (mul_ne_zero (pow_ne_zero _ hword.ne') hsqrt.ne')),
    Real.log_mul hfac.ne' (mul_ne_zero (pow_ne_zero _ hword.ne') hsqrt.ne'),
    Real.log_mul (pow_ne_zero _ hword.ne') hsqrt.ne',
    Real.log_pow, Real.log_sqrt hrms.le, hexp]
  have hf := factorial_log_le k
  have hw := wordMass_log_le k
  have hk : (k:ℝ) ≤ ((k+1:ℕ):ℝ) := by push_cast; linarith
  have hwordBound : (k:ℝ)*Real.log (materialWordMassBase k) ≤
      7*((k+1:ℕ):ℝ)*Real.log M := by
    calc
      _ ≤ (k:ℝ)*(7*Real.log M) :=
        mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg k)
      _ ≤ ((k+1:ℕ):ℝ)*(7*Real.log M) := by gcongr
      _ = _ := by ring
  have hfacBound : Real.log (k.factorial:ℝ) ≤
      ((k+1:ℕ):ℝ)*Real.log M :=
    hf.trans (mul_le_mul_of_nonneg_right hk hlogM.le)
  have hhalf : (1:ℝ)/2 ≤ ((k+1:ℕ):ℝ)*Real.log M := by
    have h1 : (1:ℝ) ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast (show 1≤k+1 by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) hlogM.le,
      Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)]
  linarith


/-- The backward material factor has the same explicit `k log k` growth. -/
theorem backwardUnit_log_le (k : ℕ) :
    Real.log (backwardUnit k) ≤
      53*((k+1:ℕ):ℝ)*Real.log ((k+2:ℕ):ℝ) := by
  let s : ℕ := 3+3*k
  let M : ℝ := ((k+2:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlogM : 0 < Real.log M :=
    NumericalCoefficientGrowth.log_succ_pos k
  have hlog2 : Real.log 2 ≤ Real.log M :=
    NumericalCoefficientGrowth.log_two_le_log_succ k
  have h3 : Real.log (3:ℝ) ≤ 2*Real.log M := by
    calc
      Real.log (3:ℝ) ≤ Real.log (4:ℝ) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 2*Real.log 2 := by
        conv_lhs => rw [show (4:ℝ)=2^2 by norm_num]
        rw [Real.log_pow]
        norm_num
      _ ≤ 2*Real.log M := by gcongr
  have hlinear : 0 < 3*(k:ℝ)+4 := by positivity
  have hlinearBound : 3*(k:ℝ)+4 ≤ 4*M := by
    dsimp [M]
    push_cast
    linarith
  have hloglinear : Real.log (3*(k:ℝ)+4) ≤ 3*Real.log M := by
    calc
      Real.log (3*(k:ℝ)+4) ≤ Real.log (4*M) :=
        Real.log_le_log hlinear hlinearBound
      _ = Real.log 4 + Real.log M := Real.log_mul (by norm_num) hM.ne'
      _ = 2*Real.log 2 + Real.log M := by
        conv_lhs => rw [show (4:ℝ)=2^2 by norm_num]
        rw [Real.log_pow]
        ring
      _ ≤ 3*Real.log M := by linarith
  have hmass : 0 < 3*(3+3*(k:ℝ)+1)^2 := by positivity
  have hmassLog : Real.log (3*(3+3*(k:ℝ)+1)^2) ≤
      8*Real.log M := by
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0)
      (pow_ne_zero _ (by linarith : (3+3*(k:ℝ)+1) ≠ 0)),
      Real.log_pow]
    have he : 3+3*(k:ℝ)+1=3*(k:ℝ)+4 := by ring
    rw [he]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hsM : (s:ℝ) ≤ 3*((k+1:ℕ):ℝ) := by
    dsimp [s]
    push_cast
    nlinarith
  have hsarg : ((s+2:ℕ):ℝ) ≤ 4*M := by
    dsimp [s,M]
    exact_mod_cast (show 3+3*k+2 ≤ 4*(k+2) by omega)
  have hlogS : Real.log ((s+2:ℕ):ℝ) ≤ 3*Real.log M := by
    calc
      _ ≤ Real.log (4*M) := Real.log_le_log (by positivity) hsarg
      _ = Real.log 4 + Real.log M := Real.log_mul (by norm_num) hM.ne'
      _ = 2*Real.log 2 + Real.log M := by
        conv_lhs => rw [show (4:ℝ)=2^2 by norm_num]
        rw [Real.log_pow]
        ring
      _ ≤ 3*Real.log M := by linarith
  have hrms := rms_one_pos s
  have hsqrt : 0 < Real.sqrt (materialRmsNumeric 1 s) :=
    Real.sqrt_pos.2 hrms
  have hrmsBound : Real.log (materialRmsNumeric 1 s) ≤
      90*((k+1:ℕ):ℝ)*Real.log M := by
    calc
      _ ≤ 10*(s:ℝ)*Real.log ((s+2:ℕ):ℝ) :=
        NumericalCoefficientGrowth.materialRmsNumeric_one_log_le s
      _ ≤ 10*(s:ℝ)*(3*Real.log M) := by gcongr
      _ ≤ 10*(3*((k+1:ℕ):ℝ))*(3*Real.log M) := by gcongr
      _ = _ := by ring
  unfold backwardUnit
  rw [Real.log_mul (pow_ne_zero _ hmass.ne') hsqrt.ne',
    Real.log_pow, Real.log_sqrt hrms.le]
  have hk : (k:ℝ) ≤ ((k+1:ℕ):ℝ) := by push_cast; linarith
  have hleft : (k:ℝ)*Real.log (3*(3+3*(k:ℝ)+1)^2) ≤
      8*((k+1:ℕ):ℝ)*Real.log M := by
    calc
      _ ≤ (k:ℝ)*(8*Real.log M) :=
        mul_le_mul_of_nonneg_left hmassLog (Nat.cast_nonneg k)
      _ ≤ ((k+1:ℕ):ℝ)*(8*Real.log M) := by gcongr
      _ = _ := by ring
  linarith


private theorem factorial_log_nonneg (m : ℕ) :
    0 ≤ Real.log (m.factorial:ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ m.factorial by have := Nat.factorial_pos m; omega)

private theorem log_div_factorial_le {a : ℝ} (ha : 0 < a) (m : ℕ) :
    Real.log (a/(m.factorial:ℝ)) ≤ Real.log a := by
  rw [Real.log_div ha.ne' (by exact_mod_cast (Nat.factorial_pos m).ne')]
  linarith [factorial_log_nonneg m]

private theorem log_two_le_log_plus_three (m : ℕ) :
    Real.log 2 ≤ Real.log ((m+3:ℕ):ℝ) := by
  apply Real.log_le_log (by norm_num)
  exact_mod_cast (show 2 ≤ m+3 by omega)

private theorem phase_sqrt_log_le {c : ℝ} (hc : 1 ≤ c) (_hc256 : c ≤ 256)
    (n : ℕ) {L : ℝ} (hQ : Real.log (Tensor.AdjointReduction.PhaseBudget.Q c n) ≤ L)
    {M : ℝ} (_hM : 0 < M) (hlog2 : Real.log 2 ≤ Real.log M) :
    Real.log (Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q c n)) ≤
      (Real.log M + L)/2 := by
  have hq : 0 < Tensor.AdjointReduction.PhaseBudget.Q c n := by
    unfold Tensor.AdjointReduction.PhaseBudget.Q
    have hcpos : 0 < c := by linarith
    positivity
  have h2q : 0 < 2*Tensor.AdjointReduction.PhaseBudget.Q c n := by positivity
  rw [Real.log_sqrt h2q.le,
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hq.ne']
  linarith

/-- The state phase term uses the largest literal index in the inventory. -/
theorem stateUnit_log_le (m : ℕ) :
    Real.log (stateUnit m) ≤
      4034*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  let M : ℝ := ((m+3:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlogM : 0 < Real.log M := by
    apply Real.log_pos
    dsimp [M]
    exact_mod_cast (show 1 < m+3 by omega)
  have hlog2 := log_two_le_log_plus_three m
  have hQ := NumericalCoefficientGrowth.phaseQ_state_log_le
    (by norm_num : (1:ℝ)≤128) (by norm_num : (128:ℝ)≤256) m
  have hbase : 0 < Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q 128
      (5*(m+1)+1)) := by
    apply Real.sqrt_pos.2
    unfold Tensor.AdjointReduction.PhaseBudget.Q
    positivity
  have hsqrt := phase_sqrt_log_le
    (by norm_num : (1:ℝ)≤128) (by norm_num : (128:ℝ)≤256)
    (5*(m+1)+1) hQ hM hlog2
  have hMbound : ((m+1:ℕ):ℝ) ≤ ((m+3:ℕ):ℝ) := by exact_mod_cast (show m+1≤m+3 by omega)
  have hlogarg : Real.log ((m+2:ℕ):ℝ) ≤ Real.log M := by
    apply Real.log_le_log (by positivity)
    dsimp [M]
    exact_mod_cast (show m+2≤m+3 by omega)
  have hX : ((m+1:ℕ):ℝ)*Real.log ((m+2:ℕ):ℝ) ≤
      ((m+3:ℕ):ℝ)*Real.log M := by
    exact (mul_le_mul_of_nonneg_left hlogarg (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hMbound hlogM.le)
  have h1 : Real.log 2 ≤ ((m+3:ℕ):ℝ)*Real.log M := by
    have hm1 : (1:ℝ) ≤ ((m+3:ℕ):ℝ) := by exact_mod_cast (show 1≤m+3 by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) hlogM.le]
  unfold stateUnit
  have hnum : 0 < 2*Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q 128
      (5*(m+1)+1)) := by positivity
  have hdiv := log_div_factorial_le hnum m
  have hlognum : Real.log (2*Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q 128
      (5*(m+1)+1))) =
      Real.log 2 + Real.log (Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q 128
        (5*(m+1)+1))) :=
    Real.log_mul (by norm_num) hbase.ne'
  rw [hlognum] at hdiv
  have hlogMbound : Real.log M ≤ ((m+3:ℕ):ℝ)*Real.log M := by
    have hm1 : (1:ℝ) ≤ ((m+3:ℕ):ℝ) := by exact_mod_cast (show 1≤m+3 by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) hlogM.le]
  have hQcomp : 8064*((m+1:ℕ):ℝ)*Real.log ((m+2:ℕ):ℝ) ≤
      8064*((m+3:ℕ):ℝ)*Real.log M := by nlinarith [hX]
  linarith


/-- Center-score term, using the literal lower phase index. -/
theorem scoreUnit_log_le (m : ℕ) :
    Real.log (scoreUnit m) ≤
      2883*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  let M : ℝ := ((m+3:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlogM : 0 < Real.log M := by
    apply Real.log_pos
    dsimp [M]
    exact_mod_cast (show 1 < m+3 by omega)
  have hlog2 := log_two_le_log_plus_three m
  have hQ := NumericalCoefficientGrowth.phaseQ_angle_log_le
    (by norm_num : (1:ℝ)≤128) (by norm_num : (128:ℝ)≤256) m
  have hbase : 0 < Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q 128
      (5*m+1)) := by
    apply Real.sqrt_pos.2
    unfold Tensor.AdjointReduction.PhaseBudget.Q
    positivity
  have hsqrt := phase_sqrt_log_le
    (by norm_num : (1:ℝ)≤128) (by norm_num : (128:ℝ)≤256)
    (5*m+1) hQ hM hlog2
  have hMbound : ((m+1:ℕ):ℝ) ≤ ((m+3:ℕ):ℝ) := by exact_mod_cast (show m+1≤m+3 by omega)
  have hlogarg : Real.log ((m+2:ℕ):ℝ) ≤ Real.log M := by
    apply Real.log_le_log (by positivity)
    dsimp [M]
    exact_mod_cast (show m+2≤m+3 by omega)
  have hX : ((m+1:ℕ):ℝ)*Real.log ((m+2:ℕ):ℝ) ≤
      ((m+3:ℕ):ℝ)*Real.log M := by
    exact (mul_le_mul_of_nonneg_left hlogarg (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hMbound hlogM.le)
  have hM1 : (1:ℝ) ≤ ((m+3:ℕ):ℝ) := by exact_mod_cast (show 1≤m+3 by omega)
  have hlogMbound : Real.log M ≤ ((m+3:ℕ):ℝ)*Real.log M := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hM1) hlogM.le]
  have hlog4 : Real.log (4:ℝ) ≤ 2*((m+3:ℕ):ℝ)*Real.log M := by
    have he : Real.log (4:ℝ)=2*Real.log 2 := by
      conv_lhs => rw [show (4:ℝ)=2^2 by norm_num]
      rw [Real.log_pow]
      norm_num
    rw [he]
    nlinarith [mul_nonneg (sub_nonneg.mpr hM1) hlogM.le]
  unfold scoreUnit
  have hnum : 0 < 4*Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q 128
      (5*m+1)) := by positivity
  have hdiv := log_div_factorial_le hnum m
  have hlognum : Real.log (4*Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q 128
      (5*m+1))) =
      Real.log 4 + Real.log (Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q 128
        (5*m+1))) :=
    Real.log_mul (by norm_num) hbase.ne'
  rw [hlognum] at hdiv
  have hQcomp : 5760*((m+1:ℕ):ℝ)*Real.log ((m+2:ℕ):ℝ) ≤
      5760*((m+3:ℕ):ℝ)*Real.log M := by nlinarith [hX]
  linarith


private theorem log_factorial_ratio {a : ℝ} (ha : 0 < a) (m : ℕ) :
    Real.log (a/(m.factorial:ℝ)) ≤ Real.log a :=
  log_div_factorial_le ha m

theorem kernelVelocityUnit_log_le (m : ℕ) :
    Real.log (kernelVelocityUnit m) ≤
      113*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  let M : ℝ := ((m+3:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlogM : 0 < Real.log M := by
    apply Real.log_pos
    dsimp [M]
    exact_mod_cast (show 1<m+3 by omega)
  have hlog2 := log_two_le_log_plus_three m
  have hkernel : 0 < kernelUnit (m+2) := by
    unfold kernelUnit
    have := rms_one_pos (3*(m+2)-1)
    have := materialWordMassBase_one_le (m+2)
    positivity
  have hnum : 0 < 2*16^m*kernelUnit (m+2) := by positivity
  have hq := kernelUnit_log_le (m+2)
  have hlogarg : Real.log ((m+4:ℕ):ℝ) ≤ 2*Real.log M := by
    have hM2 : ((m+4:ℕ):ℝ) ≤ 2*M := by
      dsimp [M]
      exact_mod_cast (show m+4≤2*(m+3) by omega)
    calc
      _ ≤ Real.log (2*M) := Real.log_le_log (by positivity) hM2
      _ = Real.log 2 + Real.log M := Real.log_mul (by norm_num) hM.ne'
      _ ≤ 2*Real.log M := by linarith
  have hqBound : Real.log (kernelUnit (m+2)) ≤
      108*((m+3:ℕ):ℝ)*Real.log M := by
    have he : ((m+2+1:ℕ):ℝ) = ((m+3:ℕ):ℝ) := by congr 1
    rw [he] at hq
    have hp := mul_le_mul_of_nonneg_left hlogarg (by positivity : 0 ≤ 54*((m+3:ℕ):ℝ))
    nlinarith [hq, hp]
  have h16 : Real.log (16:ℝ) ≤ 4*Real.log M := by
    calc
      _ = 4*Real.log 2 := by
        conv_lhs => rw [show (16:ℝ)=2^4 by norm_num]
        rw [Real.log_pow]
        norm_num
      _ ≤ 4*Real.log M := by gcongr
  have hmM : (m:ℝ) ≤ ((m+3:ℕ):ℝ) := by exact_mod_cast (show m≤m+3 by omega)
  have hlogpow : (m:ℝ)*Real.log 16 ≤
      4*((m+3:ℕ):ℝ)*Real.log M := by
    calc
      _ ≤ (m:ℝ)*(4*Real.log M) := mul_le_mul_of_nonneg_left h16 (Nat.cast_nonneg m)
      _ ≤ ((m+3:ℕ):ℝ)*(4*Real.log M) := by gcongr
      _ = _ := by ring
  have hlog2X : Real.log 2 ≤ ((m+3:ℕ):ℝ)*Real.log M := by
    have hm1 : (1:ℝ)≤((m+3:ℕ):ℝ) := by exact_mod_cast (show 1≤m+3 by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) hlogM.le]
  unfold kernelVelocityUnit
  have hd := log_factorial_ratio hnum m
  rw [Real.log_mul (mul_ne_zero (by norm_num : (2:ℝ)≠0)
      (pow_ne_zero _ (by norm_num : (16:ℝ)≠0))) hkernel.ne',
    Real.log_mul (by norm_num : (2:ℝ)≠0)
      (pow_ne_zero _ (by norm_num : (16:ℝ)≠0)),
    Real.log_pow] at hd
  linarith


theorem backwardRowUnit_log_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (backwardRowUnit m) ≤
      54*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  let M : ℝ := ((m+3:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlogM : 0 < Real.log M := by
    apply Real.log_pos
    dsimp [M]
    exact_mod_cast (show 1<m+3 by omega)
  have hlog2 := log_two_le_log_plus_three m
  have hback : 0 < backwardUnit (m-1) := by
    unfold backwardUnit
    have := rms_one_pos (3+3*(m-1))
    positivity
  have hnum : 0 < 2^(m+1)*backwardUnit (m-1) := by positivity
  have hd := log_div_factorial_le hnum m
  have hbk := backwardUnit_log_le (m-1)
  have hindex : (m-1)+1=m := by omega
  rw [hindex] at hbk
  have hlogarg : Real.log (((m-1)+2:ℕ):ℝ) ≤ Real.log M := by
    apply Real.log_le_log (by positivity)
    dsimp [M]
    exact_mod_cast (show (m-1)+2≤m+3 by omega)
  have hmM : (m:ℝ) ≤ M := by
    dsimp [M]
    exact_mod_cast (show m≤m+3 by omega)
  have hbackBound : Real.log (backwardUnit (m-1)) ≤ 53*M*Real.log M := by
    have hx : (m:ℝ)*Real.log (((m-1)+2:ℕ):ℝ) ≤ M*Real.log M := by
      exact (mul_le_mul_of_nonneg_left hlogarg (Nat.cast_nonneg m)).trans
        (mul_le_mul_of_nonneg_right hmM hlogM.le)
    nlinarith [hbk, hx]
  have hpowBound : ((m+1:ℕ):ℝ)*Real.log 2 ≤ M*Real.log M := by
    have hi : ((m+1:ℕ):ℝ)≤M := by
      dsimp [M]
      exact_mod_cast (show m+1≤m+3 by omega)
    exact (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hi hlogM.le)
  unfold backwardRowUnit
  rw [Real.log_mul (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)) hback.ne',
    Real.log_pow] at hd
  linarith


private theorem two_power_conditional_log_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (2^(m+1)*conditionalOrderEnvelope m) ≤
      61*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  let M : ℝ := ((m+3:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlogM : 0 < Real.log M := by
    apply Real.log_pos
    dsimp [M]
    exact_mod_cast (show 1<m+3 by omega)
  have hlog2 := log_two_le_log_plus_three m
  have henv : 0 < conditionalOrderEnvelope m := by
    unfold conditionalOrderEnvelope
    have hmpos : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
    positivity
  have henvLog := NumericalCoefficientGrowth.conditionalOrderEnvelope_log_le m hm
  have hlogarg : Real.log ((m+2:ℕ):ℝ) ≤ Real.log M := by
    apply Real.log_le_log (by positivity)
    dsimp [M]
    exact_mod_cast (show m+2≤m+3 by omega)
  have hmM : (m:ℝ) ≤ M := by
    dsimp [M]
    exact_mod_cast (show m≤m+3 by omega)
  have henvBound : Real.log (conditionalOrderEnvelope m) ≤ 60*M*Real.log M := by
    have hx : (m:ℝ)*Real.log ((m+2:ℕ):ℝ) ≤ M*Real.log M :=
      (mul_le_mul_of_nonneg_left hlogarg (Nat.cast_nonneg m)).trans
        (mul_le_mul_of_nonneg_right hmM hlogM.le)
    nlinarith [henvLog, hx]
  have hpowBound : ((m+1:ℕ):ℝ)*Real.log 2 ≤ M*Real.log M := by
    have hi : ((m+1:ℕ):ℝ)≤M := by
      dsimp [M]
      exact_mod_cast (show m+1≤m+3 by omega)
    exact (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hi hlogM.le)
  rw [Real.log_mul (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)) henv.ne',
    Real.log_pow]
  linarith

theorem forwardRowUnit_log_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (forwardRowUnit m) ≤
      61*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  have henv : 0 < conditionalOrderEnvelope m := by
    unfold conditionalOrderEnvelope
    have hmpos : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
    positivity
  unfold forwardRowUnit
  exact (log_div_factorial_le (mul_pos (pow_pos (by norm_num) _) henv) m).trans
    (two_power_conditional_log_le m hm)

theorem conditionalRowUnit_log_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (conditionalRowUnit m) ≤
      61*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  have henv : 0 < conditionalOrderEnvelope m := by
    unfold conditionalOrderEnvelope
    have hmpos : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
    positivity
  have hc : 0 < conditionalEnd := conditionalEnd_pos
  have hc1 : conditionalEnd ≤ 1 := conditionalEnd_lt_one.le
  have hnum : 0 < 2^(m+1)*conditionalEnd*conditionalOrderEnvelope m := by positivity
  have hle : 2^(m+1)*conditionalEnd*conditionalOrderEnvelope m ≤
      2^(m+1)*conditionalOrderEnvelope m := by
    calc
      _ = (2^(m+1)*conditionalOrderEnvelope m)*conditionalEnd := by ring
      _ ≤ (2^(m+1)*conditionalOrderEnvelope m)*1 := by gcongr
      _ = _ := by ring
  unfold conditionalRowUnit
  calc
    Real.log (2^(m+1)*conditionalEnd*conditionalOrderEnvelope m/(m.factorial:ℝ)) ≤
        Real.log (2^(m+1)*conditionalEnd*conditionalOrderEnvelope m) :=
      log_div_factorial_le hnum m
    _ ≤ Real.log (2^(m+1)*conditionalOrderEnvelope m) :=
      Real.log_le_log hnum hle
    _ ≤ _ := two_power_conditional_log_le m hm


theorem angleVelocityUnit_log_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (angleVelocityUnit m) ≤
      2900*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  let M : ℝ := ((m+3:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlogM : 0 < Real.log M := by
    apply Real.log_pos
    dsimp [M]
    exact_mod_cast (show 1<m+3 by omega)
  have hlog2 := log_two_le_log_plus_three m
  have hQ := NumericalCoefficientGrowth.phaseQ_angle_log_le
    (by norm_num : (1:ℝ)≤256) (by norm_num : (256:ℝ)≤256) m
  have hbase : 0 < Real.sqrt (2*Tensor.AdjointReduction.PhaseBudget.Q 256
      (5*m+1)) := by
    apply Real.sqrt_pos.2
    unfold Tensor.AdjointReduction.PhaseBudget.Q
    positivity
  have hsqrt := phase_sqrt_log_le
    (by norm_num : (1:ℝ)≤256) (by norm_num : (256:ℝ)≤256)
    (5*m+1) hQ hM hlog2
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hlogm : Real.log (m:ℝ) ≤ Real.log M := by
    apply Real.log_le_log hmpos
    dsimp [M]
    exact_mod_cast (show m≤m+3 by omega)
  have hlogarg : Real.log ((m+2:ℕ):ℝ) ≤ Real.log M := by
    apply Real.log_le_log (by positivity)
    dsimp [M]
    exact_mod_cast (show m+2≤m+3 by omega)
  have hX : ((m+1:ℕ):ℝ)*Real.log ((m+2:ℕ):ℝ) ≤ M*Real.log M := by
    have hi : ((m+1:ℕ):ℝ)≤M := by dsimp [M]; exact_mod_cast (show m+1≤m+3 by omega)
    exact (mul_le_mul_of_nonneg_left hlogarg (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hi hlogM.le)
  have hM1 : 1 ≤ M := by dsimp [M]; exact_mod_cast (show 1≤m+3 by omega)
  have hlogMB : Real.log M ≤ M*Real.log M := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hM1) hlogM.le]
  have h160 : Real.log (160:ℝ) ≤ 8*M*Real.log M := by
    have h256 : Real.log (160:ℝ) ≤ Real.log (256:ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hpow : Real.log (256:ℝ)=8*Real.log 2 := by
      conv_lhs => rw [show (256:ℝ)=2^8 by norm_num]
      rw [Real.log_pow]
      norm_num
    rw [hpow] at h256
    nlinarith [h256, hlog2, hlogMB]
  have h2pow : (m:ℝ)*Real.log 2 ≤ M*Real.log M := by
    have hmM : (m:ℝ)≤M := by dsimp [M]; exact_mod_cast (show m≤m+3 by omega)
    exact (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg m)).trans
      (mul_le_mul_of_nonneg_right hmM hlogM.le)
  have h5m : 5*Real.log (m:ℝ) ≤ 5*M*Real.log M := by nlinarith [hlogm,hlogMB]
  have hQcomp : 5760*((m+1:ℕ):ℝ)*Real.log ((m+2:ℕ):ℝ) ≤
      5760*M*Real.log M := by nlinarith [hX]
  have hnum : 0 < 160*(m:ℝ)^5*2^m*Real.sqrt
      (2*Tensor.AdjointReduction.PhaseBudget.Q 256 (5*m+1)) := by positivity
  unfold angleVelocityUnit
  have hd := log_div_factorial_le hnum m
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (by norm_num : (160:ℝ)≠0)
      (pow_ne_zero _ hmpos.ne')) (pow_ne_zero _ (by norm_num : (2:ℝ)≠0))) hbase.ne',
    Real.log_mul (mul_ne_zero (by norm_num : (160:ℝ)≠0)
      (pow_ne_zero _ hmpos.ne')) (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)),
    Real.log_mul (by norm_num : (160:ℝ)≠0) (pow_ne_zero _ hmpos.ne'),
    Real.log_pow, Real.log_pow] at hd
  linarith


theorem forwardVelocityUnit_log_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (forwardVelocityUnit m) ≤
      75*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  let M : ℝ := ((m+3:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hlogM : 0 < Real.log M := by
    apply Real.log_pos
    dsimp [M]
    exact_mod_cast (show 1<m+3 by omega)
  have hlog2 := log_two_le_log_plus_three m
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have henv : 0 < conditionalOrderEnvelope m := by
    unfold conditionalOrderEnvelope
    positivity
  have hnum : 0 < 80*2^(m+1)*(m:ℝ)^5*conditionalOrderEnvelope m := by positivity
  have henvLog := NumericalCoefficientGrowth.conditionalOrderEnvelope_log_le m hm
  have hlogarg : Real.log ((m+2:ℕ):ℝ) ≤ Real.log M := by
    apply Real.log_le_log (by positivity)
    dsimp [M]
    exact_mod_cast (show m+2≤m+3 by omega)
  have hmM : (m:ℝ) ≤ M := by dsimp [M]; exact_mod_cast (show m≤m+3 by omega)
  have henvB : Real.log (conditionalOrderEnvelope m) ≤ 60*M*Real.log M := by
    have hx : (m:ℝ)*Real.log ((m+2:ℕ):ℝ) ≤ M*Real.log M :=
      (mul_le_mul_of_nonneg_left hlogarg (Nat.cast_nonneg m)).trans
        (mul_le_mul_of_nonneg_right hmM hlogM.le)
    nlinarith [henvLog,hx]
  have hlogm : Real.log (m:ℝ) ≤ Real.log M :=
    Real.log_le_log hmpos hmM
  have hlogMbound : Real.log M ≤ M*Real.log M := by
    have hm1 : (1:ℝ)≤M := by dsimp [M]; exact_mod_cast (show 1≤m+3 by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) hlogM.le]
  have h80 : Real.log (80:ℝ) ≤ 7*M*Real.log M := by
    have h128 : Real.log (80:ℝ) ≤ Real.log (128:ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hp : Real.log (128:ℝ)=7*Real.log 2 := by
      conv_lhs => rw [show (128:ℝ)=2^7 by norm_num]
      rw [Real.log_pow]
      norm_num
    rw [hp] at h128
    nlinarith [h128,hlog2,hlogMbound]
  have hpow : ((m+1:ℕ):ℝ)*Real.log 2 ≤ M*Real.log M := by
    have hi : ((m+1:ℕ):ℝ)≤M := by dsimp [M]; exact_mod_cast (show m+1≤m+3 by omega)
    exact (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hi hlogM.le)
  have hm5 : 5*Real.log (m:ℝ) ≤ 5*M*Real.log M := by nlinarith [hlogm,hlogMbound]
  unfold forwardVelocityUnit
  have hd := log_div_factorial_le hnum m
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (by norm_num : (80:ℝ)≠0)
      (pow_ne_zero _ (by norm_num : (2:ℝ)≠0))) (pow_ne_zero _ hmpos.ne')) henv.ne',
    Real.log_mul (mul_ne_zero (by norm_num : (80:ℝ)≠0)
      (pow_ne_zero _ (by norm_num : (2:ℝ)≠0))) (pow_ne_zero _ hmpos.ne'),
    Real.log_mul (by norm_num : (80:ℝ)≠0)
      (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)),
    Real.log_pow, Real.log_pow] at hd
  linarith


private theorem posLog_le_of_log_le {u X : ℝ} (hX : 0 ≤ X)
    (h : Real.log u ≤ X) : Real.posLog u ≤ X := by
  simp only [Real.posLog_apply]
  exact max_le hX h

private theorem posLog_three (a b c : ℝ) :
    Real.posLog (a+b+c) ≤
      2*Real.log 2 + Real.posLog a+Real.posLog b+Real.posLog c := by
  have h1 := Real.posLog_add (x := a+b) (y := c)
  have h2 := Real.posLog_add (x := a) (y := b)
  linarith

private theorem posLog_six (a b c d e f : ℝ) :
    Real.posLog (a+b+c+d+e+f) ≤
      5*Real.log 2 + Real.posLog a+Real.posLog b+Real.posLog c+
        Real.posLog d+Real.posLog e+Real.posLog f := by
  have h1 := Real.posLog_add (x := a+b+c+d+e) (y := f)
  have h2 := Real.posLog_add (x := a+b+c+d) (y := e)
  have h3 := Real.posLog_add (x := a+b+c) (y := d)
  have h4 := Real.posLog_add (x := a+b) (y := c)
  have h5 := Real.posLog_add (x := a) (y := b)
  linarith

theorem velocityUnit_posLog_le (m : ℕ) (hm : 1 ≤ m) :
    Real.posLog (velocityUnit m) ≤
      3090*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  let X : ℝ := ((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ)
  have hX : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1≤m+3 by omega)))
  have hlog2 : Real.log 2 ≤ X := by
    have hM1 : (1:ℝ)≤((m+3:ℕ):ℝ) := by exact_mod_cast (show 1≤m+3 by omega)
    have hlogM : 0 ≤ Real.log ((m+3:ℕ):ℝ) := Real.log_nonneg hM1
    have hle := log_two_le_log_plus_three m
    dsimp [X]
    nlinarith [mul_nonneg (sub_nonneg.mpr hM1) hlogM]
  have hk := posLog_le_of_log_le (by positivity : 0 ≤ 113*X)
    (by simpa only [X, mul_assoc] using kernelVelocityUnit_log_le m)
  have ha := posLog_le_of_log_le (by positivity : 0 ≤ 2900*X)
    (by simpa only [X, mul_assoc] using angleVelocityUnit_log_le m hm)
  have hf := posLog_le_of_log_le (by positivity : 0 ≤ 75*X)
    (by simpa only [X, mul_assoc] using forwardVelocityUnit_log_le m hm)
  unfold velocityUnit
  nlinarith [posLog_three (kernelVelocityUnit m)
    (angleVelocityUnit m) (forwardVelocityUnit m)]

/-- Fully explicit growth of the actual m-only row inventory: the numerical
coefficient is at most `exp(10200(m+3)log(m+3))`. -/
theorem A_log_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (A m) ≤
      10200*((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ) := by
  let X : ℝ := ((m+3:ℕ):ℝ)*Real.log ((m+3:ℕ):ℝ)
  have hX : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1≤m+3 by omega)))
  have hlog2 : Real.log 2 ≤ X := by
    have hM1 : (1:ℝ)≤((m+3:ℕ):ℝ) := by exact_mod_cast (show 1≤m+3 by omega)
    have hlogM : 0 ≤ Real.log ((m+3:ℕ):ℝ) := Real.log_nonneg hM1
    have hle := log_two_le_log_plus_three m
    dsimp [X]
    nlinarith [mul_nonneg (sub_nonneg.mpr hM1) hlogM]
  have hlog3 : Real.log 3 ≤ 2*X := by
    have h34 : Real.log (3:ℝ) ≤ Real.log (4:ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
      conv_lhs => rw [show (4:ℝ)=2^2 by norm_num]
      rw [Real.log_pow]
      norm_num
    rw [h4] at h34
    linarith
  have hlog4 : Real.log 4 ≤ 2*X := by
    have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
      conv_lhs => rw [show (4:ℝ)=2^2 by norm_num]
      rw [Real.log_pow]
      norm_num
    rw [h4]
    linarith
  have hs := posLog_le_of_log_le (by positivity : 0 ≤ 4034*X)
    (by simpa only [X, mul_assoc] using stateUnit_log_le m)
  have hv := velocityUnit_posLog_le m hm
  have hb := posLog_le_of_log_le (by positivity : 0 ≤ 54*X)
    (by simpa only [X, mul_assoc] using backwardRowUnit_log_le m hm)
  have hc := posLog_le_of_log_le (by positivity : 0 ≤ 61*X)
    (by simpa only [X, mul_assoc] using conditionalRowUnit_log_le m hm)
  have hsc := posLog_le_of_log_le (by positivity : 0 ≤ 2883*X)
    (by simpa only [X, mul_assoc] using scoreUnit_log_le m)
  have hf := posLog_le_of_log_le (by positivity : 0 ≤ 61*X)
    (by simpa only [X, mul_assoc] using forwardRowUnit_log_le m hm)
  have h3s := Real.posLog_nat_mul (n := 3) (x := stateUnit m)
  have h3v := Real.posLog_nat_mul (n := 3) (x := velocityUnit m)
  have h3b := Real.posLog_nat_mul (n := 3) (x := backwardRowUnit m)
  have h4c := Real.posLog_nat_mul (n := 4) (x := conditionalRowUnit m)
  have hAeq : A m = 3*stateUnit m+3*velocityUnit m+
      3*backwardRowUnit m+4*conditionalRowUnit m+
      scoreUnit m+forwardRowUnit m := by
    unfold A
    ring
  have hsum := posLog_six (3*stateUnit m) (3*velocityUnit m)
    (3*backwardRowUnit m) (4*conditionalRowUnit m)
    (scoreUnit m) (forwardRowUnit m)
  rw [←hAeq] at hsum
  have hlog : Real.log (A m) ≤ Real.posLog (A m) := by
    unfold Real.posLog
    exact le_max_right _ _
  dsimp [X] at *
  nlinarith

end AcceleratedLogConcave.Numerics.SmoothInventoryDimension
