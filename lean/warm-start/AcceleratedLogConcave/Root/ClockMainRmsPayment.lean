import AcceleratedLogConcave.Root.ClockMainRms
import AcceleratedLogConcave.Root.ClockQuadratureResolution

/-! Explicit scalar payment for the proved finite Clock main-loop error. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockMainRmsPayment
open Oracle Numerics ClockNoisyLayer
variable (P : SourceSchedule) (clock : ClockLaw.Clock) {d : ℕ}
local notation "rf" => ClockCollocation.rF P.delta
local notation "sigma" => CovarianceSetup.sigma (N P) (rhoC P) (a P)
local notation "E" => 4*sigma*P.delta^(P.K:ℝ)*(10/3)*Real.sqrt (d:ℝ)
local notation "B" => rf*Real.sqrt (d:ℝ)*P.delta^P.K

private theorem childBudget_le (k : ℕ) (i : Index P) :
    ClockMainRms.childBudget (d := d) P k i≤E := by
  have hamp : 0≤4*sigma*P.delta^(P.K:ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) ((CovarianceSetup.sigma_pos (ClockCollocation.count_pos P.delta_pos P.K) (rhoC_pos P) (a_pos P)).le)) (Real.rpow_nonneg P.delta_pos.le _)
  have hs : Real.sqrt 10≤(10/3:ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤10),Real.sqrt_nonneg 10]
  unfold ClockMainRms.childBudget
  split_ifs
  · rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hamp,Real.sqrt_mul (by norm_num : (0:ℝ)≤10)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (d:ℝ))) hamp
  · exact mul_nonneg (mul_nonneg hamp (by norm_num)) (Real.sqrt_nonneg _)

private theorem childRow_le (hDs : 1≤P.Ds) (k : ℕ) :
    SharedLayerRms.childRowBudget (A P clock) (ClockMainRms.childBudget (d := d) P) k≤(5/3)*B := by
  have hσ : 0≤sigma := (CovarianceSetup.sigma_pos (ClockCollocation.count_pos P.delta_pos P.K) (rhoC_pos P) (a_pos P)).le
  have hE : 0≤E := mul_nonneg (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hσ) (Real.rpow_nonneg P.delta_pos.le _)) (by norm_num)) (Real.sqrt_nonneg _)
  have hrow : SharedLayerRms.childRowBudget (A P clock) (ClockMainRms.childBudget (d := d) P) k≤a P*E := by
    unfold SharedLayerRms.childRowBudget
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (a_pos P).le hE)).2
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) (by unfold ClockMainRms.childBudget; split_ifs <;> positivity))]
    calc
      _ ≤ ∑ j,|A P clock i j| * E := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (childBudget_le (d := d) P k j) (abs_nonneg _)
      _ = (∑ j,|A P clock i j|)*E := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (ClockCollocation.sum_abs_matrix_le_quarter P.delta P.delta_pos P.K clock (0:ℝ) 0 i) hE
  have hn : 1≤Real.sqrt (N P:ℝ) := by
    have hnbase : (1:ℝ)≤(N P:ℝ) := by exact_mod_cast (show 1≤N P from ClockCollocation.count_pos P.delta_pos P.K)
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnbase
  have hd : 1≤P.Ds*Real.sqrt (N P:ℝ) := one_mul (1:ℝ) ▸ mul_le_mul hDs hn (by norm_num) P.Ds_pos.le
  have hN : 0<Real.sqrt (N P:ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hEq : a P*E=(5/3)*B/(P.Ds*Real.sqrt (N P:ℝ)) := by
    rw [sigma_identity P,Real.rpow_natCast]
    unfold a
    field_simp
    ring
  exact hrow.trans (hEq.trans_le (div_le_self (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (rF_pos P).le (Real.sqrt_nonneg _)) (pow_nonneg P.delta_pos.le _))) hd))

private theorem forcing_le {q F : ℝ} (hq : 0≤q) (hquarter : q≤1/4) (hF : 0≤F)
    (eta : ℕ→ℝ) (heta : ∀ k,eta k≤F) (n : ℕ) :
    Collocation.forcingSum q eta n≤(4/3)*F := by
  induction n with
  | zero => rw [Collocation.forcingSum_zero]; positivity
  | succ n ih =>
    rw [Collocation.forcingSum_succ]
    have h := mul_le_mul_of_nonneg_left ih hq
    have h' := mul_le_mul_of_nonneg_right hquarter (mul_nonneg (by norm_num : (0:ℝ)≤4/3) hF)
    nlinarith [heta n]

/-- The explicit resolution threshold pays the whole actual finite-loop budget. -/
theorem budget_le (hc : 0<P.csch) (hdelta : P.delta≤1/2)
    (hyQuad : ClockQuadratureResolution.threshold P.K≤P.y) :
    ClockMainRms.budget (d := d) P clock≤4*rf*Real.sqrt (d:ℝ)*P.delta^P.K := by
  have hδ1 : P.delta≤1 := hdelta.trans (by norm_num)
  have hDs : 1≤P.Ds := Real.one_le_rpow_of_pos_of_le_one_of_nonpos P.delta_pos hδ1 (by linarith [P.t_pos hc])
  have hB : 0≤B := mul_nonneg (mul_nonneg (rF_pos P).le (Real.sqrt_nonneg _)) (pow_nonneg P.delta_pos.le _)
  have hrf : rf^2=2*P.delta := Real.sq_sqrt (mul_pos (by norm_num) P.delta_pos).le
  have hq : (2*P.delta)*a P=P.delta^2 := by unfold a; nlinarith
  have hq0 : 0≤(2*P.delta)*a P := by rw [hq]; positivity
  have hqquarter : (2*P.delta)*a P≤1/4 := by rw [hq]; nlinarith [P.delta_pos]
  have ht : ((2*P.delta)*a P)^(P.K+4)*(rf*Real.sqrt (d:ℝ))≤B := by
    have hqδ : (2*P.delta)*a P≤P.delta := by rw [hq]; nlinarith [P.delta_pos]
    have hp := (pow_le_pow_left₀ hq0 hqδ (P.K+4)).trans
      (pow_le_pow_of_le_one P.delta_pos.le hδ1 (by omega : P.K≤P.K+4))
    exact (mul_le_mul_of_nonneg_right hp (mul_nonneg (rF_pos P).le (Real.sqrt_nonneg _))).trans_eq (by ring)
  have hr : (rf/2)*ClockQuadraturePower.orderConstant P.K*Real.sqrt (d:ℝ)*P.delta^(P.K+6)≤B/2 := by
    have he := mul_le_mul_of_nonneg_left (ClockQuadratureResolution.endpoint_payment P hyQuad)
      (div_nonneg (mul_nonneg (rF_pos P).le (Real.sqrt_nonneg (d:ℝ))) (by norm_num : (0:ℝ)≤2))
    nlinarith
  have hf := forcing_le hq0 hqquarter (mul_nonneg (by norm_num : (0:ℝ)≤13/6) hB)
    (fun k => (rf/2)*ClockQuadraturePower.orderConstant P.K*Real.sqrt (d:ℝ)*P.delta^(P.K+6) +
      SharedLayerRms.childRowBudget (A P clock) (ClockMainRms.childBudget (d := d) P) k)
    (fun k => by linarith [childRow_le (d := d) P clock hDs k]) (P.K+4)
  unfold ClockMainRms.budget
  nlinarith
end AcceleratedLogConcave.Root.ClockMainRmsPayment
