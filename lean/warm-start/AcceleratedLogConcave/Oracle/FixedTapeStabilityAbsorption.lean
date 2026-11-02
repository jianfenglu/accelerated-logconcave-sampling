import AcceleratedLogConcave.Oracle.FixedTapeStabilityGrowth
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Ring.Pow

/-! Scalar absorption for the existing finite fixed-tape growth polynomials.
No division by the oracle constant, positive layer count, reachable-call
invariant, or recursive uniform stability is assumed or asserted. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.FixedTapeStability
open scoped BigOperators

theorem powerSum_le_geometric (N : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    powerSum N z ≤ 1/(1-z) := by
  simpa [powerSum, one_div] using
    (geom_sum_Ico_le_of_lt_one (m := 0) (n := N+1) hz hz1)

theorem samplingGrowth_le_geometric (N : ℕ) {F L r η : ℝ}
    (hF : 0 ≤ F) (hL : 0 ≤ L) (hr : 0 ≤ r) (hη : 0 ≤ η)
    (hq : F*η < 1) (hsize : L*r^2 ≤ η) :
    samplingGrowth N (F*L) r ≤ F*L*r/(1-F*η) := by
  have hprod : F*L*r^2 ≤ F*η := by nlinarith [mul_le_mul_of_nonneg_left hsize hF]
  have hp := (powerSum_mono (N := N) le_rfl (by positivity) hprod).trans
    (powerSum_le_geometric N (mul_nonneg hF hη) hq)
  unfold samplingGrowth
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg hF hL) hr)

theorem meanGrowth_le_geometric (N : ℕ) {F L r b A η : ℝ}
    (hF : 0 ≤ F) (hL : 0 ≤ L) (hr : 0 ≤ r) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hq : F*η < 1) (hb : b^2 ≤ 1) (hsize : L*r^2 ≤ η) (hrow : L*A ≤ η) :
    meanGrowth N (F*L) (F*L) r b A ≤ F*L/(1-F*η)^2 := by
  have hd : 0 < 1-F*η := by linarith
  have hsample := samplingGrowth_le_geometric N hF hL hr hη hq hsize
  have hsample0 := samplingGrowth_nonneg N (mul_nonneg hF hL) hr
  have hcoef : r*b^2 ≤ r := by nlinarith [mul_le_mul_of_nonneg_left hb hr]
  have hinner : r*b^2*samplingGrowth N (F*L) r ≤ F*η/(1-F*η) := by
    calc
      _ ≤ r*(F*L*r/(1-F*η)) := mul_le_mul hcoef hsample hsample0 hr
      _ = F*(L*r^2)/(1-F*η) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hF) hd.le
  have hone : 1+r*b^2*samplingGrowth N (F*L) r ≤ 1/(1-F*η) := by
    calc
      _ ≤ 1+F*η/(1-F*η) := by linarith
      _ = _ := by field_simp; ring
  have hprod : F*L*A ≤ F*η := by nlinarith [mul_le_mul_of_nonneg_left hrow hF]
  have hp := (powerSum_mono (N := N) le_rfl (by positivity) hprod).trans
    (powerSum_le_geometric N (mul_nonneg hF hη) hq)
  unfold meanGrowth
  calc
    _ ≤ (F*L*(1/(1-F*η)))*(1/(1-F*η)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hone (mul_nonneg hF hL)) hp
        (powerSum_nonneg N (by positivity)) (by positivity)
    _ = _ := by field_simp

/-- Smaller, separately chosen main and sampling constants are handled by the
proved polynomial monotonicity; no lower bound on L is required. -/
theorem meanGrowth_le_geometric_of_le (N : ℕ) {κm κs F L r b A η : ℝ}
    (hm : 0 ≤ κm) (hs : 0 ≤ κs) (hmm : κm ≤ F*L) (hss : κs ≤ F*L)
    (hF : 0 ≤ F) (hL : 0 ≤ L) (hr : 0 ≤ r) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hq : F*η < 1) (hb : b^2 ≤ 1) (hsize : L*r^2 ≤ η) (hrow : L*A ≤ η) :
    meanGrowth N κm κs r b A ≤ F*L/(1-F*η)^2 :=
  (meanGrowth_mono le_rfl hm hs hr hA hmm hss le_rfl le_rfl le_rfl).trans
    (meanGrowth_le_geometric N hF hL hr hA hη hq hb hsize hrow)

theorem samplingGrowth_le_geometric_of_le (N : ℕ) {κ F L r η : ℝ}
    (hκ : 0 ≤ κ) (hκF : κ ≤ F*L)
    (hF : 0 ≤ F) (hL : 0 ≤ L) (hr : 0 ≤ r) (hη : 0 ≤ η)
    (hq : F*η < 1) (hsize : L*r^2 ≤ η) :
    samplingGrowth N κ r ≤ F*L*r/(1-F*η) :=
  (samplingGrowth_mono le_rfl hκ hr hκF le_rfl).trans
    (samplingGrowth_le_geometric N hF hL hr hη hq hsize)

private theorem reciprocal_square_le_linear {F η : ℝ}
    (hF2 : F ≤ 2) (hη : 0 ≤ η) (hη100 : η ≤ 1/100) :
    1/(1-F*η)^2 ≤ 1+20*η := by
  have hx : F*η ≤ 2*η := mul_le_mul_of_nonneg_right hF2 hη
  have hd : 0 < 1-F*η := by linarith
  have hden : 1-4*η ≤ (1-F*η)^2 := by nlinarith [sq_nonneg (F*η)]
  have hsq : η^2 ≤ (1/100)*η := by nlinarith [mul_le_mul_of_nonneg_right hη100 hη]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).2
  calc
    1 ≤ (1+20*η)*(1-4*η) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

theorem meanGrowth_le_linear (N : ℕ) {F L r b A η : ℝ}
    (hF : 0 ≤ F) (hF2 : F ≤ 2) (hL : 0 ≤ L) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hη : 0 ≤ η) (hη100 : η ≤ 1/100) (hb : b^2 ≤ 1)
    (hsize : L*r^2 ≤ η) (hrow : L*A ≤ η) :
    meanGrowth N (F*L) (F*L) r b A ≤ F*L*(1+20*η) := by
  have hq : F*η < 1 := by nlinarith [mul_le_mul_of_nonneg_right hF2 hη]
  exact (meanGrowth_le_geometric N hF hL hr hA hη hq hb hsize hrow).trans
    (by simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left (reciprocal_square_le_linear hF2 hη hη100) (mul_nonneg hF hL))

theorem samplingGrowth_le_five (N : ℕ) {F L r η : ℝ}
    (hF : 0 ≤ F) (hF2 : F ≤ 2) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hη : 0 ≤ η) (hη100 : η ≤ 1/100) (hsize : L*r^2 ≤ η) :
    samplingGrowth N (F*L) r ≤ 5*r*L := by
  have hx : F*η ≤ 2*η := mul_le_mul_of_nonneg_right hF2 hη
  have hq : F*η < 1 := by linarith
  have hd : 0 < 1-F*η := by linarith
  have hf : F/(1-F*η) ≤ 5 := (div_le_iff₀ hd).2 (by linarith)
  calc
    _ ≤ F*L*r/(1-F*η) := samplingGrowth_le_geometric N hF hL hr hη hq hsize
    _ = (F/(1-F*η))*(r*L) := by ring
    _ ≤ 5*(r*L) := mul_le_mul_of_nonneg_right hf (mul_nonneg hr hL)
    _ = _ := by ring

theorem meanGrowth_le_linear_of_le (N : ℕ) {κm κs F L r b A η : ℝ}
    (hm : 0 ≤ κm) (hs : 0 ≤ κs) (hmm : κm ≤ F*L) (hss : κs ≤ F*L)
    (hF : 0 ≤ F) (hF2 : F ≤ 2) (hL : 0 ≤ L) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hη : 0 ≤ η) (hη100 : η ≤ 1/100) (hb : b^2 ≤ 1)
    (hsize : L*r^2 ≤ η) (hrow : L*A ≤ η) :
    meanGrowth N κm κs r b A ≤ F*L*(1+20*η) :=
  (meanGrowth_mono le_rfl hm hs hr hA hmm hss le_rfl le_rfl le_rfl).trans
    (meanGrowth_le_linear N hF hF2 hL hr hA hη hη100 hb hsize hrow)

theorem samplingGrowth_le_five_of_le (N : ℕ) {κ F L r η : ℝ}
    (hκ : 0 ≤ κ) (hκF : κ ≤ F*L)
    (hF : 0 ≤ F) (hF2 : F ≤ 2) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hη : 0 ≤ η) (hη100 : η ≤ 1/100) (hsize : L*r^2 ≤ η) :
    samplingGrowth N κ r ≤ 5*r*L :=
  (samplingGrowth_mono le_rfl hκ hr hκF le_rfl).trans
    (samplingGrowth_le_five N hF hF2 hL hr hη hη100 hsize)

/-- A finite height budget absorbs the successive linear inflation factors.
H=0 is handled before deriving any bound on eta. -/
theorem height_factor_mem (H k : ℕ) {η : ℝ} (hη : 0 ≤ η) (hk : k ≤ H)
    (hbudget : 20*(H:ℝ)*η ≤ 1/2) : 1 ≤ (1+20*η)^k ∧ (1+20*η)^k ≤ 2 := by
  refine ⟨one_le_pow₀ (by linarith), ?_⟩
  by_cases hH : H = 0
  · have hk0 : k = 0 := by omega
    simp [hk0]
  have hH1 : (1:ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  have hx : 20*η ≤ 1/2 := by nlinarith
  have hkR : (k:ℝ) ≤ H := by exact_mod_cast hk
  have hkx : (k:ℝ)*(20*η) ≤ 1/2 := by nlinarith
  have hbern := one_add_mul_le_pow (show (-2:ℝ) ≤ -(20*η) by linarith) k
  have hlow : (1/2:ℝ) ≤ (1-20*η)^k := by
    simpa only [sub_eq_add_neg] using (show (1/2:ℝ) ≤ (1+-(20*η))^k by nlinarith)
  have hprod : (1+20*η)^k*(1-20*η)^k ≤ (1:ℝ) := by
    rw [← mul_pow]
    have hh := pow_le_pow_left₀ (mul_nonneg (by linarith : (0:ℝ) ≤ 1+20*η)
      (by linarith : (0:ℝ) ≤ 1-20*η))
      (show (1+20*η)*(1-20*η) ≤ (1:ℝ) by nlinarith [sq_nonneg (20*η)]) k
    simpa only [one_pow] using hh
  have hp : 0 ≤ (1+20*η)^k := pow_nonneg (by linarith) k
  nlinarith

end AcceleratedLogConcave.Oracle.FixedTapeStability
