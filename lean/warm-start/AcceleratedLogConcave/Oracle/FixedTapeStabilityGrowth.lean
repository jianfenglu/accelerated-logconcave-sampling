import AcceleratedLogConcave.Oracle.FixedTapeChildStability

/-! Finite scalar growth for the actual fixed-tape block bounds. These are
polynomials, with no contraction, precision induction or schedule assertion. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.FixedTapeStability
open scoped BigOperators

/-- Increasing a child constant preserves the same all-momenta, full-tape IH. -/
theorem ChildStable.mono {d c : ℕ} {p : Program c .point} {coeff : Fin c → ℝ}
    {G : Point d → Point d} {κ κ' : ℝ} (h : ChildStable p coeff G κ) (hκ : κ ≤ κ') :
    ChildStable p coeff G κ' := by
  intro P x y z rest
  exact (h P x y z rest).trans (mul_le_mul_of_nonneg_right hκ (norm_nonneg _))

/-- Initialization and N synchronous layers give N+1 powers. -/
def powerSum (N : ℕ) (q : ℝ) : ℝ := ∑ j ∈ Finset.range (N+1), q^j

@[simp] theorem powerSum_zero_layers (q : ℝ) : powerSum 0 q = 1 := by
  simp [powerSum]

@[simp] theorem powerSum_zero (N : ℕ) : powerSum N 0 = 1 := by
  simp [powerSum]

theorem powerSum_nonneg (N : ℕ) {q : ℝ} (hq : 0 ≤ q) : 0 ≤ powerSum N q :=
  Finset.sum_nonneg fun j _ => pow_nonneg hq j

theorem powerSum_mono {N N' : ℕ} {q q' : ℝ}
    (hN : N ≤ N') (hq : 0 ≤ q) (hqq : q ≤ q') : powerSum N q ≤ powerSum N' q' := by
  apply (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hq hqq j).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun j _ _ => pow_nonneg (hq.trans hqq) j)

/-- The sampling child IH constant is κ, while its final row has mass r. -/
def samplingGrowth (N : ℕ) (κ r : ℝ) : ℝ := κ*r*powerSum N (κ*r^2)

theorem samplingGrowth_nonneg (N : ℕ) {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r) :
    0 ≤ samplingGrowth N κ r := by
  exact mul_nonneg (mul_nonneg hκ hr) (powerSum_nonneg N (by positivity))

theorem samplingGrowth_mono {N N' : ℕ} {κ κ' r r' : ℝ}
    (hN : N ≤ N') (hκ : 0 ≤ κ) (hr : 0 ≤ r) (hκκ : κ ≤ κ') (hrr : r ≤ r') :
    samplingGrowth N κ r ≤ samplingGrowth N' κ' r' := by
  have hκ' := hκ.trans hκκ
  have hr' := hr.trans hrr
  have hprod : κ*r^2 ≤ κ'*r'^2 :=
    mul_le_mul hκκ (pow_le_pow_left₀ hr hrr 2) (sq_nonneg _) (hκ.trans hκκ)
  exact mul_le_mul (mul_le_mul hκκ hrr hr (hκ.trans hκκ))
    (powerSum_mono hN (by positivity) hprod)
    (powerSum_nonneg N (by positivity)) (by positivity)

@[simp] theorem samplingGrowth_zero_layers (κ r : ℝ) : samplingGrowth 0 κ r = κ*r := by
  simp [samplingGrowth]

@[simp] theorem samplingGrowth_zero_child (N : ℕ) (r : ℝ) : samplingGrowth N 0 r = 0 := by
  simp [samplingGrowth]

@[simp] theorem samplingGrowth_zero_radius (N : ℕ) (κ : ℝ) : samplingGrowth N κ 0 = 0 := by
  simp [samplingGrowth]

/-- κm bounds the main/final mean children; κs bounds both families inside the
private sampler. Its radius is the actual parent radius, and b is the anchor scale. -/
def meanGrowth (N : ℕ) (κm κs r b A : ℝ) : ℝ :=
  κm*(1+r*b^2*samplingGrowth N κs r)*powerSum N (κm*A)

theorem meanGrowth_nonneg (N : ℕ) {κm κs r b A : ℝ}
    (hm : 0 ≤ κm) (hs : 0 ≤ κs) (hr : 0 ≤ r) (hA : 0 ≤ A) :
    0 ≤ meanGrowth N κm κs r b A := by
  have hp := samplingGrowth_nonneg N hs hr
  have hq := powerSum_nonneg N (mul_nonneg hm hA)
  dsimp only [meanGrowth]
  positivity

/-- Monotonicity uses b² directly, so no sign restriction on b is needed. -/
theorem meanGrowth_mono {N N' : ℕ} {κm κm' κs κs' r r' b b' A A' : ℝ}
    (hN : N ≤ N') (hm : 0 ≤ κm) (hs : 0 ≤ κs) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hmm : κm ≤ κm') (hss : κs ≤ κs') (hrr : r ≤ r') (hbb : b^2 ≤ b'^2)
    (hAA : A ≤ A') : meanGrowth N κm κs r b A ≤ meanGrowth N' κm' κs' r' b' A' := by
  have hm' := hm.trans hmm
  have hr' := hr.trans hrr
  have hp := samplingGrowth_nonneg N hs hr
  have hp' := samplingGrowth_nonneg N' (hs.trans hss) (hr.trans hrr)
  have hsp := samplingGrowth_mono hN hs hr hss hrr
  have ha : r*b^2 ≤ r'*b'^2 := mul_le_mul hrr hbb (sq_nonneg _) (hr.trans hrr)
  have hinner : 1+r*b^2*samplingGrowth N κs r ≤
      1+r'*b'^2*samplingGrowth N' κs' r' := by
    exact add_le_add le_rfl (mul_le_mul ha hsp hp (by positivity))
  have hq := powerSum_mono hN (mul_nonneg hm hA)
    (mul_le_mul hmm hAA hA (hm.trans hmm))
  exact mul_le_mul (mul_le_mul hmm hinner (by positivity) (hm.trans hmm)) hq
    (powerSum_nonneg N (mul_nonneg hm hA)) (by positivity)

@[simp] theorem meanGrowth_zero_layers (κm κs r b A : ℝ) :
    meanGrowth 0 κm κs r b A = κm*(1+r*b^2*(κs*r)) := by
  simp [meanGrowth]

@[simp] theorem meanGrowth_zero_child (N : ℕ) (κs r b A : ℝ) :
    meanGrowth N 0 κs r b A = 0 := by
  simp [meanGrowth]

@[simp] theorem meanGrowth_zero_radius (N : ℕ) (κm κs b A : ℝ) :
    meanGrowth N κm κs 0 b A = κm*powerSum N (κm*A) := by
  simp [meanGrowth]

@[simp] theorem meanGrowth_zero_sampler (N : ℕ) (κm r b A : ℝ) :
    meanGrowth N κm 0 r b A = κm*powerSum N (κm*A) := by
  simp [meanGrowth]

end AcceleratedLogConcave.Oracle.FixedTapeStability
