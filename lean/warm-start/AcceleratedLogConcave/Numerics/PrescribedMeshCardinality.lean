import AcceleratedLogConcave.Numerics.ConditionalGeometricMesh
import AcceleratedLogConcave.Numerics.ForwardMeshBudget

/-! Cardinality bounds for the prescribed logarithmic probability meshes.
The ceiling denominator is exactly h0. The extra retained kernel origin is
charged explicitly. Generic counts include zero-length intervals; concrete
IntervalMesh constructors retain their positive-length guards. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.PrescribedMeshCardinality
open AffineGraph GeometricMesh
open scoped BigOperators

/-- Real logarithmic budget; no rounded natural node budget is introduced. -/
def meshBudget (R h₀ : ℝ) : ℝ := (1+|Real.log R|)/h₀

theorem meshBudget_ge_one {R h₀ : ℝ} (hh : 0 < h₀) (hhhalf : h₀ ≤ 1/2) :
    1 ≤ meshBudget R h₀ := by
  unfold meshBudget
  apply (le_div_iff₀ hh).2
  nlinarith [abs_nonneg (Real.log R)]

/-- A common endpoint gap pays the logarithmic span without changing h0. -/
theorem logSpan_le {R a b : ℝ} (hR : 0 < R) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b < 1) (hgap : R^2/16 ≤ 1-b) :
    logSpan a b ≤ 15+2*|Real.log R| := by
  have hlo := Real.log_le_log (by positivity : 0 < R^2/16) hgap
  rw [Real.log_div (pow_ne_zero _ hR.ne') (by norm_num), Real.log_pow] at hlo
  have hla : Real.log (1-a) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
  have hr := neg_abs_le (Real.log R)
  unfold logSpan
  norm_num at hlo hc
  linarith

/-- Ceiling nodes plus the retained origin, including the zero-length case. -/
theorem count_with_origin_le (m : ℕ) (hm : 2 ≤ m) {R a b h₀ : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    (hh : 0 < h₀) (hhhalf : h₀ ≤ 1/2) (hgap : R^2/16 ≤ 1-b) :
    ((cellCount a b h₀*m+1 : ℕ) : ℝ) ≤ 16*(m : ℝ)*meshBudget R h₀ := by
  have hs := logSpan_le hR ha hab hb hgap
  have hc := cellCount_le_span_div_add_one hab hb hh
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmul := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg m)
  have hspan := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg m)
  have hhM := mul_le_mul_of_nonneg_left hhhalf (Nat.cast_nonneg m)
  have hlogM := mul_nonneg (Nat.cast_nonneg m) (abs_nonneg (Real.log R))
  have hcount := mul_le_mul_of_nonneg_right hmul hh.le
  have hcancel : (logSpan a b / h₀+1)*(m:ℝ)*h₀ = (logSpan a b+h₀)*(m:ℝ) := by
    field_simp [hh.ne']
  rw [hcancel] at hcount
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  unfold meshBudget
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hh).2
  nlinarith

theorem backward_gap {R : ℝ} (hR : 0 < R) (hRh : R ≤ 1/2) :
    R^2/16 ≤ 1-backwardEnd R := by
  have hb := kernel_endpoint_bounds hR hRh
  have hs := Real.sq_sqrt (show 0 ≤ 1-R^2 by nlinarith)
  unfold backwardEnd
  nlinarith [sq_nonneg (Real.sqrt (1-R^2)-1), sq_nonneg R]

theorem conditional_gap {R : ℝ} (hR : 0 < R) (hRh : R ≤ 1/2) :
    R^2/16 ≤ 1-conditionalEnd := by
  have hs : 1/Real.sqrt 2 ≤ (3:ℝ)/4 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))).2
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg 2]
  unfold conditionalEnd
  nlinarith

/-- tau=1 is included and gives a nondegenerate sampling endpoint. -/
theorem sampling_gap {R τ : ℝ} (hR : 0 < R) (hRτ : R ≤ τ) (hτ : τ ≤ 1) :
    R^2/16 ≤ 1-samplingEnd τ := by
  let s := Real.sqrt (1+τ^2/4)
  have hτ0 : 0 < τ := hR.trans_le hRτ
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs : s^2 = 1+τ^2/4 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by nlinarith
  have hs32 : s ≤ 3/2 := by nlinarith [sq_nonneg (1-τ)]
  have hprod : s*(s+1) ≤ 4 := by nlinarith
  have he : τ^2 = 4*(s-1)*(s+1) := by nlinarith
  have hg : (τ^2/16)*s ≤ s-1 := by
    calc
      _ = (s-1)*(s*(s+1)/4) := by rw [he]; ring
      _ ≤ (s-1)*1 := mul_le_mul_of_nonneg_left ((div_le_one₀ (by norm_num)).2 hprod) (by linarith)
      _ = _ := mul_one _
  have hgap : τ^2/16 ≤ 1-s⁻¹ := by
    apply (mul_le_mul_iff_left₀ hs0).mp
    simpa only [sub_mul, one_mul, inv_mul_cancel₀ hs0.ne'] using hg
  have hsq : R^2 ≤ τ^2 := pow_le_pow_left₀ hR.le hRτ 2
  exact (div_le_div_of_nonneg_right hsq (by norm_num)).trans hgap

theorem sampling_endpoint {R τ : ℝ} (hR : 0 < R) (hRτ : R ≤ τ) (hτ : τ ≤ 1) :
    0 < samplingEnd τ ∧ samplingEnd τ < 1 := by
  have hg := sampling_gap hR hRτ hτ
  constructor
  · unfold samplingEnd; positivity
  · nlinarith [sq_pos_of_pos hR]

theorem private_tau_mem {R : ℝ} (hR : 0 < R) (hRh : R ≤ 1/2) :
    R ≤ R/backwardEnd R ∧ R/backwardEnd R ≤ 1 := by
  have hb := kernel_endpoint_bounds hR hRh
  have hb0 : 0 < backwardEnd R := by change 0 < Real.sqrt (1-R^2); linarith
  constructor
  · apply (le_div_iff₀ hb0).2
    exact mul_le_of_le_one_right hR.le hb.2.le
  · apply (div_le_one₀ hb0).2
    exact hRh.trans hb.1

theorem backward_count_le (m : ℕ) (hm : 2 ≤ m) {R a h₀ : ℝ}
    (hR : 0 < R) (hRh : R ≤ 1/2) (ha : 0 ≤ a) (hab : a ≤ backwardEnd R)
    (hh : 0 < h₀) (hhh : h₀ ≤ 1/2) :
    ((cellCount a (backwardEnd R) h₀*m+1 : ℕ) : ℝ) ≤ 16*(m:ℝ)*meshBudget R h₀ :=
  count_with_origin_le m hm hR ha hab (kernel_endpoint_bounds hR hRh).2 hh hhh (backward_gap hR hRh)

theorem conditional_count_le (m : ℕ) (hm : 2 ≤ m) {R a h₀ : ℝ}
    (hR : 0 < R) (hRh : R ≤ 1/2) (ha : 0 ≤ a) (hab : a ≤ conditionalEnd)
    (hh : 0 < h₀) (hhh : h₀ ≤ 1/2) :
    ((cellCount a conditionalEnd h₀*m+1 : ℕ) : ℝ) ≤ 16*(m:ℝ)*meshBudget R h₀ :=
  count_with_origin_le m hm hR ha hab conditionalEnd_lt_one hh hhh (conditional_gap hR hRh)

theorem sampling_count_le (m : ℕ) (hm : 2 ≤ m) {R τ a h₀ : ℝ}
    (hR : 0 < R) (hRτ : R ≤ τ) (hτ : τ ≤ 1) (ha : 0 ≤ a) (hab : a ≤ samplingEnd τ)
    (hh : 0 < h₀) (hhh : h₀ ≤ 1/2) :
    ((cellCount a (samplingEnd τ) h₀*m+1 : ℕ) : ℝ) ≤ 16*(m:ℝ)*meshBudget R h₀ :=
  count_with_origin_le m hm hR ha hab (sampling_endpoint hR hRτ hτ).2 hh hhh (sampling_gap hR hRτ hτ)
end AcceleratedLogConcave.Numerics.PrescribedMeshCardinality
