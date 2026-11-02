import AcceleratedLogConcave.Gibbs.Normalization
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.MeasureTheory.Group.Integral

/-! Qualitative polynomial envelopes from a centered Gaussian sandwich.
Constants are left as finite Gaussian integrals. This avoids any dimensional
normalizer formula and makes no sharp-constant claim. -/
noncomputable section
open MeasureTheory
namespace AcceleratedLogConcave.Gibbs
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Translating the density to a derived center and subtracting its value
there leaves the actual normalized ratio unchanged. This is an exact
change of variables, not a comparison with a replacement probability law. -/
theorem normalized_exp_ratio_eq_centered (F g : E → ℝ) (z : E) :
    (∫ u, g u * Real.exp (-F u)) / (∫ u, Real.exp (-F u)) =
      (∫ w, g (z + w) * Real.exp (-(F (z + w) - F z))) /
        (∫ w, Real.exp (-(F (z + w) - F z))) := by
  have he (w : E) : Real.exp (-F (z + w)) =
      Real.exp (-F z) * Real.exp (-(F (z + w) - F z)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hn : (∫ u, g u * Real.exp (-F u)) = Real.exp (-F z) *
      (∫ w, g (z + w) * Real.exp (-(F (z + w) - F z))) := by
    rw [← integral_add_left_eq_self (f := fun u => g u * Real.exp (-F u)) z]
    simp_rw [he]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with w
    ring
  have hz : (∫ u, Real.exp (-F u)) = Real.exp (-F z) *
      (∫ w, Real.exp (-(F (z + w) - F z))) := by
    rw [← integral_add_left_eq_self (f := fun u => Real.exp (-F u)) z]
    simp_rw [he]
    exact integral_const_mul _ _
  rw [hn, hz, mul_div_mul_left _ _ (Real.exp_ne_zero _)]

/-- A centered two-sided quadratic sandwich gives a uniform polynomial
bound for every translated normalized moment. The constant depends only on
the sandwich parameters, moment order and ambient space, not on D or z. -/
theorem exists_polynomial_ratio_bound_of_quadratic_sandwich
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : E → ℝ, Continuous D →
      (∀ w, a * ‖w‖ ^ 2 ≤ D w) → (∀ w, D w ≤ b * ‖w‖ ^ 2) →
      ∀ z : E,
        (∫ w, (1 + ‖z + w‖) ^ n * Real.exp (-D w)) /
          (∫ w, Real.exp (-D w)) ≤ C * (1 + ‖z‖) ^ n := by
  let g (w : E) := Real.exp (-(a * ‖w‖ ^ 2))
  let h (w : E) := Real.exp (-(b * ‖w‖ ^ 2))
  have hga : Integrable g := by
    simpa only [g, inner_zero_left, sub_zero, neg_mul] using
      integrable_exp_quadratic_affine ha (0 : E)
  have hgb : Integrable h := by
    simpa only [h, inner_zero_left, sub_zero, neg_mul] using
      integrable_exp_quadratic_affine hb (0 : E)
  have hgn : Integrable (fun w : E => ‖w‖ ^ n * g w) := by
    apply integrable_norm_pow_mul_exp_neg_of_quadratic_lower_bound
      (F := fun w : E => a * ‖w‖ ^ 2) (a := 0) (by fun_prop) (0 : E) ha
    intro w
    simp
  let q (w : E) := 2 ^ (n - 1) * (1 + ‖w‖ ^ n) * g w
  have hq : Integrable q := by
    convert (hga.add hgn).const_mul (2 ^ (n - 1)) using 1
    ext w
    simp only [q, Pi.add_apply]
    ring
  have hqnonneg (w : E) : 0 ≤ q w := by
    dsimp [q, g]
    positivity
  have hHpos : 0 < ∫ w, h w := integral_exp_pos hgb
  let C := (∫ w, q w) / (∫ w, h w)
  refine ⟨C, div_nonneg (integral_nonneg hqnonneg) hHpos.le, ?_⟩
  intro D hD hlo hhi z
  have hI : Integrable (fun w => Real.exp (-D w)) := by
    apply integrable_exp_neg_of_quadratic_lower_bound hD.measurable (a := 0) (0 : E) ha
    intro w
    simpa only [inner_zero_left, zero_add] using hlo w
  have hZ : (∫ w, h w) ≤ ∫ w, Real.exp (-D w) := by
    apply integral_mono hgb hI
    intro w
    exact Real.exp_le_exp.mpr (neg_le_neg (hhi w))
  have hZpos : 0 < ∫ w, Real.exp (-D w) := hHpos.trans_le hZ
  have hbound (w : E) :
      (1 + ‖z + w‖) ^ n * Real.exp (-D w) ≤ (1 + ‖z‖) ^ n * q w := by
    have hlin : 1 + ‖z + w‖ ≤ (1 + ‖z‖) * (1 + ‖w‖) := by
      nlinarith [norm_add_le z w, norm_nonneg z, norm_nonneg w]
    have hp : (1 + ‖z + w‖) ^ n ≤
        (1 + ‖z‖) ^ n * (2 ^ (n - 1) * (1 + ‖w‖ ^ n)) := by
      calc
        _ ≤ ((1 + ‖z‖) * (1 + ‖w‖)) ^ n :=
          pow_le_pow_left₀ (by positivity) hlin n
        _ = (1 + ‖z‖) ^ n * (1 + ‖w‖) ^ n := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (by simpa only [one_pow] using add_pow_le zero_le_one (norm_nonneg w) n)
          (by positivity)
    have he : Real.exp (-D w) ≤ g w := Real.exp_le_exp.mpr (neg_le_neg (hlo w))
    calc
      _ ≤ ((1 + ‖z‖) ^ n * (2 ^ (n - 1) * (1 + ‖w‖ ^ n))) * g w :=
        mul_le_mul hp he (Real.exp_pos _).le (by positivity)
      _ = _ := by simp only [q]; ring
  have hnum : Integrable (fun w => (1 + ‖z + w‖) ^ n * Real.exp (-D w)) := by
    apply (hq.const_mul ((1 + ‖z‖) ^ n)).mono' (by fun_prop)
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound w
  have hN := integral_mono hnum (hq.const_mul ((1 + ‖z‖) ^ n)) hbound
  rw [integral_const_mul] at hN
  apply (div_le_iff₀ hZpos).mpr
  calc
    _ ≤ (1 + ‖z‖) ^ n * (∫ w, q w) := hN
    _ = (C * (1 + ‖z‖) ^ n) * (∫ w, h w) := by
      dsimp [C]
      field_simp [hHpos.ne']
    _ ≤ (C * (1 + ‖z‖) ^ n) * (∫ w, Real.exp (-D w)) :=
      mul_le_mul_of_nonneg_left hZ (by
        dsimp [C]
        exact mul_nonneg (div_nonneg (integral_nonneg hqnonneg) hHpos.le) (by positivity))

end AcceleratedLogConcave.Gibbs
