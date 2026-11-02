import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Scale normalization for the Gaussian angle specialization of the phase
engine. Keeping the engine radius distinct from the terminal smoothing radius
avoids an unnecessary third inverse-radius factor per angle derivative. -/
noncomputable section
namespace AcceleratedLogConcave.Analysis.AnglePhase

def radius (R q : ℝ) : ℝ := min 1 (R/q)

theorem radius_pos {R q : ℝ} (hR : 0 < R) (hq : 0 < q) : 0 < radius R q :=
  lt_min (by norm_num) (div_pos hR hq)

theorem radius_le_one (R q : ℝ) : radius R q ≤ 1 := min_le_left _ _

theorem pullback_ratio_le_inv_radius {R q : ℝ} (hR : 0 < R) (hq : 0 < q) :
    q/R ≤ (radius R q)⁻¹ := by
  by_cases hqr : q ≤ R
  · have hh : 1 ≤ R/q := (le_div_iff₀ hq).mpr (by simpa using hqr)
    rw [radius,min_eq_left hh,inv_one]
    exact (div_le_one hR).mpr hqr
  · have hrq : R ≤ q := le_of_lt (lt_of_not_ge hqr)
    have hh : R/q ≤ 1 := (div_le_one hq).mpr hrq
    rw [radius,min_eq_right hh,inv_div]

theorem normalized_speed_le {R q : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1) (hhalf : R ≤ 2*q) :
    q⁻¹ / (radius R q)^2 ≤ 2/R^2 := by
  by_cases hqr : q ≤ R
  · have hh : 1 ≤ R/q := (le_div_iff₀ hq).mpr (by simpa using hqr)
    rw [radius,min_eq_left hh,one_pow,div_one,← one_div]
    apply (div_le_div_iff₀ hq (sq_pos_of_pos hR)).mpr
    nlinarith
  · have hrq : R ≤ q := le_of_lt (lt_of_not_ge hqr)
    have hh : R/q ≤ 1 := (div_le_one hq).mpr hrq
    rw [radius,min_eq_right hh]
    calc
      q⁻¹ / (R/q)^2 = q/R^2 := by field_simp
      _ ≤ 2/R^2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg R)

end AcceleratedLogConcave.Analysis.AnglePhase
