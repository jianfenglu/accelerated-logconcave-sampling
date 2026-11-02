import AcceleratedLogConcave.Kinetic.Mixing.SourceContraction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Explicit exponential decay and an integer horizon for the actual source
contraction factor. These are scalar estimates, not an executable-law claim. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Kinetic

/-- The inverse factor decays at rate at least half its increment when the
increment is at most one. -/
theorem inverse_one_add_pow_le_exp {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    ((1+a)⁻¹)^k ≤ Real.exp (-(k:ℝ)*a/2) := by
  have hlog : a/2 ≤ Real.log (1+a) := by
    have hh := Real.le_log_one_add_of_nonneg ha
    have hd : a/2 ≤ 2*a/(a+2) := by
      apply (le_div_iff₀ (by positivity : 0 < a+2)).2
      nlinarith
    exact hd.trans hh
  have he : ((1+a)⁻¹)^k = Real.exp (-(k:ℝ)*Real.log (1+a)) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by positivity), inv_pow]
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k : (0:ℝ) ≤ k)]

/-- An integer horizon fixed from the scalar rate and requested decay exponent. -/
def referenceHorizon (a L : ℝ) : ℕ := ⌈2*L/a⌉₊

theorem inverse_one_add_horizon {a L : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ((1+a)⁻¹)^(referenceHorizon a L) ≤ Real.exp (-L) := by
  apply (inverse_one_add_pow_le_exp ha.le ha1 _).trans
  apply Real.exp_le_exp.mpr
  have hk := Nat.le_ceil (2*L/a)
  have hr : 2*L ≤ (referenceHorizon a L : ℝ)*a := by
    exact (div_le_iff₀ ha).mp hk
  linarith

/-- Specialization to the manuscript's proved phase contraction factor. -/
theorem sourceContractionFactor_horizon {θ m h L : ℝ}
    (ha : 0 < (Real.sqrt 2*θ/64)*(Real.sqrt m*h))
    (ha1 : (Real.sqrt 2*θ/64)*(Real.sqrt m*h) ≤ 1) :
    sourceContractionFactor θ m h ^
      referenceHorizon ((Real.sqrt 2*θ/64)*(Real.sqrt m*h)) L ≤ Real.exp (-L) := by
  exact inverse_one_add_horizon ha ha1

/-- The logarithmic exponent that pays the warm-density prefactor. -/
def warmMixingExponent (B ε : ℝ) : ℝ := Real.log (5*B/(12*ε^2))

theorem warm_prefactor_le {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    Real.sqrt ((5/3:ℝ)*Real.exp (-warmMixingExponent B ε))*Real.sqrt (B-1)/2 ≤ ε := by
  have hratio : 0 < 5*B/(12*ε^2) := by positivity
  have he : Real.exp (-warmMixingExponent B ε) = 12*ε^2/(5*B) := by
    rw [warmMixingExponent, Real.exp_neg, Real.exp_log hratio, inv_div]
  rw [he]
  have ha : 0 ≤ (5/3:ℝ)*(12*ε^2/(5*B)) := by positivity
  have hb : 0 ≤ B-1 := by linarith
  have hs := Real.sq_sqrt ha
  have ht := Real.sq_sqrt hb
  have heq : ((5/3:ℝ)*(12*ε^2/(5*B)))*(B-1) ≤ 4*ε^2 := by
    have hBp : 0 < B := by linarith
    field_simp
    nlinarith [sq_nonneg ε]
  have hp : 0 ≤ Real.sqrt ((5/3:ℝ)*(12*ε^2/(5*B))) * Real.sqrt (B-1) := by positivity
  have hprod : (Real.sqrt ((5/3:ℝ)*(12*ε^2/(5*B))) * Real.sqrt (B-1))^2 ≤ 4*ε^2 := by
    rw [mul_pow, hs, ht]
    exact heq
  nlinarith

/-- The selected integer count gives the desired TV-sized scalar envelope. -/
theorem warm_horizon_bound {a B ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hB : 1 ≤ B) (hε : 0 < ε) :
    Real.sqrt ((5/3:ℝ)*((1+a)⁻¹)^referenceHorizon a (warmMixingExponent B ε))*
      Real.sqrt (B-1)/2 ≤ ε := by
  apply le_trans _ (warm_prefactor_le hB hε)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (inverse_one_add_horizon ha ha1)
    (by norm_num))

end AcceleratedLogConcave.Kinetic
