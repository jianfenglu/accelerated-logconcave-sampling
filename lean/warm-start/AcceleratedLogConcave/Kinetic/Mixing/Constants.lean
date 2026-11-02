import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Scalar absorption for the exact transport/collision clock inequality.
These lemmas assemble proved analytic estimates; they do not supply them. -/
namespace AcceleratedLogConcave.Kinetic

/-- Source absolute choices absorb both the microscopic and scalar errors. -/
theorem clock_error_absorption (θ h C₂ c₀ ρ : ℝ)
    (hC : 0 < C₂) (hρ : 0 < ρ)
    (hθρ : θ ≤ (192 * Real.sqrt 2 * ρ)⁻¹)
    (hθc : θ ≤ c₀ / 32) (hh : h ≤ c₀ / (8 * C₂)) :
    3 * Real.sqrt 2 * θ * ρ - 1 / 32 ≤ 0 ∧ c₀ / 2 ≤ c₀ - 8 * θ - 2 * C₂ * h := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hden : 0 < 192 * Real.sqrt 2 * ρ := by positivity
  have hx : θ * (192 * Real.sqrt 2 * ρ) ≤ 1 := by
    exact (le_div_iff₀ hden).mp (by simpa only [one_div] using hθρ)
  have hy : h * (8 * C₂) ≤ c₀ := (le_div_iff₀ (by positivity)).mp hh
  constructor <;> nlinarith

/-- The averaged source inequality implies a genuine multiplicative decrease.
The explicit coefficient c₀θ/2 is positive whenever c₀ and θ are positive. -/
theorem contraction_of_clock_estimate (Eout Ein N R Γ θ c₀ C₂ h ρ : ℝ)
    (hΓ : 0 ≤ Γ) (hθ : 0 ≤ θ) (hc : 0 ≤ c₀) (hN : 0 ≤ N) (hR : 0 ≤ R)
    (hE : Ein ≤ N)
    (hmicro : 3 * Real.sqrt 2 * θ * ρ - 1 / 32 ≤ 0)
    (hscalar : c₀ / 2 ≤ c₀ - 8 * θ - 2 * C₂ * h)
    (hstep : Eout ≤ Ein + Γ * (3 * Real.sqrt 2 * θ * ρ - 1 / 32) * R -
      θ * Γ * (c₀ - 8 * θ - 2 * C₂ * h) * N) :
    Eout ≤ (1 + (c₀ * θ / 2) * Γ)⁻¹ * Ein := by
  have hd : 0 ≤ (c₀ * θ / 2) * Γ := by positivity
  have hbad : Γ * (3 * Real.sqrt 2 * θ * ρ - 1 / 32) * R ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hΓ hmicro) hR
  have hgood := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscalar (mul_nonneg hθ hΓ)) hN
  have hdec : Eout ≤ Ein - (c₀ * θ / 2) * Γ * N := by nlinarith
  have hout : Eout ≤ N := (hdec.trans (sub_le_self _ (mul_nonneg hd hN))).trans hE
  have hmult := mul_le_mul_of_nonneg_left hout hd
  have hden : 0 < 1 + (c₀ * θ / 2) * Γ := by positivity
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ hden).mpr
  nlinarith

/-- The manuscript's absolute parameter choices meet the local transport,
OU and heat smallness conditions simultaneously. -/
theorem source_parameter_admissibility (h γ θ ρ : ℝ)
    (hh0 : 0 ≤ h) (hh : h ≤ 1/4) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ (Real.sqrt 2 / 32) / 32)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1/2) :
    0 ≤ γ*h ∧ γ*h ≤ 1/2 ∧
    0 ≤ θ*γ ∧ θ*γ ≤ 1 ∧
    0 ≤ 2*h^2*ρ^2 ∧ 2*h^2*ρ^2 ≤ 2*h^2 ∧
    |2*h^2*ρ| ≤ (Real.sqrt 2*h)/4 ∧
    (θ*γ)*Real.sqrt (2*h^2*ρ^2) ≤ 1/24 := by
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have hsmax : Real.sqrt 2 ≤ 2 := by nlinarith
  have hθsmall : θ ≤ 1/8 := by linarith
  have hΓ : γ*h ≤ h := by nlinarith
  have hε : θ*γ ≤ θ := by nlinarith
  have hρsq : ρ^2 ≤ 1/4 := by nlinarith
  have hhSq : h^2 ≤ 1/16 := by nlinarith
  have hτ : 2*h^2*ρ^2 ≤ 1/32 := by
    nlinarith [mul_le_mul_of_nonneg_left hρsq (show 0 ≤ 2*h^2 by positivity)]
  have hroot : Real.sqrt (2*h^2*ρ^2) ≤ 1/3 := by
    have he := Real.sq_sqrt (show 0 ≤ 2*h^2*ρ^2 by positivity)
    have hn := Real.sqrt_nonneg (2*h^2*ρ^2)
    nlinarith
  refine ⟨mul_nonneg hγ0 hh0,by linarith,mul_nonneg hθ0 hγ0,by linarith,
    by positivity,?_,?_,?_⟩
  · nlinarith [sq_nonneg h]
  · rw [abs_of_nonneg (by positivity : 0 ≤ 2*h^2*ρ)]
    have hx := mul_le_mul_of_nonneg_left hρ (show 0 ≤ 2*h^2 by positivity)
    have hy := mul_le_mul_of_nonneg_right hh hh0
    have hz := mul_le_mul_of_nonneg_right hs1 hh0
    nlinarith
  · have hn := Real.sqrt_nonneg (2*h^2*ρ^2)
    nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg hθ0 hγ0)]

end AcceleratedLogConcave.Kinetic
