import AcceleratedLogConcave.Kinetic.ReferenceMixingHorizon

/-! Scalar phase counts at the actual smoothed curvature. The count is fixed
before any oracle answers and has the explicit square-root condition-number factor. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Kinetic

def sourceRate (θ κ h : ℝ) : ℝ :=
  (Real.sqrt 2*θ/64)*(h/Real.sqrt (κ+2*h^2))

theorem sourceContractionFactor_eq_rate (θ κ h : ℝ) :
    sourceContractionFactor θ ((κ+2*h^2)⁻¹) h = (1+sourceRate θ κ h)⁻¹ :=
  sourceContractionFactor_source_curvature θ κ h

theorem sourceRate_pos {θ κ h : ℝ} (hθ : 0 < θ) (hκ : 1 ≤ κ) (hh : 0 < h) :
    0 < sourceRate θ κ h := by
  unfold sourceRate
  positivity

theorem sourceRate_le_one {θ κ h : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hκ : 1 ≤ κ) (hh : 0 ≤ h) (hh1 : h ≤ 1) : sourceRate θ κ h ≤ 1 := by
  have hroot : 1 ≤ Real.sqrt (κ+2*h^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith [sq_nonneg h]
  have hr : h/Real.sqrt (κ+2*h^2) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have htwo : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
  have hc : Real.sqrt 2*θ/64 ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  exact (mul_le_mul hc hr (by positivity) (by norm_num)).trans (by norm_num)

theorem sourceRate_lower {θ κ h : ℝ} (hθ : 0 < θ) (hκ : 1 ≤ κ)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    θ*h/(128*Real.sqrt κ) ≤ sourceRate θ κ h := by
  have hk : 0 < κ := by linarith
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hk
  have hd : 0 < Real.sqrt (κ+2*h^2) := by positivity
  have hdle : Real.sqrt (κ+2*h^2) ≤ 2*Real.sqrt κ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hk.le]
      nlinarith
  have htwo : 1 ≤ Real.sqrt 2 := by norm_num [Real.le_sqrt]
  unfold sourceRate
  rw [show Real.sqrt 2*θ/64*(h/Real.sqrt (κ+2*h^2)) =
      (Real.sqrt 2*θ*h)/(64*Real.sqrt (κ+2*h^2)) by ring]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have ht : θ*h*Real.sqrt (κ+2*h^2) ≤ 2*θ*h*Real.sqrt κ := by
    nlinarith [mul_le_mul_of_nonneg_left hdle (by positivity : 0 ≤ θ*h)]
  nlinarith [mul_le_mul_of_nonneg_right htwo (by positivity : 0 ≤ θ*h*Real.sqrt κ)]

/-- An explicit every-run phase-count cap at the source curvature. -/
theorem sourceHorizon_le {θ κ h L : ℝ} (hθ : 0 < θ) (hκ : 1 ≤ κ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 ≤ L) :
    (referenceHorizon (sourceRate θ κ h) L : ℝ) ≤
      256*L*Real.sqrt κ/(θ*h)+1 := by
  have ha := sourceRate_pos hθ hκ hh
  have hlo := sourceRate_lower hθ hκ hh hh1
  have hk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr (by linarith)
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*L/sourceRate θ κ h)).le
  apply hc.trans
  apply add_le_add_left
  apply (div_le_iff₀ ha).2
  have hlo' := (div_le_iff₀ (by positivity : 0 < 128*Real.sqrt κ)).mp hlo
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < θ*h)).2
  nlinarith [mul_le_mul_of_nonneg_left hlo' hL]

end AcceleratedLogConcave.Kinetic
