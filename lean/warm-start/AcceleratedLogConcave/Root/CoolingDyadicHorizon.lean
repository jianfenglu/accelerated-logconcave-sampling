import AcceleratedLogConcave.Root.CoolingDyadicReference

/-! Explicit logarithmic count paying the actual dyadic terminal heat bias. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.CoolingDyadicHorizon

def count (d : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.log (max 1 (8*(d:ℝ)/ε^2))/Real.log 2⌉₊

theorem power_bound (d : ℕ) (ε : ℝ) : 8*(d:ℝ)/ε^2≤(2:ℝ)^count d ε := by
  have hmax : 0<max 1 (8*(d:ℝ)/ε^2) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (Real.log (max 1 (8*(d:ℝ)/ε^2))/Real.log 2)
  have hl : Real.log (max 1 (8*(d:ℝ)/ε^2))≤(count d ε:ℝ)*Real.log 2 :=
    (div_le_iff₀ hlog).mp hc
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log hmax] at he
  have hp : Real.exp ((count d ε:ℝ)*Real.log 2)=(2:ℝ)^count d ε := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  rw [hp] at he
  exact (le_max_right _ _).trans he

theorem bias_payment (d : ℕ) {h ε : ℝ} (hh : 0≤h) (hh1 : h≤1) (hε : 0<ε) :
    Real.sqrt ((d:ℝ)*(2*h^2/(2:ℝ)^count d ε))/2≤ε/4 := by
  have hpow : 0<(2:ℝ)^count d ε := by positivity
  have hb := (div_le_iff₀ (sq_pos_of_pos hε)).mp (power_bound d ε)
  have hs : h^2≤1 := by nlinarith
  have hprod : 2*(d:ℝ)*h^2≤2*(d:ℝ) := by nlinarith [(Nat.cast_nonneg d : (0:ℝ)≤d)]
  have hinside : (d:ℝ)*(2*h^2/(2:ℝ)^count d ε)≤(ε/2)^2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hpow).mpr
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hinside
  rw [Real.sqrt_sq (by positivity : 0≤ε/2)] at hsqrt
  linarith

theorem count_le (d : ℕ) (ε : ℝ) :
    (count d ε:ℝ)≤1+Real.log (max 1 (8*(d:ℝ)/ε^2))/Real.log 2 := by
  have hn : 0≤Real.log (max 1 (8*(d:ℝ)/ε^2))/Real.log 2 :=
    div_nonneg (Real.log_nonneg (le_max_left _ _)) (Real.log_pos (by norm_num)).le
  exact (Nat.ceil_lt_add_one hn).le.trans_eq (by ring)

@[simp] theorem count_zero (ε : ℝ) : count 0 ε=0 := by simp [count]

/-- Concrete original-data terminal decoder bias at the prescribed logarithmic
count. No implementation or warmness conclusion is used in this supplier. -/
theorem terminal_bias_paid {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (hV : ContDiff ℝ 2 V) {κ h ε : ℝ} (hκ : 1≤κ)
    (hlo : ∀ x v,κ⁻¹*‖v‖^2≤fderiv ℝ (fderiv ℝ V) x v v)
    (hup : ∀ x v,fderiv ℝ (fderiv ℝ V) x v v≤‖v‖^2)
    (hh : 0<h) (hh1 : h≤1) (hε : 0<ε) :
    let hI := Gibbs.integrable_exp_neg_of_hessian_lower hV (by positivity : 0<κ⁻¹) hlo
    let : IsProbabilityMeasure (volume.tilted (fun x => -V x)) := isProbabilityMeasure_tilted hI
    let : IsMarkovKernel (CoolingDyadicReference.chain V hV.continuous.measurable h (count d ε)) :=
      CoolingDyadicReference.chain_markov V hV.continuous.measurable h hI (count d ε)
    let : IsProbabilityMeasure (Channels.forward (volume.tilted (fun x => -V x))
        (CoolingDyadicReference.variance h 0)) := by unfold Channels.forward; infer_instance
    Probability.totalVariationDistance
      (CoolingDyadicReference.chain V hV.continuous.measurable h (count d ε) ∘ₘ
        Channels.forward (volume.tilted (fun x => -V x)) (CoolingDyadicReference.variance h 0))
      (volume.tilted (fun x => -V x))≤ε/4 :=
  (CoolingDyadicReference.terminal_bias V hV.continuous.measurable h hV hκ hlo hup hh (count d ε)).trans
    (bias_payment d hh.le hh1 hε)
end AcceleratedLogConcave.Root.CoolingDyadicHorizon
