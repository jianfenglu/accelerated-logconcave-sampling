import AcceleratedLogConcave.Kinetic.SourcePhaseCount

/-! Scalar original-source phase and work inventory after the dimension choice
`h = D ^ (-e)` and the joint warmness bound `B = D ^ Cw`. These statements
do not identify an executable output law with the reference channel. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Kinetic

/-- A dimension-independent coefficient for the actual ceiling horizon. -/
def sourceDimensionPhaseConstant (θ Cw ε e : ℝ) : ℝ :=
  1 + 256 * (Real.log (5 / (12 * ε ^ 2)) + Cw / e) / θ

theorem log_dimension_le_rpow_div {D e : ℝ} (hD : 1 ≤ D) (he : 0 < e) :
    Real.log D ≤ D ^ e / e := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hh := Real.add_one_le_exp (e * Real.log D)
  have hexp : Real.exp (e * Real.log D) = D ^ e := by
    rw [Real.rpow_def_of_pos hDp]
    congr 1
    ring
  rw [hexp] at hh
  apply (le_div_iff₀ he).2
  nlinarith

theorem warmMixingExponent_dimension (D Cw ε : ℝ)
    (hD : 1 ≤ D) (hε : 0 < ε) :
    warmMixingExponent (D ^ Cw) ε =
      Real.log (5 / (12 * ε ^ 2)) + Cw * Real.log D := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have ha : 0 < 5 / (12 * ε ^ 2) := by positivity
  have hB : 0 < D ^ Cw := Real.rpow_pos_of_pos hDp _
  unfold warmMixingExponent
  have hrewrite : 5 * D ^ Cw / (12 * ε ^ 2) =
      (5 / (12 * ε ^ 2)) * D ^ Cw := by ring
  rw [hrewrite, Real.log_mul ha.ne' hB.ne', Real.log_rpow hDp]

theorem warmMixingExponent_dimension_nonneg {D Cw ε : ℝ}
    (hD : 1 ≤ D) (hCw : 0 ≤ Cw) (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    0 ≤ warmMixingExponent (D ^ Cw) ε := by
  rw [warmMixingExponent_dimension D Cw ε hD hε]
  have hratio : 1 ≤ 5 / (12 * ε ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 12 * ε ^ 2)).2
    nlinarith [sq_nonneg ε]
  have hlog : 0 ≤ Real.log (5 / (12 * ε ^ 2)) := Real.log_nonneg hratio
  have hDlog : 0 ≤ Real.log D := Real.log_nonneg hD
  positivity

theorem warmMixingExponent_dimension_le {D Cw ε e : ℝ}
    (hD : 1 ≤ D) (hCw : 0 ≤ Cw) (he : 0 < e)
    (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    warmMixingExponent (D ^ Cw) ε ≤
      (Real.log (5 / (12 * ε ^ 2)) + Cw / e) * D ^ e := by
  rw [warmMixingExponent_dimension D Cw ε hD hε]
  have hDpow : 1 ≤ D ^ e := Real.one_le_rpow hD he.le
  have hratio : 1 ≤ 5 / (12 * ε ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 12 * ε ^ 2)).2
    nlinarith [sq_nonneg ε]
  have hlog : 0 ≤ Real.log (5 / (12 * ε ^ 2)) := Real.log_nonneg hratio
  have hlogD := log_dimension_le_rpow_div hD he
  have hC := mul_le_mul_of_nonneg_left hlogD hCw
  have hC' : Cw * Real.log D ≤ (Cw / e) * D ^ e := by
    calc
      _ ≤ Cw * (D ^ e / e) := hC
      _ = _ := by ring
  nlinarith [mul_nonneg hlog (sub_nonneg.mpr hDpow)]

theorem sourceDimensionPhaseConstant_pos {θ Cw ε e : ℝ}
    (hθ : 0 < θ) (hCw : 0 ≤ Cw) (he : 0 < e)
    (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    0 < sourceDimensionPhaseConstant θ Cw ε e := by
  have hratio : 1 ≤ 5 / (12 * ε ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 12 * ε ^ 2)).2
    nlinarith [sq_nonneg ε]
  have hlog : 0 ≤ Real.log (5 / (12 * ε ^ 2)) := Real.log_nonneg hratio
  unfold sourceDimensionPhaseConstant
  positivity

/-- The selected source rate lies in the range required by the reference
contraction argument. -/
theorem source_dimension_rate_range {θ κ D e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hκ : 1 ≤ κ)
    (hD : 1 ≤ D) (he : 0 < e) :
    0 < sourceRate θ κ (D ^ (-e)) ∧
      sourceRate θ κ (D ^ (-e)) ≤ 1 := by
  have hsmall : 0 < D ^ (-e) := Real.rpow_pos_of_pos (by linarith) _
  have hsmall1 : D ^ (-e) ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hD
      (show -e ≤ 0 by linarith)
    simpa only [Real.rpow_zero] using hh
  exact ⟨sourceRate_pos hθ hκ hsmall,
    sourceRate_le_one hθ.le hθ1 hκ hsmall.le hsmall1⟩

/-- The actual ceiling horizon at `h = D ^ (-e)` with `B = D ^ Cw`.
The coefficient depends only on the displayed scalar parameters. -/
theorem source_dimension_horizon_le {θ κ D e Cw ε : ℝ}
    (hθ : 0 < θ) (hκ : 1 ≤ κ) (hD : 1 ≤ D)
    (he : 0 < e) (hCw : 0 ≤ Cw)
    (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    (referenceHorizon (sourceRate θ κ (D ^ (-e)))
      (warmMixingExponent (D ^ Cw) ε) : ℝ) ≤
        sourceDimensionPhaseConstant θ Cw ε e * Real.sqrt κ * D ^ (2 * e) := by
  let u := D ^ e
  let A := Real.log (5 / (12 * ε ^ 2)) + Cw / e
  let L := warmMixingExponent (D ^ Cw) ε
  let x := Real.sqrt κ
  have hD0 : 0 ≤ D := by linarith
  have hu : 1 ≤ u := Real.one_le_rpow hD he.le
  have hup : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hx : 1 ≤ x := by
    apply (Real.le_sqrt (by norm_num) (by linarith : 0 ≤ κ)).2
    simpa only [one_pow] using hκ
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsmall : 0 < D ^ (-e) := Real.rpow_pos_of_pos (by linarith) _
  have hsmall1 : D ^ (-e) ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hD
      (show -e ≤ 0 by linarith)
    simpa only [Real.rpow_zero] using hh
  have hL : 0 ≤ L := warmMixingExponent_dimension_nonneg hD hCw hε hε4
  have hLupper : L ≤ A * u := warmMixingExponent_dimension_le hD hCw he hε hε4
  have hbase := sourceHorizon_le hθ hκ hsmall hsmall1 hL
  have hD2 : D ^ (2 * e) = u ^ 2 := by
    rw [show 2 * e = e + e by ring, Real.rpow_add (by linarith : 0 < D)]
    dsimp [u]
    ring
  have hratio : 1 ≤ 5 / (12 * ε ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 12 * ε ^ 2)).2
    nlinarith [sq_nonneg ε]
  have hA : 0 ≤ A := by
    dsimp [A]
    have hlog : 0 ≤ Real.log (5 / (12 * ε ^ 2)) := Real.log_nonneg hratio
    positivity
  have hsimp : 256 * L * x / (θ * D ^ (-e)) + 1 =
      256 * L * x * u / θ + 1 := by
    rw [Real.rpow_neg hD0]
    dsimp [u]
    field_simp
  have hmul : 256 * L * x * u / θ ≤ 256 * (A * u) * x * u / θ := by
    gcongr
  have hunit : 1 ≤ x * u ^ 2 := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ x * u ^ 2 := mul_le_mul hx (by nlinarith [hu]) (by norm_num)
        (by linarith)
  calc
    (referenceHorizon (sourceRate θ κ (D ^ (-e))) L : ℝ) ≤
        256 * L * x / (θ * D ^ (-e)) + 1 := hbase
    _ = 256 * L * x * u / θ + 1 := hsimp
    _ ≤ 256 * (A * u) * x * u / θ + 1 := by linarith [hmul]
    _ ≤ sourceDimensionPhaseConstant θ Cw ε e * x * D ^ (2 * e) := by
      rw [hD2]
      dsimp [sourceDimensionPhaseConstant, A]
      have hh : 0 < θ := hθ
      have hfrac : 256 * (A * u) * x * u / θ = 256 * A / θ * x * u ^ 2 := by ring
      rw [hfrac]
      nlinarith [hunit]

/-- The scalar phase count times the original source per-call exponential
inventory at `y = e * log D`. This is not a complete algorithm work bound. -/
theorem source_dimension_phase_work_le {θ κ D e Cw ε : ℝ}
    (hθ : 0 < θ) (hκ : 1 ≤ κ) (hD : 1 ≤ D)
    (he : 0 < e) (hCw : 0 ≤ Cw)
    (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    (referenceHorizon (sourceRate θ κ (D ^ (-e)))
      (warmMixingExponent (D ^ Cw) ε) : ℝ) *
        Real.exp ((e * Real.log D) / 64) ≤
      sourceDimensionPhaseConstant θ Cw ε e * Real.sqrt κ * D ^ (3 * e) := by
  have hDp : 0 < D := by linarith
  have hexp : Real.exp ((e * Real.log D) / 64) ≤ D ^ e := by
    calc
      Real.exp ((e * Real.log D) / 64) = D ^ (e / 64) := by
        rw [Real.rpow_def_of_pos hDp]
        congr 1
        ring
      _ ≤ D ^ e := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hcoeff : 0 ≤ sourceDimensionPhaseConstant θ Cw ε e * Real.sqrt κ *
      D ^ (2 * e) := by
    have hc := sourceDimensionPhaseConstant_pos hθ hCw he hε hε4
    positivity
  have hpow : D ^ (2 * e) * D ^ e = D ^ (3 * e) := by
    rw [← Real.rpow_add hDp]
    congr 1
    ring
  calc
    (referenceHorizon (sourceRate θ κ (D ^ (-e)))
      (warmMixingExponent (D ^ Cw) ε) : ℝ) *
        Real.exp ((e * Real.log D) / 64) ≤
      (sourceDimensionPhaseConstant θ Cw ε e * Real.sqrt κ * D ^ (2 * e)) *
        Real.exp ((e * Real.log D) / 64) :=
      mul_le_mul_of_nonneg_right
        (source_dimension_horizon_le hθ hκ hD he hCw hε hε4) (Real.exp_nonneg _)
    _ ≤ (sourceDimensionPhaseConstant θ Cw ε e * Real.sqrt κ * D ^ (2 * e)) *
        D ^ e := mul_le_mul_of_nonneg_left hexp hcoeff
    _ = sourceDimensionPhaseConstant θ Cw ε e * Real.sqrt κ * D ^ (3 * e) := by
      rw [mul_assoc, hpow]

/-- The scalar inventory fits a prescribed dimension exponent whenever
`e ≤ η/3`. No executable call count or end-to-end output law is asserted. -/
theorem source_dimension_phase_work_le_target {θ κ D e Cw ε η : ℝ}
    (hθ : 0 < θ) (hκ : 1 ≤ κ) (hD : 1 ≤ D)
    (he : 0 < e) (hCw : 0 ≤ Cw)
    (hε : 0 < ε) (hε4 : ε < 1 / 4)
    (heη : e ≤ η / 3) :
    (referenceHorizon (sourceRate θ κ (D ^ (-e)))
      (warmMixingExponent (D ^ Cw) ε) : ℝ) *
        Real.exp ((e * Real.log D) / 64) ≤
      sourceDimensionPhaseConstant θ Cw ε e * Real.sqrt κ * D ^ η := by
  have hc := sourceDimensionPhaseConstant_pos hθ hCw he hε hε4
  have hpow : D ^ (3 * e) ≤ D ^ η :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  exact (source_dimension_phase_work_le hθ hκ hD he hCw hε hε4).trans
    (mul_le_mul_of_nonneg_left hpow (by positivity))

end AcceleratedLogConcave.Kinetic
