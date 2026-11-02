import AcceleratedLogConcave.Conditional.ScaledJetPolynomial

/-! Nonsingular actual spatial coefficient transitions, including probability time zero. -/
noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The center-jet definition gives this transition without dividing by time. -/
theorem fderiv_scaledJet_apply (q : ℕ) (F : E → ℝ) (x : E) (r t : ℝ)
    (y v : E) (a : Fin q → E) :
    (fderiv ℝ (scaledJet q F x r t) y v) a =
      t • scaledJet (q+1) F x r t y (Fin.cons v a) := by
  unfold scaledJet
  rw [fderiv_comp_smul]
  simp only [smul_apply,
    iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]

 theorem contDiff_scaledJet_spatial (q : ℕ) {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hhi : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖^2)
    (x : E) (r : ℝ) {t : ℝ} (htlo : -1 < t) (hthi : t < 1) :
    ContDiff ℝ ∞ (scaledJet q F x r t) := by
  have hc : ContDiff ℝ ∞ (fun y : E => (t,y)) := contDiff_const.prodMk contDiff_id
  have hh := (contDiffOn_scaledJet q hF hlo hhi x r).comp
    hc.contDiffOn (s := Set.univ) (fun _ _ => And.intro htlo hthi)
  exact contDiffOn_univ.mp hh

 theorem fderiv_scaledJet_coordinate (q : ℕ) {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hhi : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖^2)
    (x : E) (r : ℝ) {t : ℝ} (htlo : -1 < t) (hthi : t < 1)
    (y v w : E) (a : Fin q → E) :
    fderiv ℝ (fun z => inner ℝ w (scaledJet q F x r t z a)) y v =
      t * inner ℝ w (scaledJet (q+1) F x r t y (Fin.cons v a)) := by
  have hj := (contDiff_scaledJet_spatial q hF hlo hhi x r htlo hthi).differentiable (by simp)
  have ha := (hj y).continuousMultilinear_apply_const a
  rw [fderiv_inner_apply ℝ (differentiableAt_const w) ha]
  rw [fderiv_continuousMultilinear_apply_const_apply (hj y)]
  rw [fderiv_scaledJet_apply]
  simp [inner_smul_right]

/-- Source normalization Jq = Uq/(ell*r*q!) gives the exact next-coefficient factor. -/
theorem fderiv_normalized_scaledJet_coordinate (q : ℕ) {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {L : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hhi : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖^2)
    (hL : L ≠ 0) (x : E) {r : ℝ} (hr : r ≠ 0) {t : ℝ}
    (htlo : -1 < t) (hthi : t < 1) (y v w : E) (a : Fin q → E) :
    fderiv ℝ (fun z => (L*r*(q.factorial : ℝ))⁻¹ *
      inner ℝ w (scaledJet q F x r t z a)) y v =
    t*(q+1) * ((L*r*((q+1).factorial : ℝ))⁻¹ *
      inner ℝ w (scaledJet (q+1) F x r t y (Fin.cons v a))) := by
  have hj := (contDiff_scaledJet_spatial q hF hlo hhi x r htlo hthi).differentiable (by simp)
  have ha := (hj y).continuousMultilinear_apply_const a
  have hw := (differentiableAt_const w).inner ℝ ha
  rw [fderiv_const_mul hw, smul_apply,
    fderiv_scaledJet_coordinate q hF hlo hhi x r htlo hthi]
  simp only [smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hq : (q.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
  have hq1 : (q : ℝ)+1 ≠ 0 := by positivity
  field_simp [hL, hr, hq, hq1]

end AcceleratedLogConcave.Conditional
