import AcceleratedLogConcave.Oracle.MeanPrescribedOriginalPayments

/-! Scalar guards of the actual recursive mean error recurrence. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
namespace AcceleratedLogConcave.Oracle.MeanPrescribedRecursiveGuards
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall RecursiveSize

/-- The literal row inventory pays the physical width ratio. -/
theorem ratio_of_row {m : ℕ} (hm : 2≤m) {δ t w r σ ell : ℝ}
    (hδ : 0<δ) (hd : δ≤1) (ht : 0≤t) (hw : 0≤w)
    (hr : 0≤r) (hσ : 0<σ) (hell : 0≤ell)
    (hrow : 2*ell*SourceMeanExecutable.rowBound (m := m) r σ δ t w≤δ^((1:ℝ)/3)) :
    ell*r≤σ*δ^((1:ℝ)/4)/4096 := by
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hm5 : (32:ℝ)≤(m:ℝ)^5 := by
    calc
      _ = (2:ℝ)^5 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hmR _
  have hp : 1≤δ^(-4*t-w) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hd (by linarith)
  have hbase : 8192*(r/σ)≤SourceMeanExecutable.rowBound (m := m) r σ δ t w := by
    have h0 : 0≤r/σ := div_nonneg hr hσ.le
    have h1 := mul_le_mul_of_nonneg_right hm5 h0
    have h2 := mul_le_mul_of_nonneg_left hp (show 0≤256*(m:ℝ)^5*(r/σ) by positivity)
    unfold SourceMeanExecutable.rowBound
    change 8192*(r/σ)≤256*(m:ℝ)^5*(r/σ)*δ^(-4*t-w)+4*r^2
    nlinarith [sq_nonneg r]
  have hbound := (mul_le_mul_of_nonneg_left hbase (show 0≤2*ell by positivity)).trans hrow
  have hpow : δ^((1:ℝ)/3)≤δ^((1:ℝ)/4) := Real.rpow_le_rpow_of_exponent_ge hδ hd (by norm_num)
  have hratio : ell*r/σ≤δ^((1:ℝ)/4)/4096 := by
    have hbound' : 16384*(ell*r/σ)≤δ^((1:ℝ)/3) := by
      convert hbound using 1
      ring
    clear hbound
    nlinarith [div_nonneg (mul_nonneg hell hr) hσ.le,Real.rpow_nonneg hδ.le ((1:ℝ)/4)]
  exact (div_le_iff₀ hσ).mp hratio |>.trans_eq (by ring)

/-- The actual prescribed layer count pays a contraction of delta^(1/3),
including the zero-contraction endpoint. -/
theorem transient (P : SourceSchedule) (hC : 8≤P.Csch) (hd : P.delta≤1)
    {χ : ℝ} (hχ : 0≤χ) (hbound : χ≤P.delta^((1:ℝ)/3)) :
    χ^P.NP≤P.delta^((P.K:ℝ)+2) := by
  have hn : 3*(P.K+2)≤P.NP := by
    have hb := (P.NP_bounds (by linarith : 1≤P.Csch)).1
    have ha := mul_le_mul_of_nonneg_right hC (show 0≤(P.K:ℝ)+2 by positivity)
    change 8*((P.K:ℝ)+2)≤P.A at ha
    exact_mod_cast (show 3*((P.K:ℝ)+2)≤(P.NP:ℝ) by linarith [Nat.cast_nonneg (α := ℝ) P.K])
  calc
    _ ≤ (P.delta^((1:ℝ)/3))^P.NP := pow_le_pow_left₀ hχ hbound _
    _ = P.delta^(((1:ℝ)/3)*(P.NP:ℝ)) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul P.delta_pos.le]
    _ ≤ P.delta^((P.K:ℝ)+2) := by
      apply Real.rpow_le_rpow_of_exponent_ge P.delta_pos hd
      have hnR : 3*((P.K:ℝ)+2)≤(P.NP:ℝ) := by exact_mod_cast hn
      linarith

section Reachable
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
variable {ell r0 σ0 : ℝ} (hell : 0≤ell) (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hroot : ell*r0^2≤P.delta) (hrootRatio : ell*(r0/σ0)≤P.delta)
  {p : State} {depth cost : ℕ}

include hell hr0 hσ0 hroot hrootRatio in
/-- Actual occurrence paths supply the small physical ratio used in the
one-unit main-error payment. -/
theorem reachable_ratio
    (hp : Path (source P hR) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    ell*p.radius≤p.width*P.delta^((1:ℝ)/4)/4096 := by
  have hm := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  have hpos := hp.positive (by omega) P.Ds_pos P.delta_pos hr0 hσ0
  have hd := P.delta_le_one (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  exact ratio_of_row hm P.delta_pos hd (P.t_pos hc).le (P.w_pos hc).le
    hpos.1.le hpos.2 hell
    (PrescribedMeanNumericalData.reachable_row_payment P hell hK hc hsmall hC hy hr0 hσ0 hroot hrootRatio hp)

variable {D : ℕ} {F : Point D → ℝ} (hF : ContDiff ℝ 2 F)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2) (x : Point D)

include hrootRatio in
/-- The actual graph's contraction, literal layer count and transient need
no extra hypothesis on an executed recursive call. -/
theorem reachable_transient
    (hp : Path (source P hR) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    let d := PrescribedMeanNumericalData.reachableDatum P hF hell hlo hup x hK hc hsmall hC hy hr0 hσ0 hroot hp
    let χ := 2*MeanCollocationLp.contraction d P.h0
    0≤χ ∧ χ≤1/2 ∧ χ^P.NP≤P.delta^((P.K:ℝ)+2) := by
  dsimp only
  have hrow := PrescribedMeanNumericalData.reachable_row_payment P hell hK hc hsmall hC hy hr0 hσ0 hroot hrootRatio hp
  have hd := P.delta_le_one (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  have hnonneg : 0≤2*MeanCollocationLp.contraction
      (PrescribedMeanNumericalData.reachableDatum P hF hell hlo hup x hK hc hsmall hC hy hr0 hσ0 hroot hp) P.h0 := by
    unfold MeanCollocationLp.contraction
    exact mul_nonneg (by norm_num) (mul_nonneg hell (MeanCollocationLp.rowMass_nonneg _ _ (PrescribedMeanNumericalData.reachable_mesh P hF hell hlo hup x hK hc hsmall hC hy hr0 hσ0 hroot hp)))
  have hbound : 2*MeanCollocationLp.contraction
      (PrescribedMeanNumericalData.reachableDatum P hF hell hlo hup x hK hc hsmall hC hy hr0 hσ0 hroot hp) P.h0≤P.delta^((1:ℝ)/3) := by
    unfold MeanCollocationLp.contraction
    unfold PrescribedMeanNumericalData.reachableDatum
    rw [PrescribedMeanNumericalData.rowMass_eq]
    have hnn := Real.rpow_nonneg P.delta_pos.le ((1:ℝ)/3)
    change 2*(ell*SourceMeanExecutable.rowBound (m := P.m) p.radius p.width P.delta P.t P.w)≤_
    linarith
  have hd100 := PrivateSourceScalarAbsorption.delta_le_hundredth P hK hc (by linarith) (by linarith) hy
  have he : (P.delta^((1:ℝ)/3))^3=P.delta := by
    rw [←Real.rpow_natCast,←Real.rpow_mul P.delta_pos.le]
    norm_num
  have hp := Real.rpow_nonneg P.delta_pos.le ((1:ℝ)/3)
  have hhalf : P.delta^((1:ℝ)/3)≤1/2 := by
    nlinarith [sq_nonneg (P.delta^((1:ℝ)/3)-1/2)]
  exact ⟨hnonneg,hbound.trans hhalf,transient P hC hd hnonneg hbound⟩

end Reachable

end AcceleratedLogConcave.Oracle.MeanPrescribedRecursiveGuards
