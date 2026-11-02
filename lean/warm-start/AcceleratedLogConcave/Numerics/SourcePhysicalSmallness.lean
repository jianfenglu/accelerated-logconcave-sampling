import AcceleratedLogConcave.Numerics.SourceScheduledData

/-! The source resolution inequality also pays the physical smallness needed
to construct the analytic data. It need not be a separately assumed numerical
fact about the receiver. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourcePhysicalSmallness
open AffineGraph

theorem tier_size_le_half {m : ℕ} (hm : 1 ≤ m) {δ b S : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : (1:ℝ)/2 ≤ b) (hS : 1 ≤ S)
    (hres : δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ)) : S*δ^b ≤ 1/2 := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm5 : (1:ℝ) ≤ (m:ℝ)^5 := one_le_pow₀ hm1
  have hS0 : 0 < S := by linarith
  have h := affine_resolution_envelope_le (t := 0) (w := 0)
    hδ hδone (by positivity : 0 < 520*(m:ℝ)^5*S) hb (by norm_num) (by norm_num) hres
  simp only [mul_zero, sub_zero] at h
  have hp : δ^((1:ℝ)/3) ≤ 1 := Real.rpow_le_one hδ.le hδone (by norm_num)
  have ha : 0 ≤ S*δ^b := mul_nonneg hS0.le (Real.rpow_nonneg hδ.le _)
  have hprod := mul_nonneg (sub_nonneg.mpr hm5) ha
  nlinarith

theorem radius_small {m : ℕ} (hm : 1 ≤ m) {δ b S ell r : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : (1:ℝ)/2 ≤ b) (hS : 1 ≤ S)
    (hsize : ell*r^2 ≤ S*δ^b)
    (hres : δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ)) : r^2*ell ≤ 1/2 := by
  have h := tier_size_le_half hm hδ hδone hb hS hres
  nlinarith

theorem ratio_small {m : ℕ} (hm : 1 ≤ m) {δ b S ell r sigma : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : (1:ℝ)/2 ≤ b) (hS : 1 ≤ S)
    (hsize : ell*r/sigma ≤ S*δ^b)
    (hres : δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ)) : ell*r/sigma ≤ 1 :=
  (hsize.trans (tier_size_le_half hm hδ hδone hb hS hres)).trans (by norm_num)

/-- The original analytic input is constructible from the prescribed physical
size and resolution; its smallness field is proved rather than supplied. -/
def originalData {D m : ℕ} (F : EuclideanSpace ℝ (Fin D) → ℝ)
    (hF : ContDiff ℝ 2 F) (ell : ℝ) (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell*‖a‖^2)
    (x : EuclideanSpace ℝ (Fin D)) (r sigma : ℝ) (hr : 0 < r) (hsigma : 0 < sigma)
    (hm : 1 ≤ m) {δ b S : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hb : (1:ℝ)/2 ≤ b) (hS : 1 ≤ S) (hsize : ell*r^2 ≤ S*δ^b)
    (hres : δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ)) : SourceScheduledData.OriginalData D where
  F := F
  hF := hF
  ell := ell
  hell := hell
  hlo := hlo
  hup := hup
  x := x
  r := r
  hr := hr
  hsmall := radius_small hm hδ hδone hb hS hsize hres
  sigma := sigma
  hsigma := hsigma

end AcceleratedLogConcave.Numerics.SourcePhysicalSmallness
