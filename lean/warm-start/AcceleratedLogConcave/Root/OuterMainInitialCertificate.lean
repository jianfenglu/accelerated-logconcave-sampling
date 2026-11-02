import AcceleratedLogConcave.Root.FinalMeanInitialCertificate

/-! Distinct outer main-center width. Nr is a separate positive outer inventory;
no equality with the final-slot count or internal layer count is imposed. The
one explicit scalar payment below is not discharged by the cubic schedule here. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.OuterMainInitialCertificate
open ClockBackwardKernel RecursiveRadiusFamily Oracle.RecursiveSize

/-- Literal manuscript sigma_c, using Ds=h^(-t) and rF=sqrt(2h). -/
def mainWidth (h t : ℝ) (Nr : ℕ) : ℝ :=
  1/(2*h^(-t)*Real.sqrt (Nr:ℝ)*Real.sqrt (2*h))

theorem mainWidth_pos {h : ℝ} (hh : 0 < h) (t : ℝ) {Nr : ℕ} (hNr : 0 < Nr) :
    0 < mainWidth h t Nr := by
  unfold mainWidth
  have hpow := Real.rpow_pos_of_pos hh (-t)
  have hroot := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNr : (0:ℝ) < Nr)
  have hhroot := Real.sqrt_pos.mpr (mul_pos (by norm_num : (0:ℝ)<2) hh)
  positivity

/-- Ratio estimate at every actual source-band radius, before the scalar payment. -/
theorem radiusBand_ratio_le {h : ℝ} (hh : 0 < h) (t : ℝ) (Nr : ℕ) (r : RadiusBand h) :
    (r:ℝ)/mainWidth h t Nr ≤ 4*Real.sqrt (Nr:ℝ)*h^(1-t) := by
  have hh0 : 0 ≤ 2*h := mul_nonneg (by norm_num) hh.le
  have hpow := (Real.rpow_pos_of_pos hh (-t)).le
  calc
    (r:ℝ)/mainWidth h t Nr = (r:ℝ)*(2*h^(-t)*Real.sqrt (Nr:ℝ)*Real.sqrt (2*h)) := by
      simp [mainWidth, div_eq_mul_inv]
    _ ≤ Real.sqrt (2*h)*(2*h^(-t)*Real.sqrt (Nr:ℝ)*Real.sqrt (2*h)) :=
      mul_le_mul_of_nonneg_right r.2.2 (by positivity)
    _ = 2*h^(-t)*Real.sqrt (Nr:ℝ)*(Real.sqrt (2*h))^2 := by ring
    _ = 4*Real.sqrt (Nr:ℝ)*(h*h^(-t)) := by rw [Real.sq_sqrt hh0]; ring
    _ = 4*Real.sqrt (Nr:ℝ)*h^(1-t) := by
      rw [sub_eq_add_neg, Real.rpow_add hh, Real.rpow_one]

/-- Initial main width certificate from an explicit inventory/resolution payment.
The algebra works for any real t; in the source schedule 0<t<1 is derived. -/
theorem radiusBand_sizeBound {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    (t : ℝ) (Nr : ℕ) (r : RadiusBand h)
    (hpay : 4*Real.sqrt (Nr:ℝ)*h^(1-t) ≤ 1) :
    SizeBound h h 1 1 r (mainWidth h t Nr) := by
  have hsq : (r:ℝ)^2 ≤ 1 := (FinalMeanInitialCertificate.radiusBand_sq_le hh r).trans (by linarith)
  have hratio := (radiusBand_ratio_le hh t Nr r).trans hpay
  constructor
  · simpa only [Real.rpow_one, one_mul, mul_one] using mul_le_mul_of_nonneg_left hsq hh.le
  · simpa only [Real.rpow_one, one_mul, mul_one] using mul_le_mul_of_nonneg_left hratio hh.le

/-- The actual outer clock radius and precision K, with the distinct main width. -/
def mainMeanState (h : ℝ) (hh : 0 < h) (t : ℝ) (Nr K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h*ClockSchedule.sourceOrder K))
    (clock : ClockLaw.Clock) : Oracle.RecursiveCall.State :=
  ⟨radiusParameter h hh K i clock, mainWidth h t Nr, (K:ℝ)⟩

theorem mainMeanState_parameters (h : ℝ) (hh : 0 < h) (t : ℝ) (Nr K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h*ClockSchedule.sourceOrder K)) (clock : ClockLaw.Clock) :
    (mainMeanState h hh t Nr K i clock).radius = sourceRadius h hh K i clock ∧
    (mainMeanState h hh t Nr K i clock).width = 1/(2*h^(-t)*Real.sqrt (Nr:ℝ)*Real.sqrt (2*h)) ∧
    (mainMeanState h hh t Nr K i clock).precision = (K:ℝ) := ⟨rfl,rfl,rfl⟩

theorem mainSlot_initialCertificate {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    (t : ℝ) {Nr : ℕ} (hNr : 0 < Nr) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h*ClockSchedule.sourceOrder K)) (clock : ClockLaw.Clock)
    (hpay : 4*Real.sqrt (Nr:ℝ)*h^(1-t) ≤ 1) :
    0 < (mainMeanState h hh t Nr K i clock).radius ∧
    0 < (mainMeanState h hh t Nr K i clock).width ∧
    SizeBound h h 1 1 (mainMeanState h hh t Nr K i clock).radius
      (mainMeanState h hh t Nr K i clock).width :=
  ⟨radius_pos hh (radiusParameter h hh K i clock), mainWidth_pos hh t hNr,
    radiusBand_sizeBound hh hhalf t Nr (radiusParameter h hh K i clock) hpay⟩
end AcceleratedLogConcave.Root.OuterMainInitialCertificate
