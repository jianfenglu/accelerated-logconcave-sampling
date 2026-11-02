import AcceleratedLogConcave.Root.PhysicalPosteriorScaling
import AcceleratedLogConcave.Oracle.RecursiveSizeBound
import AcceleratedLogConcave.Oracle.RecursiveCallOccurrence

/-! Initial scalar certificate for the actual final-mean clock slots. The
original gradient is normalized at exactly sqrt(h), and the radius, final
width and precision-K labels are unchanged. This does not discharge the
outer-main width or the public schedule, count, rank and resolution guards. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.FinalMeanInitialCertificate
open ClockBackwardKernel RecursiveRadiusFamily
open Oracle.RecursiveSize
open scoped NNReal

/-- The actual compact source band pays its stronger radius-square estimate. -/
theorem radiusBand_sq_le {h : ℝ} (hh : 0 < h) (r : RadiusBand h) :
    (r : ℝ)^2 ≤ 2*h := by
  have hr := radius_pos hh r
  nlinarith [r.2.2, Real.sqrt_nonneg (2*h), Real.sq_sqrt (show 0 ≤ 2*h by positivity)]

/-- The literal final width dominates every actual source-band radius. -/
theorem radiusBand_le_sourceWidth {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    (r : RadiusBand h) : (r : ℝ) ≤ sourceWidth h := by
  rw [sourceWidth_eq]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (show 0 < 2*h by positivity))).2
  have hs : (1 : ℝ) ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have hm := mul_le_mul_of_nonneg_right r.2.2 (Real.sqrt_nonneg (2*h))
  nlinarith [Real.sq_sqrt (show 0 ≤ 2*h by positivity)]

/-- Initial SizeBound with lambda=delta=h, exponent and multiplier both one.
This uses the prescribed final width, not an outer-main width. -/
theorem radiusBand_sizeBound {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    (r : RadiusBand h) : SizeBound h h 1 1 r (sourceWidth h) := by
  have hsq : (r : ℝ)^2 ≤ 1 := (radiusBand_sq_le hh r).trans (by linarith)
  have hratio : (r : ℝ)/sourceWidth h ≤ 1 :=
    (div_le_one₀ (sourceWidth_pos hh)).2 (radiusBand_le_sourceWidth hh hhalf r)
  constructor
  · simpa only [Real.rpow_one, one_mul, mul_one] using mul_le_mul_of_nonneg_left hsq hh.le
  · simpa only [Real.rpow_one, one_mul, mul_one] using mul_le_mul_of_nonneg_left hratio hh.le

/-- Exact scalar call label for each actual final slot and clock: no new mesh,
order, radius, width or precision is selected. -/
def finalMeanState (h : ℝ) (hh : 0 < h) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K))
    (clock : ClockLaw.Clock) : Oracle.RecursiveCall.State :=
  ⟨radiusParameter h hh K i clock, sourceWidth h, (K : ℝ)⟩

theorem finalMeanState_parameters (h : ℝ) (hh : 0 < h) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) (clock : ClockLaw.Clock) :
    (finalMeanState h hh K i clock).radius = sourceRadius h hh K i clock ∧
    (finalMeanState h hh K i clock).width = sourceWidth h ∧
    (finalMeanState h hh K i clock).precision = (K : ℝ) := ⟨rfl, rfl, rfl⟩

theorem finalSlot_sizeBound {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) (clock : ClockLaw.Clock) :
    SizeBound h h 1 1 (finalMeanState h hh K i clock).radius
      (finalMeanState h hh K i clock).width :=
  radiusBand_sizeBound hh hhalf (radiusParameter h hh K i clock)

section Oracle
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The physical-potential Hessian bound h yields the original-gradient oracle
normalized by sqrt(h). The final Lipschitz premise is derived, not supplied. -/
theorem normalized_gradient_lipschitz {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    {h : ℝ} (hh : 0 ≤ h) :
    LipschitzWith ⟨h, hh⟩ (fun z => Real.sqrt h • gradient V (Real.sqrt h • z)) := by
  have hl := Gibbs.gradient_lipschitz_of_hessian_bounds (physicalPotential_C2 hV h) hh
    (physicalPotential_hessian_nonneg hV hlo hh) (physicalPotential_hessian_upper hV hup hh)
  have he : gradient (physicalPotential V h) =
      fun z => Real.sqrt h • gradient V (Real.sqrt h • z) :=
    funext (PhysicalPosteriorScaling.physicalPotential_gradient hV h)
  rw [he] at hl
  exact hl

/-- The two initial certified-root inputs and positive final scalar parameters
are paid for every actual final clock slot. Other schedule guards remain open. -/
theorem finalSlot_initialCertificate {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) (clock : ClockLaw.Clock) :
    LipschitzWith ⟨h, hh.le⟩ (fun z => Real.sqrt h • gradient V (Real.sqrt h • z)) ∧
    SizeBound (↑(⟨h, hh.le⟩ : ℝ≥0)) h 1 1 (finalMeanState h hh K i clock).radius
      (finalMeanState h hh K i clock).width ∧
    0 < (finalMeanState h hh K i clock).radius ∧
    0 < (finalMeanState h hh K i clock).width :=
  ⟨normalized_gradient_lipschitz hV hlo hup hh.le,
    finalSlot_sizeBound hh hhalf K i clock,
    radius_pos hh (radiusParameter h hh K i clock), sourceWidth_pos hh⟩
end Oracle
end AcceleratedLogConcave.Root.FinalMeanInitialCertificate
