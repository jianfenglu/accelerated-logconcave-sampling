import AcceleratedLogConcave.Kinetic.SourceFlowCoordinateIdentity
import AcceleratedLogConcave.Kinetic.ExecutedPhaseReadout

/-! Exact physical position and refreshed momentum for the accepted source
phase flow at a fixed clock. This is a deterministic reference-side readout;
no finite executable/reference law equality is used. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Kinetic.Reheating
open MeasureTheory Set ConditionalContraction
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The literal split, coupled flow, dormant replacement, final rotation,
reheat and OU output has the manuscript's physical position and refreshed
momentum. Here `P' = s Y_R + n H₁` is the actually rotated momentum. -/
theorem sourceFixedClockOutput_eq {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell : ℝ) (hell : 0 ≤ ell) (hEll : ell^2 = A)
    (t : Icc (0:ℝ) (1/2)) (s n : ℝ) (hsn : s^2+n^2=1)
    (Γ : ℝ) (z : GaussianPhase E) (H1 Gx Gp : E) :
    let pre := preCollisionMap (clockTransportFamily H hA hR) ell t s n hsn z
    let P' := s • pre.1.2 + n • H1
    fixedClockOutput s n hsn (A*(t:ℝ)^2) Γ (((pre,H1),Gx),Gp) =
      (z.1.1 + (ell*(t:ℝ)*s) • (P'+Gx), gaussianMix E Γ (P',Gp)) := by
  let pre := preCollisionMap (clockTransportFamily H hA hR) ell t s n hsn z
  let P' := s • pre.1.2 + n • H1
  have hsqrt : Real.sqrt (A*(t:ℝ)^2) = ell*(t:ℝ) := by
    rw [← hEll]
    exact source_reheat_scale ell hell t
  have hpre := clockTransportFamily_preCollisionMap_position_eq
    H hA hR ell hEll t s n hsn z
  have hpos : (dormantNewState ((pre,H1) : GaussianPhase E × E)).1.1 =
      z.1.1 + Real.sqrt (A*(t:ℝ)^2) •
        (dormantNewState ((pre,H1) : GaussianPhase E × E)).1.2 := by
    change pre.1.1 = z.1.1 + Real.sqrt (A*(t:ℝ)^2) • pre.1.2
    rw [hsqrt]
    exact hpre
  have hread := fixedClockOutput_position_from_initial s n hsn
    (A*(t:ℝ)^2) Γ (((pre,H1),Gx),Gp) z.1.1 hpos
  apply Prod.ext
  · change (fixedClockOutput s n hsn (A*(t:ℝ)^2) Γ (((pre,H1),Gx),Gp)).1 =
      z.1.1 + (ell*(t:ℝ)*s) • (P'+Gx)
    dsimp only at hread
    rw [hread, hsqrt]
    change z.1.1 + (ell*(t:ℝ)) • (s • P' + s • Gx) = _
    module
  · rfl

/-- The same complete readout with the source's fixed split/rotation
coefficients `s=1/2` and `n=√3/2`. -/
theorem sourceFixedClockOutput_eq_actual {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell : ℝ) (hell : 0 ≤ ell) (hEll : ell^2 = A)
    (t : Icc (0:ℝ) (1/2)) (Γ : ℝ)
    (z : GaussianPhase E) (H1 Gx Gp : E) :
    let pre := preCollisionMap (clockTransportFamily H hA hR) ell t
      (1/2) (Real.sqrt 3/2) source_split_coefficients z
    let P' := (1/2:ℝ) • pre.1.2 + (Real.sqrt 3/2) • H1
    fixedClockOutput (1/2) (Real.sqrt 3/2) source_split_coefficients
      (A*(t:ℝ)^2) Γ (((pre,H1),Gx),Gp) =
      (z.1.1 + (ell*(t:ℝ)*(1/2:ℝ)) • (P'+Gx),
        gaussianMix E Γ (P',Gp)) :=
  sourceFixedClockOutput_eq H hA hR ell hell hEll t
    (1/2) (Real.sqrt 3/2) source_split_coefficients Γ z H1 Gx Gp

end AcceleratedLogConcave.Kinetic.Reheating
