import AcceleratedLogConcave.Numerics.SamplingCenterLp
import AcceleratedLogConcave.Gibbs.PrimitiveMoments

/-! SOURCE-ONLY. Literal normalized-root potential and conditional flow data.
No derivative budget, quadrature accuracy, or flow equality is assumed. -/
noncomputable section
set_option autoImplicit false
open Set
namespace AcceleratedLogConcave.Root.OuterRootOriginalData
variable {ι : Type*} [Fintype ι]
variable {V : (EuclideanSpace ℝ ι) → ℝ} (hV : ContDiff ℝ 2 V) {h : ℝ} (hh : 0 < h)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)

def potential (V : (EuclideanSpace ℝ ι) → ℝ) (h : ℝ) (z : (EuclideanSpace ℝ ι)) : ℝ := V (Real.sqrt h • z)

include hV in
theorem potential_C2 : ContDiff ℝ 2 (potential V h) := by
  change ContDiff ℝ 2 (fun z : EuclideanSpace ℝ ι => V (Real.sqrt h • z))
  exact hV.comp (contDiff_id.const_smul (Real.sqrt h))

include hV hlo in
theorem potential_hessian_nonneg :
    ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ (potential V h)) z v v := by
  change ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ ι => V (Real.sqrt h • z))) z v v
  simpa only [potential, zero_add] using
    Gibbs.primitive_affine_hessian_nonneg hV hlo (0 : (EuclideanSpace ℝ ι)) (Real.sqrt h)

include hV hh hup in
theorem potential_hessian_upper :
    ∀ z v, fderiv ℝ (fderiv ℝ (potential V h)) z v v ≤ h*‖v‖^2 := by
  change ∀ z v, fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ ι => V (Real.sqrt h • z))) z v v ≤ h*‖v‖^2
  simpa only [potential, zero_add, Real.sq_sqrt hh.le, mul_one, one_mul] using
    Gibbs.primitive_affine_hessian_upper hV
      (show ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ (1:ℝ)*‖v‖^2 by simpa using hup)
      (0 : (EuclideanSpace ℝ ι)) (Real.sqrt h)

/-- The exact outer-root mean-coordinate data: F=V(sqrt(h)·), rF=sqrt(2h), b=1/2. -/
def data : Numerics.SamplingCenterLp.Data ι where
  F := potential V h
  hF := potential_C2 hV
  ell := h
  hell := hh.le
  hlo := potential_hessian_nonneg hV hlo
  hup := potential_hessian_upper hV hh hup
  r := Real.sqrt (2*h)
  hr := Real.sqrt_pos.mpr (by positivity)
  b := 1/2
  hb := by norm_num
  hb1 := by norm_num

theorem data_small (hsmall : h ≤ 1/2) :
    (data hV hh hlo hup).r^2 * (data hV hh hlo hup).ell ≤ 1/2 := by
  change (Real.sqrt (2*h))^2*h ≤ 1/2
  rw [Real.sq_sqrt (by positivity)]
  nlinarith

end AcceleratedLogConcave.Root.OuterRootOriginalData
