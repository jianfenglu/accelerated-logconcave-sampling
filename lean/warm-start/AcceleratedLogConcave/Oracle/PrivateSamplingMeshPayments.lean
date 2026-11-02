import AcceleratedLogConcave.Oracle.PrivateSamplingOriginalBounds
import AcceleratedLogConcave.Oracle.PrescribedSourceGeometry
import AcceleratedLogConcave.Oracle.CubicSchedulePayments

/-! Actual prescribed adaptive private-mesh payments. The cell-local variance
denominators cancel against the proved geometric cell lengths. The original
material order/dimension factor remains explicit; no regularity or desired
accuracy budget is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.PrivateSamplingMeshPayments
open Numerics Numerics.AffineGraph Numerics.SamplingGaussianJetLp
open PrivateSamplingOriginalBounds ConditionalSmoothing

def orderFactor (D m : ℕ) : ℝ :=
  2^(m+1)*materialOrderFactor D (m-1)/(m.factorial:ℝ)

theorem orderFactor_nonneg (D m : ℕ) : 0 ≤ orderFactor D m := by
  unfold orderFactor
  positivity [materialOrderFactor_nonneg D (m-1)]

variable {D : ℕ} (d : SamplingCenterLp.Data (Fin D))

theorem cellBudget_le_geometric (hpos : 0 < d.b) (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (m : ℕ) :
    let M := probabilityGeometricInterval 0 d.b h₀ hpos d.hb1 hh
    AffineResidual.cellBudget M m (cellDerivativeBudget d M m) ≤
      d.b*(d.ell*d.r)*orderFactor D m*h₀^m := by
  dsimp only
  let M := probabilityGeometricInterval 0 d.b h₀ hpos d.hb1 hh
  have H := AffineResidual.probability_cellBudget_le M (by norm_num) d.hb1 m
    (cellDerivativeBudget d M m) ((d.ell*d.r)*materialOrderFactor D (m-1)) h₀
    (mul_nonneg (mul_nonneg d.hell d.hr.le) (materialOrderFactor_nonneg _ _)) hh.le
    (probabilityGeometricInterval_step 0 d.b h₀ hpos d.hb1 hh hhalf (by norm_num))
    (fun _ => le_rfl)
  refine H.trans_eq ?_
  unfold orderFactor
  ring

theorem cellBudget_le_of_mesh (hpos : 0 < d.b) (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (M : IntervalMesh 0 d.b) (m : ℕ)
    (hmesh : M = probabilityGeometricInterval 0 d.b h₀ hpos d.hb1 hh) :
    AffineResidual.cellBudget M m (cellDerivativeBudget d M m) ≤
      d.b*(d.ell*d.r)*orderFactor D m*h₀^m := by
  subst M
  exact cellBudget_le_geometric d hpos h₀ hh hhalf m

section Prescribed
variable (m : ℕ) (R h₀ : ℝ) (hR : 0 < R) (hRh : R ≤ 1/2) (hh : 0 < h₀)
  {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (r : ℝ) (hr : 0 < r)
local notation "S" => PrescribedSourceGeometry.samplingGeometry m R h₀ hR hRh hh
local notation "data" => PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr

/-- The actual source mesh, not an arbitrary mesh with a supplied step bound. -/
theorem prescribed_cellBudget (hhalf : h₀ ≤ 1/2) :
    AffineResidual.cellBudget (S).mesh m (cellDerivativeBudget data (S).mesh m) ≤
      (samplingEnd (S).τ)*(ell*r)*orderFactor D m*h₀^m :=
  cellBudget_le_of_mesh data (S).samplingEnd_pos h₀ hh hhalf (S).mesh m
    (PrescribedSourceGeometry.sampling_mesh m R h₀ hR hRh hh)

theorem prescribed_rowBudget (hhalf : h₀ ≤ 1/2) :
    r^2*(samplingEnd (S).τ)*AffineResidual.cellBudget (S).mesh m (cellDerivativeBudget data (S).mesh m) ≤
      ell*r^3*(samplingEnd (S).τ)^2*orderFactor D m*h₀^m := by
  have H := mul_le_mul_of_nonneg_left
    (prescribed_cellBudget m R h₀ hR hRh hh hF hell hlo hup r hr hhalf)
    (mul_nonneg (sq_nonneg r) (S).samplingEnd_pos.le)
  exact H.trans_eq (by ring)

/-- The endpoint output scaling cancels the full probability endpoint. -/
theorem prescribed_finalBudget (hhalf : h₀ ≤ 1/2) :
    (r/samplingEnd (S).τ)*AffineResidual.cellBudget (S).mesh m (cellDerivativeBudget data (S).mesh m) ≤
      (ell*r^2)*orderFactor D m*h₀^m := by
  have H := mul_le_mul_of_nonneg_left
    (prescribed_cellBudget m R h₀ hR hRh hh hF hell hlo hup r hr hhalf)
    (div_nonneg hr.le (S).samplingEnd_pos.le)
  refine H.trans_eq ?_
  have hcancel : r / samplingEnd (S).τ * samplingEnd (S).τ = r :=
    div_mul_cancel₀ _ (S).samplingEnd_pos.ne'
  calc
    _ = (r / samplingEnd (S).τ * samplingEnd (S).τ) *
        ((ell*r)*orderFactor D m*h₀^m) := by ring
    _ = _ := by rw [hcancel]; ring
end Prescribed

/-- The actual ceiling order pays A in the literal h0=delta^w power. -/
theorem source_power (Q : SourceSchedule) (hc : 0 < Q.csch) (hC : 1 ≤ Q.Csch) (hy : 0 ≤ Q.y) :
    Q.h0^Q.m ≤ Q.delta^Q.A := by
  have hw := Q.w_pos hc
  have hm := (Q.m_bounds hc hC).1
  have hwm : Q.A ≤ Q.w*(Q.m:ℝ) := by
    have H := (div_le_iff₀ hw).mp hm
    nlinarith
  unfold SourceSchedule.h0
  rw [← Real.rpow_natCast,← Real.rpow_mul Q.delta_pos.le]
  exact Real.rpow_le_rpow_of_exponent_ge Q.delta_pos (Q.delta_le_one hy) hwm

section Source
variable (Q : SourceSchedule) (hK : 10 ≤ Q.K) (hc : 0 < Q.csch) (hsmall : Q.csch < 1/160)
  (hC : 8 ≤ Q.Csch) (hy : CubicScheduleThreshold.threshold Q ≤ Q.y)
local notation "hR" => CubicSchedulePayments.radius_guard Q hK hc hsmall hC hy
local notation "S" => PrescribedSourceGeometry.samplingGeometry Q.m Q.R Q.h0 Q.R_pos hR Q.h0_pos
variable {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (r : ℝ) (hr : 0 < r)
local notation "data" => PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr

/-- Actual ceiling order and cubic source guards pay the prescribed mesh
power. The material factor is displayed, with no dimension/order suppression. -/
theorem source_finalBudget :
    (r/samplingEnd (S).τ)*AffineResidual.cellBudget (S).mesh Q.m (cellDerivativeBudget data (S).mesh Q.m) ≤
      (ell*r^2)*orderFactor D Q.m*Q.delta^Q.A := by
  have hp := CubicSchedulePayments.prerequisites Q hK hc hsmall hC hy
  have hhalf := (ScalarSchedulePayment.geometry_caps Q hc hsmall (by linarith) hp.1 hp.2.2).2.2.2
  have H := prescribed_finalBudget Q.m Q.R Q.h0 Q.R_pos hR Q.h0_pos hF hell hlo hup r hr hhalf
  exact H.trans (mul_le_mul_of_nonneg_left (source_power Q hc (by linarith) hp.1)
    (mul_nonneg (mul_nonneg hell (sq_nonneg r)) (orderFactor_nonneg D Q.m)))

theorem source_rowBudget :
    r^2*(samplingEnd (S).τ)*AffineResidual.cellBudget (S).mesh Q.m (cellDerivativeBudget data (S).mesh Q.m) ≤
      ell*r^3*(samplingEnd (S).τ)^2*orderFactor D Q.m*Q.delta^Q.A := by
  have hp := CubicSchedulePayments.prerequisites Q hK hc hsmall hC hy
  have hhalf := (ScalarSchedulePayment.geometry_caps Q hc hsmall (by linarith) hp.1 hp.2.2).2.2.2
  have H := prescribed_rowBudget Q.m Q.R Q.h0 Q.R_pos hR Q.h0_pos hF hell hlo hup r hr hhalf
  exact H.trans (mul_le_mul_of_nonneg_left (source_power Q hc (by linarith) hp.1)
    (by positivity [hell,hr.le,orderFactor_nonneg D Q.m]))

/-- The original-data physical curvature size multiplies the actual mesh
payment. No desired quadrature error is taken as a hypothesis. -/
theorem source_sized_finalBudget (B beta : ℝ) (hsize : ell*r^2 ≤ B*Q.delta^beta) :
    (r/samplingEnd (S).τ)*AffineResidual.cellBudget (S).mesh Q.m (cellDerivativeBudget data (S).mesh Q.m) ≤
      B*orderFactor D Q.m*Q.delta^(Q.A+beta) := by
  calc
    _ ≤ (ell*r^2)*orderFactor D Q.m*Q.delta^Q.A :=
      source_finalBudget Q hK hc hsmall hC hy hF hell hlo hup r hr
    _ ≤ (B*Q.delta^beta)*orderFactor D Q.m*Q.delta^Q.A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsize (orderFactor_nonneg D Q.m))
        (Real.rpow_nonneg Q.delta_pos.le _)
    _ = _ := by rw [Real.rpow_add Q.delta_pos]; ring

/-- Explicit source exponent absorption through K+4. The material order and
dimension factor remains fully visible instead of being declared universal. -/
theorem source_sized_finalBudget_precision (B beta : ℝ) (hB : 0 ≤ B) (hbeta : 0 ≤ beta)
    (hsize : ell*r^2 ≤ B*Q.delta^beta) :
    (r/samplingEnd (S).τ)*AffineResidual.cellBudget (S).mesh Q.m (cellDerivativeBudget data (S).mesh Q.m) ≤
      B*orderFactor D Q.m*Q.delta^((Q.K:ℝ)+4) := by
  have hp := CubicSchedulePayments.prerequisites Q hK hc hsmall hC hy
  have hA := mul_le_mul_of_nonneg_right hC (by positivity : (0:ℝ) ≤ (Q.K:ℝ)+2)
  change 8*((Q.K:ℝ)+2) ≤ Q.A at hA
  have hexp : (Q.K:ℝ)+4 ≤ Q.A+beta := by nlinarith [Nat.cast_nonneg (α := ℝ) Q.K]
  exact (source_sized_finalBudget Q hK hc hsmall hC hy hF hell hlo hup r hr B beta hsize).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge Q.delta_pos (Q.delta_le_one hp.1) hexp)
      (mul_nonneg hB (orderFactor_nonneg D Q.m)))
/-- On the original physical curvature domain, the actual endpoint defect
budget has no endpoint denominator and pays the source precision power. -/
theorem source_physical_finalBudget (hphysical : r^2*ell ≤ 1/2) :
    (r/samplingEnd (S).τ)*AffineResidual.cellBudget (S).mesh Q.m (cellDerivativeBudget data (S).mesh Q.m) ≤
      (1/2:ℝ)*orderFactor D Q.m*Q.delta^((Q.K:ℝ)+4) := by
  apply source_sized_finalBudget_precision Q hK hc hsmall hC hy hF hell hlo hup r hr
    (1/2) 0 (by norm_num) (by norm_num)
  simpa [mul_comm] using hphysical
end Source

end AcceleratedLogConcave.Oracle.PrivateSamplingMeshPayments
