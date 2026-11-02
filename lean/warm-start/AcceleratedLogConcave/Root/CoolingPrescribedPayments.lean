import AcceleratedLogConcave.Root.CoolingSourceWork
import AcceleratedLogConcave.Oracle.PrivateSourceScalarAbsorption

/-! Prescribed public cooling mesh and original-data quadrature payments.
The public endpoint is tau=1, independently of the lower mean's private mesh. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
namespace AcceleratedLogConcave.Root.CoolingPrescribedPayments
open Oracle Numerics Numerics.AffineGraph SamplingGaussianJetLp
open PrivateSamplingMeshPayments

private theorem endpoint_pos : 0<samplingEnd 1 := by unfold samplingEnd; positivity
private theorem endpoint_lt_one : samplingEnd 1<1 := by
  unfold samplingEnd
  apply inv_lt_one_of_one_lt₀
  apply (Real.lt_sqrt (by norm_num : (0:ℝ)≤1)).2
  norm_num

/-- The source probability-geometric mesh, at the public endpoint. -/
def mesh (P : SourceSchedule) : IntervalMesh 0 (samplingEnd 1) :=
  probabilityGeometricInterval 0 (samplingEnd 1) P.h0 endpoint_pos endpoint_lt_one P.h0_pos

def geometry (P : SourceSchedule) (hR : P.R≤1/2) : SamplingGeometry P.m where
  R := P.R
  R_pos := P.R_pos
  R_le_half := hR
  τ := 1
  R_le_τ := hR.trans (by norm_num)
  τ_le_one := le_rfl
  mesh := mesh P

/-- Canonical enumeration of every public quadrature slot. -/
def nodes (P : SourceSchedule) : Fin (Fintype.card ((mesh P).Source P.m)) ≃ (mesh P).Source P.m :=
  (Fintype.equivFin _).symm

def setup (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160) :=
  CoolingSourceWork.setup P hR hc hsmall (mesh P) (nodes P)

theorem setup_geometry (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160) :
    CoolingExecutable.outerGeometry (setup P hR hc hsmall)=geometry P hR := rfl

theorem public_tau (P : SourceSchedule) (hR : P.R≤1/2) : (geometry P hR).τ=1 := rfl

variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
variable {D : ℕ} {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (r : ℝ) (hr : 0<r)
local notation "S" => geometry P hR
local notation "d" => PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr

/-- The public tau=1 mesh pays its actual derivative envelope from C2 data. -/
theorem cell_payment :
    AffineResidual.cellBudget (S).mesh P.m (cellDerivativeBudget d (S).mesh P.m)≤
      (samplingEnd 1)*(ell*r)*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1) := by
  have hp := CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy
  have hhalf := (ScalarSchedulePayment.geometry_caps P hc hsmall (by linarith) hp.1 hp.2.2).2.2.2
  have hb := cellBudget_le_of_mesh d (S).samplingEnd_pos P.h0 P.h0_pos hhalf (S).mesh P.m rfl
  have hm : 1≤P.m := by have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch); omega
  have hfactor := PrivateSourceScalarAbsorption.orderFactor_le D P.m hm
  have hpow := source_power P hc (by linarith) hp.1
  have hpaid := PrivateSourceScalarAbsorption.order_payment P hK hc hsmall hC hy
  calc
    _ ≤ (samplingEnd 1)*(ell*r)*orderFactor D P.m*P.h0^P.m := hb
    _ ≤ (samplingEnd 1)*(ell*r)*(Real.sqrt (D:ℝ)*PrivateSourceScalarAbsorption.orderConstant P.m)*P.delta^P.A := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfactor (by positivity [endpoint_pos])) hpow
        (pow_nonneg P.h0_pos.le _) (by positivity [endpoint_pos,PrivateSourceScalarAbsorption.orderConstant_pos hm])
    _ = (samplingEnd 1)*(ell*r)*Real.sqrt (D:ℝ)*(PrivateSourceScalarAbsorption.orderConstant P.m*P.delta^P.A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpaid (by positivity [endpoint_pos])

/-- Endpoint scaling cancels the actual public probability endpoint. -/
theorem quadrature_payment :
    PrivateCompletedRms.quadratureBudget S r hr hF hell hlo hup≤
      (ell*r^2)*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1) := by
  have hb := mul_le_mul_of_nonneg_left (cell_payment P hK hc hsmall hC hy hF hell hlo hup r hr)
    (div_nonneg hr.le endpoint_pos.le)
  change (r/samplingEnd 1)*_≤_ at hb
  apply hb.trans_eq
  field_simp [endpoint_pos.ne']

/-- The executed collocation rows retain their physical r^3 factor. -/
theorem residual_payment :
    PrivateCompletedRms.residualBudget S r hr hF hell hlo hup≤
      (ell*r^3)*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1) := by
  have hb := mul_le_mul_of_nonneg_left (cell_payment P hK hc hsmall hC hy hF hell hlo hup r hr)
    (mul_nonneg (sq_nonneg r) endpoint_pos.le)
  have he : (samplingEnd 1)^2≤1 := by nlinarith [endpoint_pos,endpoint_lt_one]
  change _≤_ at hb
  calc
    _ ≤ r^2*(samplingEnd 1)*((samplingEnd 1)*(ell*r)*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1)) := hb
    _ = (samplingEnd 1)^2*((ell*r^3)*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1)) := by ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity [P.delta_pos]) he

end AcceleratedLogConcave.Root.CoolingPrescribedPayments
