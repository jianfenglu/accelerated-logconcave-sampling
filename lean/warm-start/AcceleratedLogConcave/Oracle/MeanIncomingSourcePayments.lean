import AcceleratedLogConcave.Oracle.MeanIncomingPrivateAccuracy
import AcceleratedLogConcave.Oracle.PrivateSourceScalarAbsorption

/-! The actual private anchor payment at the prescribed source geometry.
The private width tau=R/backwardEnd R and the literal stored-anchor scaling
cancel exactly. Only scalar schedule and original-potential conditions enter. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.MeanIncomingSourcePayments
open Numerics Numerics.AffineGraph PrivateSourceScalarAbsorption
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : threshold P≤P.y)
local notation "baseHy" => base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "M" => PrescribedSourceGeometry.meanGeometry P.m P.R P.h0 P.R_pos hR P.h0_pos
local notation "mesh" => PrescribedSourceGeometry.privateMesh P.R P.h0 P.R_pos hR P.h0_pos
local notation "S" => PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos hR P.h0_pos
variable {d sn : ℕ}
  (snodes : Fin sn ≃ (PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos
    (CubicSchedulePayments.radius_guard P hK hc hsmall hC
      (base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos).Node)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (r : ℝ) (hr : 0<r) (hr1 : r≤1) (hellδ : ell≤P.delta)
local notation "kappa" => twiceNonneg ell hell
local notation "sigmaM" => RecursiveMeanPublicTable.mainWidth sn r (S).R P.Ds (r^2)
local notation "sigmaF" => SourceExecutableTables.samplingFinalWidth S r

/-- The exact finite source helper budget with its prescribed LOWER
constant-four amplitudes. All executed private main/final calls use q-1/4. -/
def privatePayment (base : Point d) (α : ℝ) : ℝ :=
  MeanIncomingPrivateAccuracy.privateBudget M mesh snodes r hr P.NP hF hell hlo hup
    base kappa kappa (fun _ _ => 4*sigmaM*P.delta^α) (fun _ => 4*sigmaF*P.delta^α)

include hr1 hellδ in
/-- Literal backwardEnd R scaling turns the proved private constant-three
payment into 3R delta^alpha D_F(x). There is no private accuracy hypothesis. -/
theorem anchor_payment_le (base : Point d) (α : ℝ) (hα : α≤(P.K:ℝ)) :
    backwardEnd P.R*privatePayment P hK hc hsmall hC hy snodes hF hell hlo hup r hr base α ≤
      3*P.R*P.delta^α*Gibbs.primitiveScale F base := by
  have hp := source_retained_payment_le P hK hc hsmall hC hy snodes hF hell hlo hup r hr hr1 hellδ base α hα
  have hb : 0<backwardEnd P.R := (M).backwardEnd_pos
  calc
    _ ≤ backwardEnd P.R*(3*(S).τ*P.delta^α*Gibbs.primitiveScale F base) :=
      mul_le_mul_of_nonneg_left hp hb.le
    _ = _ := by
      change backwardEnd P.R*(3*(P.R/backwardEnd P.R)*P.delta^α*Gibbs.primitiveScale F base)=_
      field_simp [hb.ne']

include hr1 hellδ in
/-- Exact squared stored-anchor payment for the recursive q-1/4 family. -/
theorem recursive_anchor_payment_sq (base : Point d) (q : ℝ) (hq : q≤(P.K:ℝ)) :
    (backwardEnd P.R*privatePayment P hK hc hsmall hC hy snodes hF hell hlo hup r hr base (q-1/4))^2 ≤
      (3*P.R*P.delta^(q-1/4)*Gibbs.primitiveScale F base)^2 := by
  have hp := anchor_payment_le P hK hc hsmall hC hy snodes hF hell hlo hup r hr hr1 hellδ base (q-1/4)
    (by linarith)
  have hn : 0≤3*P.R*P.delta^(q-1/4)*Gibbs.primitiveScale F base := by
    positivity [P.R_pos,P.delta_pos,Gibbs.primitiveScale_nonneg F base]
  let flowData := PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr
  have hcell : 0≤AffineResidual.cellBudget (S).mesh P.m
      (SamplingGaussianJetLp.cellDerivativeBudget flowData (S).mesh P.m) := by
    unfold AffineResidual.cellBudget
    apply Finset.sum_nonneg
    intro c _
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ((S).mesh.length_pos c).le _))
      (SamplingGaussianJetLp.cellDerivativeBudget_nonneg flowData (S).mesh P.m c)) (Nat.cast_nonneg _)
  have hpay : 0≤privatePayment P hK hc hsmall hC hy snodes hF hell hlo hup r hr base (q-1/4) := by
    unfold privatePayment MeanIncomingPrivateAccuracy.privateBudget PrivateCompletedRms.mainBudget
      PrivateCompletedRms.initializerBudget PrivateCompletedRms.quadratureBudget Collocation.forcingSum
      SharedLayerRms.childRowBudget PrivateCompletedRms.childPayment
    positivity [hcell,(S).samplingEnd_pos,PrivateSamplingOriginalBounds.replyBudget_nonneg flowData base,
      PrivateCompletedRms.residualBudget_nonneg S r hr hF hell hlo hup]
  exact (sq_le_sq₀ (mul_nonneg (M).backwardEnd_pos.le hpay) hn).2 hp

end AcceleratedLogConcave.Oracle.MeanIncomingSourcePayments
