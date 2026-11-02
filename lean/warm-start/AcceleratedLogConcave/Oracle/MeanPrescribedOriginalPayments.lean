import AcceleratedLogConcave.Oracle.PrescribedMeanNumericalData
import AcceleratedLogConcave.Oracle.MeanSourceScalarAbsorption

/-! Original-data quadrature budgets on the actual prescribed executable
geometry. Analytic regularity is supplied by the proved C2 smooth receiver;
scalar order growth is paid by the explicit dimension-free source threshold. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
namespace AcceleratedLogConcave.Oracle.MeanPrescribedOriginalPayments
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall RecursiveSize
open MeanFlowLp MeanCollocationLp SmoothQuantitativeAssembly SmoothQuadraturePayments
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "privateHy" => MeanSourceScalarAbsorption.private_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) privateHy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
variable {D : ℕ} {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (x : Point D) (r σ : ℝ) (hr : 0<r) (hσ : 0<σ) (hcurv : r^2*ell≤1/2)
local notation "d" => PrescribedMeanNumericalData.datum P hR hF hell hlo hup x r σ hr hσ hcurv

/-- Concrete mean row residual. The remaining inputs here are scalar size
bounds only, and will be supplied by the actual occurrence path below. -/
theorem residual_payment {b S : ℝ} (hb : (1:ℝ)/2≤b) (hS : 1≤S)
    (hsize : ell*r/σ≤S*P.delta^b)
    (hres : P.delta≤(520*(P.m:ℝ)^5*S)^(-12:ℝ)) :
    MeanOriginalBounds.residualBudget d P.h0≤r*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1) := by
  have hC1 : 1≤P.Csch := by linarith
  have hm := P.m_ge_two hc hsmall hC1
  have hd := P.delta_le_one (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  have hmsh := PrescribedMeanNumericalData.scheduled_mesh P hF hell hlo hup x r σ hr hσ hcurv hK hc hsmall hC privateHy
  have hs := centerSpeed_le_of_resolution d hm P.delta_pos hd (P.w_pos hc).le
    (P.w_lt_t hc hC1).le (P.t_le hc hsmall) hb hS rfl hsize hres
  have hpsi : (d).G.psi=P.delta^(4*P.t) := P.psi_eq_R_pow.symm
  have hp := SmoothRowPayments.residual_payment d P.delta_pos hd (P.w_pos hc).le
    (P.w_lt_t hc hC1).le (P.t_le hc hsmall) hmsh hs rfl hpsi (fun _ => rfl) (fun _ => rfl)
    (velocityBounds_original_data d) (angleBounds_original_data d (by omega))
  have hratio := SourcePhysicalSmallness.ratio_small (by omega : 1≤P.m) P.delta_pos hd hb hS hsize hres
  have hcoef := SmoothInventoryDimension.norm_rowCoefficient_le_dimension d (by omega)
    ((d).G.R_le_half.trans (by norm_num)) hratio
  have hEnv := SourcePhysicalError.A_value_bound (m := P.m) (by omega : 1≤P.m)
  have hpay := MeanSourceScalarAbsorption.row_order_payment P hK hc hsmall hC hy
  change MeanOriginalBounds.residualBudget d P.h0≤_
  calc
    _ ≤ (r*Real.sqrt (D:ℝ)*SmoothInventoryDimension.A P.m)*P.delta^(SmoothRowPayments.exponent P.m P.w P.t) :=
      hp.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg P.delta_pos.le _))
    _ ≤ (r*Real.sqrt (D:ℝ)*SourceOutputCoefficient.orderEnvelope P.m)*P.delta^(SmoothRowPayments.exponent P.m P.w P.t) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEnv (mul_nonneg hr.le (Real.sqrt_nonneg _))) (Real.rpow_nonneg P.delta_pos.le _)
    _ ≤ r*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hpay (mul_nonneg hr.le (Real.sqrt_nonneg _))

/-- The full center payment retains its original factor two, and vanishes
at zero curvature or zero dimension. -/
theorem centering_payment {b S : ℝ} (hb : (1:ℝ)/2≤b) (hS : 1≤S)
    (hsize : ell*r/σ≤S*P.delta^b)
    (hres : P.delta≤(520*(P.m:ℝ)^5*S)^(-12:ℝ)) :
    MeanOriginalBounds.quadratureBudget d≤(ell*r*Real.sqrt (D:ℝ)/2)*P.delta^((P.K:ℝ)+1) := by
  have hC1 : 1≤P.Csch := by linarith
  have hm := P.m_ge_two hc hsmall hC1
  have hd := P.delta_le_one (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  have hs := centerSpeed_le_of_resolution d hm P.delta_pos hd (P.w_pos hc).le
    (P.w_lt_t hc hC1).le (P.t_le hc hsmall) hb hS rfl hsize hres
  have hcenter := centering_defect_le d (by omega) P.delta_pos hs
  have he := SourceOutputCoefficient.centering_coefficient_eq d
  rw [he] at hcenter
  have hscore := SourceOutputCoefficient.scoreUnit_le_orderEnvelope P.m
  have hpay := MeanSourceScalarAbsorption.center_order_payment P hK hc hsmall hC hy
  change MeanOriginalBounds.quadratureBudget d≤_
  calc
    _ ≤ (ell*r*Real.sqrt (D:ℝ))*(SmoothInventoryDimension.scoreUnit P.m/2)*P.delta^((P.m:ℝ)/3) := hcenter
    _ ≤ (ell*r*Real.sqrt (D:ℝ))*(SourceOutputCoefficient.orderEnvelope P.m/2)*P.delta^((P.m:ℝ)/3) := by
      gcongr
      exact Real.rpow_nonneg P.delta_pos.le _
    _ = (ell*r*Real.sqrt (D:ℝ)/2)*(SourceOutputCoefficient.orderEnvelope P.m*P.delta^((P.m:ℝ)/3)) := by ring
    _ ≤ (ell*r*Real.sqrt (D:ℝ)/2)*P.delta^((P.K:ℝ)+1) :=
      mul_le_mul_of_nonneg_left hpay (by positivity)

section Reachable
variable {r0 σ0 : ℝ} (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hroot : ell*r0^2≤P.delta) (hrootRatio : ell*(r0/σ0)≤P.delta)
  {p : State} {depth cost : ℕ}

include hell hr0 hσ0 hroot hrootRatio in
/-- All scalar size facts consumed by the smooth receiver are derived from
the actual root and occurrence path, including terminal overshoots. -/
theorem reachable_sizes
    (hp : Path (source P hR) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    let b := 1-10*P.t*(Precision.precisionRank (1/4) (P.K:ℝ):ℝ)
    let S := (stepFactor P.m P.Bsize)^(Precision.precisionRank P.t (P.K:ℝ))
    (1:ℝ)/2≤b ∧ 1≤S ∧ ell*p.radius/p.width≤S*P.delta^b ∧
      P.delta≤(520*(P.m:ℝ)^5*S)^(-12:ℝ) := by
  dsimp only
  have hC1 : 1≤P.Csch := by linarith
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC baseHy
  have hm := P.m_ge_two hc hsmall hC1
  have hB := P.Bsize_ge_one hc hsmall hC1 hy0
  have hb : SizeBound ell P.delta 1 1 r0 σ0 := by
    change ell*r0^2≤1*P.delta^1 ∧ ell*(r0/σ0)≤1*P.delta^1
    simpa only [Real.rpow_one,one_mul] using And.intro hroot hrootRatio
  have hsize := hp.root_cap_size ell P.Bsize hb (by omega) hell hr0 hσ0
    P.Ds_pos P.delta_pos (P.delta_le_one hy0) (P.t_pos hc) (step_quarter P hc hsmall)
    (P.w_pos hc).le (P.w_lt_t hc hC1).le hB rfl le_rfl
    hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2
  have hstep : 1≤stepFactor P.m P.Bsize := (by norm_num : (1:ℝ)≤3).trans
    (stepFactor_ge_three P.m P.Bsize (by linarith))
  refine ⟨by have := P.rank_budget hc hsmall; linarith, one_le_pow₀ hstep, ?_, hs.2.2.2.2.1⟩
  have hz : ell*(p.radius/p.width)≤
      (stepFactor P.m P.Bsize)^(Precision.precisionRank P.t (P.K:ℝ))*
        P.delta^(1-10*P.t*(Precision.precisionRank (1/4) (P.K:ℝ):ℝ)) := hsize.2
  simpa only [mul_div_assoc] using hz

include hrootRatio in
/-- The original-data residual of every actual reachable mean call has its
source precision payment, with no residual estimate among the inputs. -/
theorem reachable_residual_payment
    (hp : Path (source P hR) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    MeanOriginalBounds.residualBudget
      (PrescribedMeanNumericalData.reachableDatum P hF hell hlo hup x hK hc hsmall hC privateHy hr0 hσ0 hroot hp) P.h0≤
        p.radius*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1) := by
  obtain ⟨hb,hS,hsize,hres⟩ := reachable_sizes P hK hc hsmall hC hy hell hr0 hσ0 hroot hrootRatio hp
  exact residual_payment P hK hc hsmall hC hy hF hell hlo hup x p.radius p.width _ _ _ hb hS hsize hres

include hrootRatio in
/-- The actual reachable final center row has its full quantitative payment. -/
theorem reachable_centering_payment
    (hp : Path (source P hR) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    MeanOriginalBounds.quadratureBudget
      (PrescribedMeanNumericalData.reachableDatum P hF hell hlo hup x hK hc hsmall hC privateHy hr0 hσ0 hroot hp)≤
        (ell*p.radius*Real.sqrt (D:ℝ)/2)*P.delta^((P.K:ℝ)+1) := by
  obtain ⟨hb,hS,hsize,hres⟩ := reachable_sizes P hK hc hsmall hC hy hell hr0 hσ0 hroot hrootRatio hp
  exact centering_payment P hK hc hsmall hC hy hF hell hlo hup x p.radius p.width _ _ _ hb hS hsize hres

include hrootRatio in
/-- The deterministic residual prerequisite of the all-node moment reduction
is supplied on every actual path, from an original root slope bound only. -/
theorem reachable_residual_scale
    (hslope : ell*r0≤1)
    (hp : Path (source P hR) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    ell*MeanOriginalBounds.residualBudget
      (PrescribedMeanNumericalData.reachableDatum P hF hell hlo hup x hK hc hsmall hC privateHy hr0 hσ0 hroot hp) P.h0≤
        Gibbs.primitiveScale F x := by
  have hb := reachable_residual_payment P hK hc hsmall hC hy hF hell hlo hup x hr0 hσ0 hroot hrootRatio hp
  have hm := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  have hrp := PrescribedTerminalAccuracy.radius_le_root hp (by omega) P.Ds_pos P.delta_pos hr0 hσ0
  change p.radius≤r0 at hrp
  have hsl : ell*p.radius≤1 := (mul_le_mul_of_nonneg_left hrp hell).trans hslope
  have hd := P.delta_le_one (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  have ht : P.delta^((P.K:ℝ)+1)≤1 := Real.rpow_le_one P.delta_pos.le hd (by positivity)
  have hpos := hp.positive (by omega) P.Ds_pos P.delta_pos hr0 hσ0
  have hb' := mul_le_mul_of_nonneg_left hb hell
  have hc' : ell*(p.radius*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1))≤Real.sqrt (D:ℝ) := by
    calc
      _ = (ell*p.radius)*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1) := by ring
      _ ≤ 1*Real.sqrt (D:ℝ)*1 := mul_le_mul
        (mul_le_mul_of_nonneg_right hsl (Real.sqrt_nonneg _)) ht
        (Real.rpow_nonneg P.delta_pos.le _) (by positivity)
      _ = _ := by ring
  apply (hb'.trans hc').trans
  unfold Gibbs.primitiveScale
  simp only [finrank_euclideanSpace_fin]
  exact le_add_of_nonneg_right (norm_nonneg _)

end Reachable

end AcceleratedLogConcave.Oracle.MeanPrescribedOriginalPayments
