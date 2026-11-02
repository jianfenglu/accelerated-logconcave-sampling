import AcceleratedLogConcave.Oracle.PrivateCompletedRms
import Mathlib.Analysis.Complex.ExponentialBounds
import AcceleratedLogConcave.Numerics.SmoothConditionalOrder

/-! Explicit analytic enlargement of the manuscript's cubic resolution
constant. The two schedule constants are fixed before K, dimension and y.
The old work/geometry threshold remains a lower bound. No residual or desired
accuracy estimate is an input to the order-factor payment. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.PrivateSourceScalarAbsorption
open Numerics Numerics.AffineGraph Numerics.ConditionalSmoothing
open SourceSchedule SchedulePolynomialBounds PrivateSamplingMeshPayments

/-- Dimension-free numerical envelope at the actual derivative order. -/
def orderConstant (m : ℕ) : ℝ := 2^(m+1)*conditionalOrderEnvelope m

theorem orderConstant_pos {m : ℕ} (hm : 1≤m) : 0<orderConstant m := by
  unfold orderConstant conditionalOrderEnvelope
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  positivity

/-- The only dimension factor is exactly sqrt(d); factorial savings are
retained in the source supplier and may safely be discarded for this envelope. -/
theorem orderFactor_le (D m : ℕ) (hm : 1≤m) :
    orderFactor D m ≤ Real.sqrt (D:ℝ)*orderConstant m := by
  have hn : m-1+1=m := by omega
  have hf : (1:ℝ)≤(m.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hmat := materialOrderFactor_le D (m-1)
  rw [hn] at hmat
  unfold orderFactor orderConstant
  calc
    _ ≤ 2^(m+1)*(Real.sqrt (D:ℝ)*conditionalOrderEnvelope m)/(m.factorial:ℝ) := by gcongr
    _ ≤ 2^(m+1)*(Real.sqrt (D:ℝ)*conditionalOrderEnvelope m) :=
      div_le_self (by positivity [conditionalOrderEnvelope_nonneg m]) hf
    _ = _ := by ring

theorem log_orderConstant_le (m : ℕ) (hm : 1≤m) :
    Real.log (orderConstant m) ≤ 14*(m:ℝ)*Real.log (12*(m:ℝ)) := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hlog : Real.log 2≤Real.log (12*(m:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hnon : 0≤Real.log (12*(m:ℝ)) := Real.log_nonneg (by linarith)
  unfold orderConstant conditionalOrderEnvelope
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
  push_cast
  have h1 := mul_le_mul_of_nonneg_left hlog (show 0≤(m:ℝ)+1 by positivity)
  nlinarith [mul_nonneg (show 0≤(m:ℝ)-1 by linarith) hnon]

/-- A valid explicit enlargement of the absolute cubic coefficient, depending
only on the two fixed schedule constants. -/
def Cquad (c C : ℝ) : ℝ :=
  28672*C^2/c^2*(2*Real.log (12*CubicScheduleThreshold.m0 c C)+4)

def Ccomplete (c C : ℝ) : ℝ := CubicScheduleThreshold.C1 c C+Cquad c C

def threshold (P : SourceSchedule) : ℝ :=
  Ccomplete P.csch P.Csch*(P.K:ℝ)^3*Real.log (u P)

variable (P : SourceSchedule)

theorem Cquad_nonneg (hc : 0<P.csch) (hc1 : P.csch≤1) (hC : 1≤P.Csch) :
    0≤Cquad P.csch P.Csch := by
  have hm := CubicScheduleThreshold.m0_ge_one hc hc1 hC
  have hlog : 0≤Real.log (12*CubicScheduleThreshold.m0 P.csch P.Csch) := Real.log_nonneg (by linarith)
  unfold Cquad
  positivity

/-- Enlarging the analytic coefficient preserves every existing work and
geometry consumer of the former threshold. -/
theorem base_threshold (hc : 0<P.csch) (hc1 : P.csch≤1) (hC : 1≤P.Csch)
    (hy : threshold P≤P.y) : CubicScheduleThreshold.threshold P≤P.y := by
  have hn := Cquad_nonneg P hc hc1 hC
  have hL := CubicScheduleThreshold.log_u_ge_half P
  apply le_trans _ hy
  unfold threshold Ccomplete CubicScheduleThreshold.threshold
  gcongr
  exact le_add_of_nonneg_right hn

/-- The cubic coefficient pays the actual order's logarithmic growth. No
accuracy, cell regularity, or desired numerical-error premise is assumed. -/
theorem quad_log_payment (hK : 10≤P.K) (hc : 0<P.csch) (hc1 : P.csch≤1)
    (hC : 1≤P.Csch) (hy : threshold P≤P.y) :
    (56/P.w)*Real.log (12*(P.m:ℝ)) ≤ P.y := by
  have hm := CubicScheduleThreshold.m0_ge_one hc hc1 hC
  have hup := u_pos P
  have hlog0 : 0≤Real.log (12*CubicScheduleThreshold.m0 P.csch P.Csch) := Real.log_nonneg (by linarith)
  have hmu := CubicScheduleThreshold.m_upper_scaled P hc hc1 hC
  have hmpos : (0:ℝ)<P.m := by exact_mod_cast P.m_pos hc hC
  have hu := CubicScheduleThreshold.log_u_ge_half P
  have hlog : Real.log (12*(P.m:ℝ)) ≤
      (2*Real.log (12*CubicScheduleThreshold.m0 P.csch P.Csch)+4)*Real.log (u P) := by
    have h := Real.log_le_log (by positivity : 0<12*(P.m:ℝ))
      (mul_le_mul_of_nonneg_left hmu (by norm_num : (0:ℝ)≤12))
    have he : Real.log (12*(CubicScheduleThreshold.m0 P.csch P.Csch*(u P)^4)) =
        Real.log (12*CubicScheduleThreshold.m0 P.csch P.Csch)+4*Real.log (u P) := by
      rw [show 12*(CubicScheduleThreshold.m0 P.csch P.Csch*(u P)^4) =
        (12*CubicScheduleThreshold.m0 P.csch P.Csch)*(u P)^4 by ring,
        Real.log_mul (by positivity) (by positivity),Real.log_pow]
      norm_num
    rw [he] at h
    nlinarith [mul_le_mul_of_nonneg_left hu hlog0]
  have hinv := inv_w_upper P hc hc1 hC
  have hu3 := CubicScheduleThreshold.u_cube_le P hK
  have hLp : 0≤Real.log (u P) := by linarith
  have hpositive : 0≤Real.log (12*(P.m:ℝ)) :=
    Real.log_nonneg (by
      have hmr : (1:ℝ)≤P.m := by exact_mod_cast P.m_pos hc hC
      linarith)
  have hquad : (56/P.w)*Real.log (12*(P.m:ℝ)) ≤
      Cquad P.csch P.Csch*(P.K:ℝ)^3*Real.log (u P) := by
    calc
      _ ≤ 56*(256*P.Csch^2*(u P)^3/P.csch^2)*
          ((2*Real.log (12*CubicScheduleThreshold.m0 P.csch P.Csch)+4)*Real.log (u P)) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (show P.w⁻¹≤_ from by simpa only [one_div] using hinv) (by norm_num)) hlog hpositive (by positivity)
      _ ≤ 56*(256*P.Csch^2*(2*(P.K:ℝ)^3)/P.csch^2)*
          ((2*Real.log (12*CubicScheduleThreshold.m0 P.csch P.Csch)+4)*Real.log (u P)) := by gcongr
      _ = _ := by unfold Cquad; ring
  apply hquad.trans
  apply le_trans _ hy
  unfold threshold Ccomplete
  have hbase := (CubicScheduleThreshold.coefficients_nonneg hc hc1 hC).2.2
  gcongr
  linarith

/-- The exact prescribed order factor is absorbed into K+1 powers at the
manuscript's permitted enlarged cubic threshold. -/
theorem order_payment (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
    (hC : 8≤P.Csch) (hy : threshold P≤P.y) :
    orderConstant P.m*P.delta^P.A ≤ P.delta^((P.K:ℝ)+1) := by
  have hc1 : P.csch≤1 := by linarith
  have hC1 : 1≤P.Csch := by linarith
  have hp := CubicSchedulePayments.prerequisites P hK hc hsmall hC (base_threshold P hc hc1 hC1 hy)
  have hw := P.w_pos hc
  have hm : 1≤P.m := by have := P.m_ge_two hc hsmall hC1; omega
  have hA : 8*((P.K:ℝ)+2)≤P.A := by
    exact mul_le_mul_of_nonneg_right hC (by positivity)
  have hmargin : P.A/2≤P.A-((P.K:ℝ)+1) := by nlinarith [Nat.cast_nonneg (α := ℝ) P.K]
  have hmw : (P.m:ℝ)*P.w ≤ 2*P.A := by
    have hb := (P.m_bounds hc hC1).2
    have ht := (P.w_lt_t hc hC1).trans_le (P.t_le hc hsmall)
    have hh := (lt_div_iff₀ hw).mp (show (P.m:ℝ)-1<P.A/P.w by linarith)
    nlinarith [Nat.cast_nonneg (α := ℝ) P.K]
  have hscale : 14*(P.m:ℝ) ≤ (P.A-((P.K:ℝ)+1))*(56/P.w) := by
    apply (mul_le_mul_iff_left₀ hw).mp
    have he : ((P.A-((P.K:ℝ)+1))*(56/P.w))*P.w = 56*(P.A-((P.K:ℝ)+1)) := by field_simp
    rw [he]
    nlinarith
  have hlog := log_orderConstant_le P.m hm
  have hlognon : 0≤Real.log (12*(P.m:ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1≤12*P.m by omega))
  have hpaid := quad_log_payment P hK hc hc1 hC1 hy
  have hconst : Real.log (orderConstant P.m) ≤ (P.A-((P.K:ℝ)+1))*P.y :=
    hlog.trans ((mul_le_mul_of_nonneg_right hscale hlognon).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpaid (by linarith : 0≤P.A-((P.K:ℝ)+1))))
  apply (Real.log_le_log_iff (mul_pos (orderConstant_pos hm) (Real.rpow_pos_of_pos P.delta_pos _))
    (Real.rpow_pos_of_pos P.delta_pos _)).mp
  rw [Real.log_mul (orderConstant_pos hm).ne' (Real.rpow_pos_of_pos P.delta_pos _).ne',
    Real.log_rpow P.delta_pos,Real.log_rpow P.delta_pos,delta,Real.log_exp]
  nlinarith


/-- The enlarged coefficient still gives a very small source resolution. -/
theorem delta_le_hundredth (hK : 10≤P.K) (hc : 0<P.csch) (hc1 : P.csch≤1)
    (hC : 1≤P.Csch) (hy : threshold P≤P.y) : P.delta≤1/100 := by
  have hbase := (CubicScheduleThreshold.coefficients_nonneg hc hc1 hC).2.2
  have hquad := Cquad_nonneg P hc hc1 hC
  have hco : 1≤Ccomplete P.csch P.Csch := by unfold Ccomplete; linarith
  have hkr : (10:ℝ)≤P.K := by exact_mod_cast hK
  have hkpow : (1000:ℝ)≤(P.K:ℝ)^3 := by
    exact (by norm_num : (1000:ℝ)=10^3).trans_le (pow_le_pow_left₀ (by norm_num) hkr 3)
  have hlog := CubicScheduleThreshold.log_u_ge_half P
  have hthr : (100:ℝ)≤threshold P := by
    unfold threshold
    nlinarith [mul_le_mul_of_nonneg_right hco (mul_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) P.K) 3) (by linarith : 0≤Real.log (u P)))]
  have hy100 : (100:ℝ)≤P.y := hthr.trans hy
  have hlog100 : Real.log (100:ℝ)≤100 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  calc
    P.delta ≤ Real.exp (-Real.log (100:ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1/100 := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num

section OriginalBudget
variable {D : ℕ} {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v, 0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (r : ℝ) (hr : 0<r)
variable (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : threshold P≤P.y)
local notation "baseHy" => base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "S" => PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos hR P.h0_pos
local notation "d" => PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr

/-- The actual prescribed endpoint budget, after paying its exact derivative
order factor. The physical r/rhoEnd factor has already canceled locally. -/
theorem source_quadrature_budget :
    PrivateCompletedRms.quadratureBudget S r hr hF hell hlo hup ≤
      (ell*r^2)*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1) := by
  have hb := source_finalBudget P hK hc hsmall hC baseHy hF hell hlo hup r hr
  have hm : 1≤P.m := by have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch); omega
  have hfactor := orderFactor_le D P.m hm
  have hpaid := order_payment P hK hc hsmall hC hy
  have hδpow : 0≤P.delta^P.A := (Real.rpow_pos_of_pos P.delta_pos _).le
  calc
    _ ≤ (ell*r^2)*orderFactor D P.m*P.delta^P.A := hb
    _ ≤ (ell*r^2)*(Real.sqrt (D:ℝ)*orderConstant P.m)*P.delta^P.A := by gcongr
    _ = (ell*r^2)*Real.sqrt (D:ℝ)*(orderConstant P.m*P.delta^P.A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpaid (by positivity)

/-- The same payment applies to each actual collocation row, with the
source's physical r^3 factor and no endpoint denominator. -/
theorem source_residual_budget :
    PrivateCompletedRms.residualBudget S r hr hF hell hlo hup ≤
      (ell*r^3)*Real.sqrt (D:ℝ)*P.delta^((P.K:ℝ)+1) := by
  have hp := CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy
  have hhalf := (ScalarSchedulePayment.geometry_caps P hc hsmall (by linarith) hp.1 hp.2.2).2.2.2
  have hb := prescribed_rowBudget P.m P.R P.h0 P.R_pos hR P.h0_pos hF hell hlo hup r hr hhalf
  have hm : 1≤P.m := by have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch); omega
  have hpow := source_power P hc (by linarith) hp.1
  have hfactor := orderFactor_le D P.m hm
  have hpaid := order_payment P hK hc hsmall hC hy
  have hδpow : 0≤P.delta^P.A := (Real.rpow_pos_of_pos P.delta_pos _).le
  have hhpow : 0≤P.h0^P.m := pow_nonneg P.h0_pos.le _
  have horder := orderFactor_nonneg D P.m
  have hend : (samplingEnd (S).τ)^2≤1 := by
    nlinarith [(S).samplingEnd_pos,(S).samplingEnd_lt_one]
  calc
    _ ≤ ell*r^3*(samplingEnd (S).τ)^2*orderFactor D P.m*P.h0^P.m := hb
    _ ≤ ell*r^3*1*orderFactor D P.m*P.delta^P.A := by gcongr
    _ ≤ ell*r^3*1*(Real.sqrt (D:ℝ)*orderConstant P.m)*P.delta^P.A := by gcongr
    _ = (ell*r^3)*Real.sqrt (D:ℝ)*(orderConstant P.m*P.delta^P.A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpaid (by positivity)
end OriginalBudget

section MomentNormalization
variable {D : ℕ} (d : SamplingCenterLp.Data (Fin D)) (x : Point D)
local notation "B" => Gibbs.primitiveScale d.F x
local notation "dim" => Real.sqrt (Module.finrank ℝ (Point D))

/-- Original-gradient reply budget on the source radius/curvature domain. -/
theorem reply_budget_le_twice (hr1 : d.r≤1) (hellsmall : d.ell≤1/100) :
    PrivateSamplingOriginalBounds.replyBudget d x ≤ 2*B := by
  have hdim : 0≤dim := Real.sqrt_nonneg _
  have hg : 0≤‖gradient d.F x‖ := norm_nonneg _
  have hB : 0≤B := Gibbs.primitiveScale_nonneg _ _
  have hlr : 0≤d.ell*d.r := mul_nonneg d.hell d.hr.le
  have hlr1 : d.ell*d.r≤1/100 := (mul_le_mul_of_nonneg_left hr1 d.hell).trans (by simpa using hellsmall)
  have hin : dim+d.r*‖gradient d.F x‖≤B := by
    unfold Gibbs.primitiveScale
    nlinarith [mul_le_mul_of_nonneg_right hr1 hg]
  have he := Real.exp_one_lt_three.le
  have h1 := mul_le_mul_of_nonneg_left hin hlr
  have h2 := mul_le_mul_of_nonneg_left hlr1 hB
  have h3 := mul_le_mul_of_nonneg_left he hlr
  have h4 := mul_le_mul_of_nonneg_right h3 hdim
  have h5 := mul_le_mul_of_nonneg_right hlr1 hdim
  unfold PrivateSamplingOriginalBounds.replyBudget
  dsimp only [Gibbs.primitiveScale] at *
  nlinarith

/-- The existing concrete squareBudget is sufficient for the constant-four
induction: its square root is at most 3D_F(x)/2, uniformly at actual nodes. -/
theorem square_budget_le (hr1 : d.r≤1) (hellsmall : d.ell≤1/100)
    {t : ℝ} (ht : t∈Icc 0 d.b) :
    PrivateBenchmarkMoments.squareBudget d x t ≤ ((3/2:ℝ)*B)^2 := by
  have hreply := reply_budget_le_twice d x hr1 hellsmall
  have hB := Gibbs.primitiveScale_nonneg d.F x
  have hdim := Real.sqrt_nonneg (Module.finrank ℝ (Point D))
  have hdimB : dim≤B := by unfold Gibbs.primitiveScale; exact le_add_of_nonneg_right (norm_nonneg _)
  have ht1 : t≤1 := ht.2.trans d.hb1.le
  have hrt : 0≤d.r*t := mul_nonneg d.hr.le ht.1
  have hrt1 : d.r*t≤1 := (mul_le_mul_of_nonneg_left ht1 d.hr.le).trans (by simpa using hr1)
  have hcoef : 0≤d.ell*d.r*t := by positivity [d.hell,ht.1,d.hr.le]
  have hcoef1 : d.ell*d.r*t≤1/100 := by
    nlinarith [mul_le_mul_of_nonneg_left hrt1 d.hell]
  have hinner : 0≤dim+d.r*t*PrivateSamplingOriginalBounds.replyBudget d x := by
    positivity [PrivateSamplingOriginalBounds.replyBudget_nonneg d x]
  have hinnerB : dim+d.r*t*PrivateSamplingOriginalBounds.replyBudget d x≤3*B := by
    have h := mul_le_mul hrt1 hreply (PrivateSamplingOriginalBounds.replyBudget_nonneg d x) (by positivity : 0≤(1:ℝ))
    nlinarith
  have hprod : (d.ell*d.r*t)*(dim+d.r*t*PrivateSamplingOriginalBounds.replyBudget d x) ≤ (3/100:ℝ)*B := by
    have h := mul_le_mul hcoef1 hinnerB hinner (by norm_num : (0:ℝ)≤1/100)
    nlinarith
  have hsq := pow_le_pow_left₀ (mul_nonneg hcoef hinner) hprod 2
  unfold PrivateBenchmarkMoments.squareBudget
  nlinarith [sq_nonneg B]
end MomentNormalization


/-- Finite collocation forcing is bounded by the geometric sum actually
executed; no infinite solver is substituted. -/
theorem finite_forcing_le (N : ℕ) {χ T : ℝ} (hχ : 0≤χ) (hχ1 : χ≤1/10)
    (hT : 0≤T) (η : ℕ → ℝ) (hη : ∀ k, k<N → η k≤T) :
    Collocation.forcingSum χ η N ≤ (10/9:ℝ)*T := by
  have hsum : Collocation.forcingSum χ η N ≤ Collocation.forcingSum χ (fun _ => T) N := by
    unfold Collocation.forcingSum
    exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hη k (Finset.mem_range.mp hk)) (pow_nonneg hχ _)
  rw [Collocation.forcingSum_const] at hsum
  have hgeom : (∑ j ∈ Finset.range N, χ^j)≤1/(1-χ) := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hχ (by linarith : χ<1))
  have hrec : 1/(1-χ)≤(10/9:ℝ) := (div_le_iff₀ (by linarith : 0<1-χ)).2 (by linarith)
  exact hsum.trans ((mul_le_mul_of_nonneg_left (hgeom.trans hrec) hT).trans_eq (by ring))

/-- The literal source layer count pays the initializer's transient. -/
theorem transient_power (hC : 8≤P.Csch) (hδ : P.delta≤1/100) {χ : ℝ}
    (hχ : 0≤χ) (hχδ : χ≤2*P.delta) : χ^P.NP≤P.delta^((P.K:ℝ)+2) := by
  have hδ0 := P.delta_pos
  have hs : χ≤Real.sqrt P.delta := by
    have hsq := Real.sq_sqrt hδ0.le
    have hn := Real.sqrt_nonneg P.delta
    nlinarith [mul_le_mul_of_nonneg_right hδ hδ0.le]
  have hn : 2*(P.K+2)≤P.NP := by
    have h := (P.NP_bounds (by linarith : 1≤P.Csch)).1
    have ha := mul_le_mul_of_nonneg_right hC (by positivity : (0:ℝ)≤(P.K:ℝ)+2)
    change 8*((P.K:ℝ)+2)≤P.A at ha
    exact_mod_cast (show 2*((P.K:ℝ)+2)≤(P.NP:ℝ) by linarith [Nat.cast_nonneg (α := ℝ) P.K])
  calc
    _ ≤ (Real.sqrt P.delta)^P.NP := pow_le_pow_left₀ hχ hs _
    _ ≤ (Real.sqrt P.delta)^(2*(P.K+2)) :=
      pow_le_pow_of_le_one (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (by linarith)) hn
    _ = P.delta^((P.K:ℝ)+2) := by
      rw [pow_mul,Real.sq_sqrt hδ0.le,←Real.rpow_natCast]
      congr 1
      push_cast
      rfl

section ScalarMoments
variable {D m n : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r : ℝ) (hr : 0<r) {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v, 0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
local notation "data" => PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr
local notation "B" => Gibbs.primitiveScale F

theorem child_payment_le (hr1 : r≤1) (hellsmall : ell≤1/100)
    (x : Point D) (i : Fin n) (a : ℝ) (ha : 0≤a) :
    PrivateCompletedRms.childPayment S e r hr hF hell hlo hup x i a≤(3/2:ℝ)*a*B x := by
  have ht := S.mesh.location_mem_interval m (e i)
  have hb := square_budget_le data x hr1 hellsmall (show S.mesh.location m (e i)∈Icc 0 (samplingEnd S.τ) from ⟨ht.1.le,ht.2.le⟩)
  change PrivateBenchmarkMoments.squareBudget data x (S.mesh.location m (e i))≤((3/2:ℝ)*B x)^2 at hb
  unfold PrivateCompletedRms.childPayment
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity [Gibbs.primitiveScale_nonneg F x],?_⟩
  exact (mul_le_mul_of_nonneg_left hb (sq_nonneg a)).trans_eq (by ring)

theorem initializer_budget_le (hr1 : r≤1) (hellsmall : ell≤1/100) (x : Point D) :
    PrivateCompletedRms.initializerBudget S r hr hF hell hlo hup x≤2*r*B x := by
  have hb := reply_budget_le_twice data x hr1 hellsmall
  change PrivateSamplingOriginalBounds.replyBudget data x≤2*B x at hb
  have hbn := PrivateSamplingOriginalBounds.replyBudget_nonneg data x
  have he : (samplingEnd S.τ)^2≤1 := by nlinarith [S.samplingEnd_pos,S.samplingEnd_lt_one]
  have hrad : r^2≤r := by nlinarith
  unfold PrivateCompletedRms.initializerBudget
  calc
    _ ≤ r^2*1*(2*B x) := by gcongr
    _ ≤ _ := by nlinarith [Gibbs.primitiveScale_nonneg F x]
end ScalarMoments

/-- The actual weighted child budget uses maximum row mass, with no RMS
maximum or independence of benchmark nodes. -/
theorem child_row_budget_le {n : ℕ} (A : Fin n → Fin n → ℝ) (ε : ℕ → Fin n → ℝ)
    (a E : ℝ) (ha : 0≤a) (hE : 0≤E) (hrow : ∀ i, ∑ j, |A i j|≤a)
    (k : ℕ) (hε0 : ∀ i, 0≤ε k i) (hε : ∀ i, ε k i≤E) : SharedLayerRms.childRowBudget A ε k≤a*E := by
  unfold SharedLayerRms.childRowBudget
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg ha hE)).2
  intro i
  rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hε0 j))]
  calc
    _ ≤ ∑ j, |A i j| * E := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hε j) (abs_nonneg _)
    _ = (∑ j, |A i j|)*E := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) hE


section WidthPayment
variable {m n : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r Ds : ℝ)
  (hm : 0<m) (hr : 0<r) (hDs : 0<Ds)

include e hm hr hDs in
/-- The literal main width pays the maximum row mass, including the actual
finite inventory factor. -/
theorem main_width_row_le :
    r^2*RecursiveMeanPublicTable.mainWidth n r S.R Ds (r^2)≤SourceExecutableTables.samplingNoise S r Ds/2 := by
  have hn := RecursiveExecutableDomain.sampling_inventory_pos S e hm
  have hnR : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hs : 1≤Real.sqrt (n:ℝ) := Real.le_sqrt_of_sq_le (by simpa using hnR)
  have hs0 : 0<Real.sqrt (n:ℝ) := by linarith
  have hρ := (RecursiveExecutableDomain.sampling_noise_pos S r Ds hr hDs).le
  have he : r^2*RecursiveMeanPublicTable.mainWidth n r S.R Ds (r^2) =
      SourceExecutableTables.samplingNoise S r Ds/(2*Real.sqrt (n:ℝ)) := by
    unfold RecursiveMeanPublicTable.mainWidth CovarianceSetup.sigma SourceExecutableTables.samplingNoise
    field_simp [hr.ne',hs0.ne']
  rw [he]
  exact div_le_div_of_nonneg_left hρ (by norm_num) (by linarith)
end WidthPayment

/-- A purely scalar final absorption; all inputs are ordinary source sizes,
not program-error or coupling assertions. -/
theorem scalar_private_absorption {ell r τ δ rho : ℝ}
    (hell : 0≤ell) (hr : 0≤r) (hτ : 0≤τ) (hδ : 0≤δ) (hδ100 : δ≤1/100)
    (hl : ell*r^2≤δ) (hτδ : δ≤τ/10) (hρ : rho≤r*τ/2) :
    4*(ell*r^2)*δ^2+(20/9:ℝ)*(ell*r^2)*δ+(20/3:ℝ)*ell*r*rho+
      (9/4:ℝ)*τ+(ell*r^2)*δ ≤ 3*τ := by
  have hδ1 : δ≤1 := by linarith
  have hsq : δ^2≤τ/1000 := by
    have h := mul_le_mul hδ100 hτδ hδ (by norm_num : (0:ℝ)≤1/100)
    nlinarith
  have hlδ := mul_le_mul_of_nonneg_right hl hδ
  have hlδ2 : (ell*r^2)*δ^2≤δ^2 := by
    have hl1 : ell*r^2≤1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hl1 (sq_nonneg δ)]
  have hρ1 := mul_le_mul_of_nonneg_left hρ (mul_nonneg hell hr)
  have hρ2 := mul_le_mul_of_nonneg_right hl hτ
  have hδτ := mul_le_mul_of_nonneg_right hδ100 hτ
  nlinarith

def twiceNonneg (ell : ℝ) (hell : 0≤ell) : NNReal := ⟨2*ell,mul_nonneg (by norm_num) hell⟩

section SourcePayment
variable (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : threshold P≤P.y)
local notation "baseHy" => base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "S" => PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos hR P.h0_pos
variable {D n : ℕ} (e : Fin n ≃ (PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos
    (CubicSchedulePayments.radius_guard P hK hc hsmall hC
      (base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos).Node)
  {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v, 0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (r : ℝ) (hr : 0<r) (hr1 : r≤1) (hellδ : ell≤P.delta)
  (x : Point D) (α : ℝ) (hα : α≤(P.K:ℝ))
local notation "B" => Gibbs.primitiveScale F x
local notation "powα" => P.delta^α
local notation "sigmaM" => RecursiveMeanPublicTable.mainWidth n r (S).R P.Ds (r^2)
local notation "sigmaF" => SourceExecutableTables.samplingFinalWidth S r
local notation "rho" => SourceExecutableTables.samplingNoise S r P.Ds
local notation "kappa" => twiceNonneg ell hell
local notation "mainAmp" => (fun (_k : ℕ) (_i : Fin n) => 4*sigmaM*powα)
local notation "finalAmp" => (fun (_i : Fin n) => 4*sigmaF*powα)

include hr1 hellδ in
/-- The exact main finite recurrence appearing in the retained-kernel bound. -/
theorem source_main_budget_le :
    PrivateCompletedRms.mainBudget S e r P.NP hr hF hell hlo hup x kappa mainAmp ≤
      (2*r*B)*P.delta^((P.K:ℝ)+2) +
        (10/9:ℝ)*(r*B*P.delta^((P.K:ℝ)+1)+3*rho*powα*B) := by
  have hm : 0<P.m := by have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch); omega
  have hδ100 := delta_le_hundredth P hK hc (by linarith) (by linarith) hy
  have hδ := P.delta_pos
  have hpowα : 0≤powα := (Real.rpow_pos_of_pos hδ _).le
  have hB := Gibbs.primitiveScale_nonneg F x
  have hellsmall : ell≤1/100 := hellδ.trans hδ100
  have hl : ell*r^2≤P.delta := by
    have hr2 : r^2≤1 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hr2 hell).trans (by simpa using hellδ)
  have hχ0 : 0≤2*ell*r^2 := by positivity
  have hχδ : 2*ell*r^2≤2*P.delta := by linarith
  have hχ : 2*ell*r^2≤1/10 := by linarith
  have hinit := initializer_budget_le S r hr hF hell hlo hup hr1 hellsmall x
  have hres0 := source_residual_budget P hF hell hlo hup r hr hK hc hsmall hC hy
  have hdim : Real.sqrt (D:ℝ)≤B := by
    unfold Gibbs.primitiveScale
    simp only [finrank_euclideanSpace_fin]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hres : PrivateCompletedRms.residualBudget S r hr hF hell hlo hup≤r*B*P.delta^((P.K:ℝ)+1) := by
    apply hres0.trans
    have hcoef : ell*r^3≤r := by nlinarith [mul_le_mul_of_nonneg_right hl hr.le]
    gcongr
  have hσ := (RecursiveExecutableDomain.sampling_main_width_pos S e r P.Ds hm hr P.Ds_pos).le
  have hρ := (RecursiveExecutableDomain.sampling_noise_pos S r P.Ds hr P.Ds_pos).le
  have hσrow := main_width_row_le S e r P.Ds hm hr P.Ds_pos
  let ε := SourceMeanExecutionRms.finiteBudget P.NP
    (fun (_k : ℕ) (i : Fin n) => PrivateCompletedRms.childPayment S e r hr hF hell hlo hup x i (4*sigmaM*powα))
  have he0 (k : ℕ) (i : Fin n) : 0≤ε k i := by
    unfold ε SourceMeanExecutionRms.finiteBudget
    split_ifs <;> first | exact Real.sqrt_nonneg _ | exact le_rfl
  have heB (k : ℕ) (i : Fin n) : ε k i≤6*sigmaM*powα*B := by
    unfold ε SourceMeanExecutionRms.finiteBudget
    split_ifs
    · exact (child_payment_le S e r hr hF hell hlo hup hr1 hellsmall x i _ (by positivity)).trans_eq (by ring)
    · positivity
  have hrow (k : ℕ) : SharedLayerRms.childRowBudget (SourceExecutableTables.samplingMatrix S e r) ε k≤3*rho*powα*B := by
    have h := child_row_budget_le (SourceExecutableTables.samplingMatrix S e r) ε (r^2) (6*sigmaM*powα*B)
      (sq_nonneg _) (by positivity) (FixedTapeSampling.sampling_matrix_mass_le S e r hm hr.le) k (he0 k) (heB k)
    apply h.trans
    nlinarith [mul_le_mul_of_nonneg_right hσrow (mul_nonneg hpowα hB)]
  have hforcing := finite_forcing_le P.NP hχ0 hχ (show 0≤r*B*P.delta^((P.K:ℝ)+1)+3*rho*powα*B by positivity)
    (fun k => PrivateCompletedRms.residualBudget S r hr hF hell hlo hup+
      SharedLayerRms.childRowBudget (SourceExecutableTables.samplingMatrix S e r) ε k)
    (fun k _ => add_le_add hres (hrow k))
  have htrans := transient_power P hC hδ100 hχ0 hχδ
  unfold PrivateCompletedRms.mainBudget
  change (2*ell*r^2)^P.NP*PrivateCompletedRms.initializerBudget S r hr hF hell hlo hup x+_≤_
  have hp : (2*ell*r^2)^P.NP*PrivateCompletedRms.initializerBudget S r hr hF hell hlo hup x ≤
      P.delta^((P.K:ℝ)+2)*(2*r*B) :=
    mul_le_mul htrans hinit (by
      unfold PrivateCompletedRms.initializerBudget
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (PrivateSamplingOriginalBounds.replyBudget_nonneg _ _)) (by positivity)
  exact add_le_add (hp.trans_eq (by ring)) hforcing

include hr1 hellδ hα in
/-- The exact constant-four LOWER payment in the constructed retained bound
is at most the private constant-three target, at every source precision alpha
(in particular alpha=q-1/4). No target accuracy or numerical defect is assumed. -/
theorem source_retained_payment_le :
    (r*((kappa:ℝ)*PrivateCompletedRms.mainBudget S e r P.NP hr hF hell hlo hup x kappa mainAmp) +
      ∑ i, |SourceExecutableTables.samplingFinalWeight S e r i| *
        PrivateCompletedRms.childPayment S e r hr hF hell hlo hup x i (finalAmp i)) +
      PrivateCompletedRms.quadratureBudget S r hr hF hell hlo hup ≤
        3*(S).τ*powα*B := by
  have hm : 0<P.m := by have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch); omega
  have hδ100 := delta_le_hundredth P hK hc (by linarith) (by linarith) hy
  have hp := CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy
  have hδ1 := P.delta_le_one hp.1
  have hδ0 := P.delta_pos
  have hpowα : 0≤powα := (Real.rpow_pos_of_pos hδ0 _).le
  have hB := Gibbs.primitiveScale_nonneg F x
  have hellsmall : ell≤1/100 := hellδ.trans hδ100
  have hr2 : r^2≤1 := by nlinarith
  have hl : ell*r^2≤P.delta := (mul_le_mul_of_nonneg_left hr2 hell).trans (by simpa using hellδ)
  have hτ0 : 0≤(S).τ := (S).R_pos.le.trans (S).R_le_τ
  have hsqrtR : Real.sqrt P.delta≤P.R := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by have := P.t_le hc hsmall; linarith)
  have hδsqrt : P.delta≤Real.sqrt P.delta/10 := by
    have hsq := Real.sq_sqrt hδ0.le
    have hn := Real.sqrt_nonneg P.delta
    have hmul := mul_le_mul_of_nonneg_right hδ100 hδ0.le
    nlinarith
  have hτδ : P.delta≤(S).τ/10 := by
    have hτR : P.R≤(S).τ := (S).R_le_τ
    linarith
  have hDs : 1≤P.Ds := by
    have hR1 : P.R≤1 := (hR).trans (by norm_num)
    have h := mul_le_mul_of_nonneg_right hR1 P.Ds_pos.le
    rw [P.R_mul_Ds] at h
    simpa only [one_mul] using h
  have hρ : rho≤r*(S).τ/2 := by
    have hs5 : 1≤Real.sqrt 5 := Real.le_sqrt_of_sq_le (by norm_num)
    have hden : 2≤2*Real.sqrt 5*P.Ds := by nlinarith [mul_le_mul hs5 hDs (by norm_num : (0:ℝ)≤1) (Real.sqrt_nonneg _)]
    calc
      rho ≤ r*(S).R/2 := div_le_div_of_nonneg_left (by positivity [(S).R_pos]) (by norm_num) hden
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (S).R_le_τ hr.le) (by norm_num)
  have hpow1 : P.delta^((P.K:ℝ)+1)≤powα*P.delta := by
    calc
      _ ≤ P.delta^(α+1) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
      _ = _ := by rw [Real.rpow_add hδ0,Real.rpow_one]
  have hpow2 : P.delta^((P.K:ℝ)+2)≤powα*P.delta^2 := by
    calc
      _ ≤ P.delta^(α+2) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
      _ = _ := by rw [Real.rpow_add hδ0,Real.rpow_two]
  have hmain := source_main_budget_le P hK hc hsmall hC hy e hF hell hlo hup r hr hr1 hellδ x α
  have hmain' : r*((kappa:ℝ)*PrivateCompletedRms.mainBudget S e r P.NP hr hF hell hlo hup x kappa mainAmp) ≤
      (4*(ell*r^2)*P.delta^2+(20/9:ℝ)*(ell*r^2)*P.delta+(20/3:ℝ)*ell*r*rho)*powα*B := by
    change r*(2*ell*_)≤_
    calc
      _ ≤ r*(2*ell*((2*r*B)*P.delta^((P.K:ℝ)+2)+
          (10/9:ℝ)*(r*B*P.delta^((P.K:ℝ)+1)+3*rho*powα*B))) := by gcongr
      _ ≤ r*(2*ell*((2*r*B)*(powα*P.delta^2)+
          (10/9:ℝ)*(r*B*(powα*P.delta)+3*rho*powα*B))) := by gcongr
      _ = _ := by ring
  have hσF : 0≤sigmaF := (RecursiveExecutableDomain.sampling_final_width_pos S r hr).le
  have hfinal : (∑ i, |SourceExecutableTables.samplingFinalWeight S e r i| *
      PrivateCompletedRms.childPayment S e r hr hF hell hlo hup x i (finalAmp i)) ≤ (9/4:ℝ)*(S).τ*powα*B := by
    have hcoeff : r*(6*sigmaF)≤(9/4:ℝ)*(S).τ := by
      have hs2 : (4/3:ℝ)≤Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
      have hs0 : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have he : r*(6*sigmaF)=3*(S).τ/Real.sqrt 2 := by
        unfold SourceExecutableTables.samplingFinalWidth
        field_simp [hr.ne']
        ring
      rw [he]
      apply (div_le_iff₀ hs0).2
      nlinarith only [mul_le_mul_of_nonneg_left hs2 hτ0]
    calc
      _ ≤ ∑ i, |SourceExecutableTables.samplingFinalWeight S e r i| * (6*sigmaF*powα*B) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (child_payment_le S e r hr hF hell hlo hup hr1 hellsmall x i _ (by positivity)).trans_eq (by ring)
      _ = r*(6*sigmaF*powα*B) := by
        rw [← Finset.sum_mul,FixedTapeSampling.sampling_final_mass S e r hm hr.le]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hpowα hB)]
  have hquad := source_quadrature_budget P hF hell hlo hup r hr hK hc hsmall hC hy
  have hdim : Real.sqrt (D:ℝ)≤B := by
    unfold Gibbs.primitiveScale
    simp only [finrank_euclideanSpace_fin]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hquad' : PrivateCompletedRms.quadratureBudget S r hr hF hell hlo hup≤
      ((ell*r^2)*P.delta)*powα*B := by
    calc
      _ ≤ (ell*r^2)*B*(powα*P.delta) := by apply hquad.trans; gcongr
      _ = _ := by ring
  have hscalar := scalar_private_absorption hell hr.le hτ0 hδ0.le hδ100 hl hτδ hρ
  calc
    _ ≤ (4*(ell*r^2)*P.delta^2+(20/9:ℝ)*(ell*r^2)*P.delta+(20/3:ℝ)*ell*r*rho)*powα*B +
        (9/4:ℝ)*(S).τ*powα*B+((ell*r^2)*P.delta)*powα*B :=
      add_le_add (add_le_add hmain' hfinal) hquad'
    _ = (4*(ell*r^2)*P.delta^2+(20/9:ℝ)*(ell*r^2)*P.delta+(20/3:ℝ)*ell*r*rho+
        (9/4:ℝ)*(S).τ+(ell*r^2)*P.delta)*powα*B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscalar hpowα) hB

end SourcePayment

end AcceleratedLogConcave.Oracle.PrivateSourceScalarAbsorption
