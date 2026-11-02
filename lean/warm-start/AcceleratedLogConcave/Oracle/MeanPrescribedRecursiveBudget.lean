import AcceleratedLogConcave.Oracle.MeanSourceRecursiveBudget
import AcceleratedLogConcave.Oracle.MeanPrescribedRecursiveGuards
import AcceleratedLogConcave.Oracle.MeanRecursiveChronologicalCoupling

/-! Actual reachable source calls discharge the complete scalar mean
recurrence. Lower amplitudes, the private anchor payment and all original
analytic budgets are fixed in source units; no parent accuracy is assumed. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanPrescribedRecursiveBudget
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall ScalarSchedulePayment

variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "privateHy" => MeanSourceScalarAbsorption.private_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) privateHy

include hK hc hsmall hC hy in
theorem radiusGuard : P.R≤1/2 := CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy

variable {D : ℕ} {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (x : Point D) {r0 σ0 : ℝ} (hr0 : 0<r0) (hr1 : r0≤1) (hσ0 : 0<σ0)
  (hellδ : ell≤P.delta) (hrootRatio : ell*(r0/σ0)≤P.delta)
local notation "hR" => radiusGuard P hK hc hsmall hC hy
local notation "C" => source P hR

include hell hr0 hr1 hellδ in
theorem root_radius : ell*r0^2≤P.delta := by
  have hs : r0^2≤1 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hs hell).trans (by simpa using hellδ)

variable {p : State} {depth cost : ℕ}

include hrootRatio in
/-- Every scalar in the actual finite source output recurrence is paid by
the original root and actual call path. The closed private anchor bound is
3R delta^(q-1/4) D_F(x), supplied by the lower private execution theorem. -/
theorem source_budget_le
    (hp : Path (source P (radiusGuard P hK hc hsmall hC hy))
      (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    let hroot := root_radius P hell hr0 hr1 hellδ
    let d := PrescribedMeanNumericalData.reachableDatum P hF hell hlo hup x hK hc hsmall hC privateHy hr0 hσ0 hroot hp
    let κ := PrivateSourceScalarAbsorption.twiceNonneg ell hell
    let aRow := SourceMeanExecutable.rowBound (m := P.m) p.radius p.width P.delta P.t P.w
    let sigmaM := CovarianceSetup.sigma (n P hR) (RecursiveMeanPublicTable.centerNoise p.radius P.R P.Ds) aRow
    let ε := fun (_ : ℕ) (_ : Fin (n P hR)) => 256*sigmaM*P.delta^(p.precision-1/4)*Gibbs.primitiveScale F x
    let Eprivate := 3*P.R*P.delta^(p.precision-1/4)*Gibbs.primitiveScale F x
    (∑ i : Fin P.m,|GaussLegendre.weight P.m i|)*((κ:ℝ)*MeanSourceSharpRms.sourceMainBudget d (C).nodes P.h0 P.NP κ aRow Eprivate ε)+
      (∑ i : Fin P.m,|GaussLegendre.weight P.m i| *
        (4*RecursiveMeanPublicTable.finalWidth P.R p.width*P.delta^(p.precision-P.t)*
          Real.sqrt (MeanBenchmarkMoments.finalScaleSquareBudget d)))+
      MeanOriginalBounds.quadratureBudget d≤4*p.width*P.delta^p.precision*Gibbs.primitiveScale F x := by
  dsimp only
  let hroot := root_radius P hell hr0 hr1 hellδ
  let d := PrescribedMeanNumericalData.reachableDatum P hF hell hlo hup x hK hc hsmall hC privateHy hr0 hσ0 hroot hp
  let B := Gibbs.primitiveScale F x
  have hB : 0≤B := Gibbs.primitiveScale_nonneg _ _
  have hm2 := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  have hm : 0<P.m := by omega
  have hpos := hp.positive hm P.Ds_pos P.delta_pos hr0 hσ0
  have hd := P.delta_le_one (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
  have hd100 := PrivateSourceScalarAbsorption.delta_le_hundredth P hK hc (by linarith : P.csch≤1)
    (by linarith : 1≤P.Csch) privateHy
  have hrp := PrescribedTerminalAccuracy.radius_le_root hp hm P.Ds_pos P.delta_pos hr0 hσ0
  change p.radius≤r0 at hrp
  have hrp1 : p.radius≤1 := hrp.trans hr1
  have hslope : ell*p.radius≤1/8 := by
    have h := mul_le_mul_of_nonneg_left hrp1 hell
    nlinarith
  have hratio := MeanPrescribedRecursiveGuards.reachable_ratio P hK hc hsmall hC privateHy
    hell hr0 hσ0 hroot hrootRatio hp
  have hscale : ell*p.radius/p.width≤1 := by
    have h : ell*p.radius/p.width≤P.delta^((1:ℝ)/4)/4096 :=
      (div_le_iff₀ hpos.2).mpr (hratio.trans_eq (by ring))
    have hpq : P.delta^((1:ℝ)/4)≤1 := Real.rpow_le_one P.delta_pos.le hd (by norm_num)
    nlinarith
  have hpsi : (d).G.psi≤1 := by
    change P.R^4≤1
    exact pow_le_one₀ P.R_pos.le ((hR).trans (by norm_num))
  have hDs : 1≤P.Ds := by
    have h := mul_le_mul_of_nonneg_right ((hR).trans (by norm_num) : P.R≤1) P.Ds_pos.le
    rw [P.R_mul_Ds] at h
    simpa only [one_mul] using h
  have hq : p.precision≤(P.K:ℝ) := by
    have he := hp.precision_eq
    change p.precision=(P.K:ℝ)-(cost:ℝ)/4-((depth-cost:ℕ):ℝ)*P.t at he
    have hcost : 0≤(cost:ℝ) := Nat.cast_nonneg _
    have hprod : 0≤((depth-cost:ℕ):ℝ)*P.t := mul_nonneg (Nat.cast_nonneg _) (P.t_pos hc).le
    linarith
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC baseHy
  have hpsieq : (C).M.psi=P.delta^(4*P.t) := P.psi_eq_R_pow.symm
  have hrow := MeanRecursiveChronologicalCoupling.actual_rows (C).M (C).nodes (C).mesh (C).snodes
    P.Ds P.delta P.t P.w P.NP (P.t_pos hc) p.radius p.width hpos.1 hpos.2 P.delta_pos
    hm2 hd hpsieq hs.2.2.2.2.2.1.2.2.2 rfl
  obtain ⟨_,hhalf,htrans⟩ := MeanPrescribedRecursiveGuards.reachable_transient P hK hc hsmall hC privateHy
    hell hr0 hσ0 hroot hrootRatio hF hlo hup x hp
  change 2*MeanCollocationLp.contraction d P.h0≤1/2 at hhalf
  change (2*MeanCollocationLp.contraction d P.h0)^P.NP≤P.delta^((P.K:ℝ)+2) at htrans
  unfold MeanCollocationLp.contraction at hhalf htrans
  dsimp only [d,PrescribedMeanNumericalData.reachableDatum] at hhalf htrans
  rw [PrescribedMeanNumericalData.rowMass_eq] at hhalf htrans
  have hdim : Real.sqrt (D:ℝ)≤B := by
    unfold B Gibbs.primitiveScale
    simp only [finrank_euclideanSpace_fin]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hres0 := MeanPrescribedOriginalPayments.reachable_residual_payment P hK hc hsmall hC hy hF hell hlo hup x
    hr0 hσ0 hroot hrootRatio hp
  have hres : MeanOriginalBounds.residualBudget d P.h0≤p.radius*B*P.delta^((P.K:ℝ)+1) := by
    apply hres0.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdim hpos.1.le) (Real.rpow_nonneg P.delta_pos.le _)
  have hquad0 := MeanPrescribedOriginalPayments.reachable_centering_payment P hK hc hsmall hC hy hF hell hlo hup x
    hr0 hσ0 hroot hrootRatio hp
  have hquad : MeanOriginalBounds.quadratureBudget d≤(ell*p.radius*B/2)*P.delta^((P.K:ℝ)+1) := by
    apply hquad0.trans
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdim (mul_nonneg hell hpos.1.le)) (by norm_num)) (Real.rpow_nonneg P.delta_pos.le _)
  have hE0 : 0≤3*P.R*P.delta^(p.precision-1/4)*B := by positivity [P.R_pos,P.delta_pos]
  have hE : 3*P.R*P.delta^(p.precision-1/4)*B≤3*P.delta^(p.precision-1/4)*B := by
    have h := mul_le_mul_of_nonneg_right ((hR).trans (by norm_num) : P.R≤1)
      (show 0≤3*P.delta^(p.precision-1/4)*B by positivity [P.delta_pos])
    nlinarith
  exact MeanSourceRecursiveBudget.source_budget_le d P (C).nodes hm hrp1 hslope hscale hpsi rfl hd hDs p.precision hq
    hrow (by simpa only [d,PrescribedMeanNumericalData.reachableDatum,PrescribedMeanNumericalData.datum,mul_assoc] using hhalf) (by simpa only [d,PrescribedMeanNumericalData.reachableDatum,PrescribedMeanNumericalData.datum,mul_assoc] using htrans) hratio _ hE0 hE hres hquad

end AcceleratedLogConcave.Oracle.MeanPrescribedRecursiveBudget
