import AcceleratedLogConcave.Root.CoolingPrescribedPayments

/-! Public cooling scalar payment at tau=1. Every lower call keeps the true
public precision K. The actual finite private RMS recurrence is paid using
its proved generic moment/width lemmas and the public mesh's C2 quadrature
payments; no public sampler accuracy or retained law is assumed. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Root.CoolingSourceScalarPayments
open Oracle Numerics Numerics.AffineGraph PrivateSourceScalarAbsorption
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "S" => CoolingPrescribedPayments.geometry P hR
local notation "e" => CoolingPrescribedPayments.nodes P
local notation "nc" => Fintype.card ((CoolingPrescribedPayments.mesh P).Source P.m)
variable {D : ℕ} {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (r : ℝ) (hr : 0<r) (hr1 : r≤1) (hellδ : ell≤P.delta) (x : Point D)
local notation "B" => Gibbs.primitiveScale F x
local notation "powα" => P.delta^(P.K:ℝ)
local notation "sigmaM" => RecursiveMeanPublicTable.mainWidth nc r (S).R P.Ds (r^2)
local notation "sigmaF" => SourceExecutableTables.samplingFinalWidth S r
local notation "rho" => SourceExecutableTables.samplingNoise S r P.Ds
local notation "kappa" => twiceNonneg ell hell
local notation "mainAmp" => (fun (_k : ℕ) (_i : Fin nc) => 4*sigmaM*powα)
local notation "finalAmp" => (fun (_i : Fin nc) => 4*sigmaF*powα)

include hr1 hellδ in
/-- The exact main finite recurrence appearing in the retained-kernel bound. -/
theorem main_budget_le :
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
  have hres0 := CoolingPrescribedPayments.residual_payment P hK hc hsmall hC hy hF hell hlo hup r hr
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
    (fun (_k : ℕ) (i : Fin nc) => PrivateCompletedRms.childPayment S e r hr hF hell hlo hup x i (4*sigmaM*powα))
  have he0 (k : ℕ) (i : Fin nc) : 0≤ε k i := by
    unfold ε SourceMeanExecutionRms.finiteBudget
    split_ifs <;> first | exact Real.sqrt_nonneg _ | exact le_rfl
  have heB (k : ℕ) (i : Fin nc) : ε k i≤6*sigmaM*powα*B := by
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

include hr1 hellδ in
/-- Exact public constant-four lower payments at precision K fit inside
3 delta^K D_F(x), with the public tau=1 endpoint and complete finite RMS
recurrence. No current public accuracy or numerical defect is assumed. -/
theorem retained_payment_le :
    (r*((kappa:ℝ)*PrivateCompletedRms.mainBudget S e r P.NP hr hF hell hlo hup x kappa mainAmp) +
      ∑ i, |SourceExecutableTables.samplingFinalWeight S e r i| *
        PrivateCompletedRms.childPayment S e r hr hF hell hlo hup x i (finalAmp i)) +
      PrivateCompletedRms.quadratureBudget S r hr hF hell hlo hup ≤
        3*powα*B := by
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
      _ ≤ P.delta^((P.K:ℝ)+1) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
      _ = _ := by rw [Real.rpow_add hδ0,Real.rpow_one]
  have hpow2 : P.delta^((P.K:ℝ)+2)≤powα*P.delta^2 := by
    calc
      _ ≤ P.delta^((P.K:ℝ)+2) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
      _ = _ := by rw [Real.rpow_add hδ0,Real.rpow_two]
  have hmain := main_budget_le P hK hc hsmall hC hy hF hell hlo hup r hr hr1 hellδ x
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
  have hquad := CoolingPrescribedPayments.quadrature_payment P hK hc hsmall hC hy hF hell hlo hup r hr
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
    _ ≤ 3*(S).τ*powα*B := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscalar hpowα) hB
    _ = 3*powα*B := by change 3*1*powα*B=3*powα*B; ring

end AcceleratedLogConcave.Root.CoolingSourceScalarPayments
