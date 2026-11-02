import AcceleratedLogConcave.Root.CoolingPrescribedPayments
import AcceleratedLogConcave.Oracle.PrescribedTerminalAccuracy

/-! Actual public cooling inventory and physical root guards. The public
variance is bounded by 2 delta²; no child accuracy is assumed. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped NNReal
namespace AcceleratedLogConcave.Root.CoolingSourceRootGuards
open Oracle Numerics Numerics.AffineGraph RecursiveSize RecursiveCall
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "S" => CoolingPrescribedPayments.geometry P hR
local notation "nc" => Fintype.card ((CoolingPrescribedPayments.mesh P).Source P.m)

include hK hc hsmall hC hy

/-- The literal public tau=1 node count, with the same proved source envelope. -/
theorem dimension : Real.sqrt (nc:ℝ)≤P.Bsize*P.delta^(-P.w) := by
  have hp := CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy
  have hm := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  have hhalf := (ScalarSchedulePayment.geometry_caps P hc hsmall (by linarith) hp.1 hp.2.2).2.2.2
  have hn := PrescribedMeshDimensions.sampling_card_le_common S hm P.h0 P.h0_pos hhalf rfl
  have hX : 0≤PrescribedMeshCardinality.meshBudget P.R P.h0 := by
    unfold PrescribedMeshCardinality.meshBudget; positivity [P.h0_pos]
  have hs := PrescribedMeshDimensions.sqrt_card_le hX hn
  apply hs.trans
  change Real.sqrt 1280*(P.m:ℝ)^2*PrescribedMeshCardinality.meshBudget P.R P.h0≤_
  rw [PrescribedMeshCardinality.meshBudget, P.Bsize_eq_log hc hp.1]
  change Real.sqrt 1280*(P.m:ℝ)^2*((1+|Real.log (P.delta^P.t)|)/P.delta^P.w)≤_
  rw [Real.rpow_neg P.delta_pos.le]
  exact le_of_eq (by ring)

/-- The exact public-main width coefficient is paid at the physical radius
scale r²≤2 delta, from the existing cubic source threshold. -/
theorem coefficient_payment :
    8*Real.sqrt 5*P.Bsize*P.delta^(1-2*P.t-P.w)≤1 := by
  have hp := CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC baseHy
  have hB := P.Bsize_ge_one hc hsmall (by linarith : 1≤P.Csch) hp.1
  have hstep : 1≤RecursiveSize.stepFactor P.m P.Bsize := (by norm_num : (1:ℝ)≤3).trans
    (RecursiveSize.stepFactor_ge_three P.m P.Bsize (by linarith))
  have hrank : 1≤ScalarSchedulePayment.rho P := by
    exact (Precision.precisionRank_pos_iff (P.t_pos hc)).2 (CubicSchedulePayments.shift_precision P hK)
  have hpow := pow_le_pow_right₀ hstep hrank
  simp only [pow_one] at hpow
  have hmain := RecursiveSize.stepFactor_ge_main P.m P.Bsize hB
  have hm : (1:ℝ)≤P.m := by exact_mod_cast (show 1≤P.m by have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch); omega)
  have hcoef : 8*Real.sqrt 5*P.Bsize≤ScalarSchedulePayment.Q P := by
    have hh : 2*RecursiveSize.mainFactor P.Bsize≤2*(ScalarSchedulePayment.step P)^(ScalarSchedulePayment.rho P) :=
      mul_le_mul_of_nonneg_left (hmain.trans hpow) (by norm_num)
    have hh2 := mul_le_mul_of_nonneg_right (show (2:ℝ)≤520*(P.m:ℝ)^5 by nlinarith [one_le_pow₀ hm (n:=5)])
      (pow_nonneg (by linarith : 0≤RecursiveSize.stepFactor P.m P.Bsize) (ScalarSchedulePayment.rho P))
    exact (show _≤2*(ScalarSchedulePayment.step P)^(ScalarSchedulePayment.rho P) by dsimp [RecursiveSize.mainFactor] at hh; nlinarith only [hh]).trans hh2
  have hQ := ScalarSchedulePayment.Q_pos P hc hsmall (by linarith) hp.1
  have hres := rpow_resolution_mul_le_one P.delta_pos hQ hs.2.2.2.2.1
  have hexp : (1:ℝ)/12≤1-2*P.t-P.w := by
    have ht := P.t_le hc hsmall
    have hw := P.w_lt_t hc (by linarith : 1≤P.Csch)
    linarith
  have hpower := Real.rpow_le_rpow_of_exponent_ge P.delta_pos (P.delta_le_one hp.1) hexp
  exact (mul_le_mul hcoef hpower (Real.rpow_nonneg P.delta_pos.le _) hQ.le).trans hres


/-- Public main calls satisfy the actual mean-root ratio cap at every node. -/
theorem main_ratio {ell r : ℝ} (hell : 0≤ell) (hellδ : ell≤P.delta)
    (hr : 0<r) (hrsq : r^2≤2*P.delta) (i : (S).Node) :
    ell*((S).radius r i / RecursiveMeanPublicTable.mainWidth nc r P.R P.Ds (r^2))≤P.delta := by
  let e := CoolingPrescribedPayments.nodes P
  have hm : 0<P.m := by have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch); omega
  have hw := RecursiveExecutableDomain.sampling_main_width_pos S e r P.Ds hm hr P.Ds_pos
  have hn := RecursiveExecutableDomain.sampling_inventory_pos S e hm
  have hsqrt : Real.sqrt (nc:ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  have hratio : r / RecursiveMeanPublicTable.mainWidth nc r P.R P.Ds (r^2) =
      (4*Real.sqrt 5*P.Ds*Real.sqrt (nc:ℝ)/P.R)*r^2 := by
    unfold RecursiveMeanPublicTable.mainWidth CovarianceSetup.sigma RecursiveMeanPublicTable.centerNoise
    field_simp [hr.ne', P.R_pos.ne', P.Ds_pos.ne', hsqrt]
    ring
  have hcoeff := RecursiveSize.main_coefficient_le P.delta P.t P.w P.R P.Ds P.Bsize nc
    P.delta_pos rfl le_rfl (dimension P hK hc hsmall hC hy)
  have hco0 : 0≤4*Real.sqrt 5*P.Ds*Real.sqrt (nc:ℝ)/P.R := by positivity [P.Ds_pos,P.R_pos]
  calc
    _ ≤ ell*(r/RecursiveMeanPublicTable.mainWidth nc r P.R P.Ds (r^2)) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ((S).radius_le r hr.le i) hw.le) hell
    _ = ell*((4*Real.sqrt 5*P.Ds*Real.sqrt (nc:ℝ)/P.R)*r^2) := by rw [hratio]
    _ ≤ P.delta*((RecursiveSize.mainFactor P.Bsize*P.delta^(-2*P.t-P.w))*(2*P.delta)) := by
      apply mul_le_mul hellδ _ (mul_nonneg hco0 (sq_nonneg _)) P.delta_pos.le
      apply mul_le_mul hcoeff hrsq (sq_nonneg _)
      have hB := P.Bsize_ge_one hc hsmall (by linarith : 1≤P.Csch) (CubicSchedulePayments.prerequisites P hK hc hsmall hC baseHy).1
      have hB0 : 0≤P.Bsize := by linarith
      unfold RecursiveSize.mainFactor
      positivity [P.delta_pos]

    _ = P.delta*(8*Real.sqrt 5*P.Bsize*P.delta^(1-2*P.t-P.w)) := by
      rw [show 1-2*P.t-P.w=(-2*P.t-P.w)+1 by ring, Real.rpow_add P.delta_pos,Real.rpow_one]
      unfold RecursiveSize.mainFactor
      ring
    _ ≤ P.delta*1 := mul_le_mul_of_nonneg_left (coefficient_payment P hK hc hsmall hC hy) P.delta_pos.le
    _ = P.delta := mul_one _


/-- Paid-final public widths satisfy the same root ratio without a node count. -/
theorem final_ratio {ell r : ℝ} (hell : 0≤ell) (hellδ : ell≤P.delta)
    (hr : 0<r) (hrsq : r^2≤2*P.delta) (i : (S).Node) :
    ell*((S).radius r i / SourceExecutableTables.samplingFinalWidth S r)≤P.delta := by
  have hw := RecursiveExecutableDomain.sampling_final_width_pos S r hr
  have hratio : r / SourceExecutableTables.samplingFinalWidth S r = 2*Real.sqrt 2*r^2 := by
    unfold SourceExecutableTables.samplingFinalWidth
    change r/(1/Real.sqrt 2/(2*r))=_
    field_simp
  have hd := PrivateSourceScalarAbsorption.delta_le_hundredth P hK hc (by linarith) (by linarith) hy
  have hsq : Real.sqrt 2≤2 := (Real.sqrt_le_iff).2 ⟨by norm_num,by norm_num⟩
  calc
    _ ≤ ell*(r/SourceExecutableTables.samplingFinalWidth S r) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ((S).radius_le r hr.le i) hw.le) hell
    _ = ell*(2*Real.sqrt 2*r^2) := by rw [hratio]
    _ ≤ P.delta*(2*2*(2*P.delta)) := by gcongr; exact P.delta_pos.le
    _ ≤ P.delta := by nlinarith [mul_le_mul_of_nonneg_right hd P.delta_pos.le]

/-- Both original mean-root radius guards hold at every actual public node. -/
theorem radius_guards {ell r : ℝ} (hell : 0≤ell) (hellδ : ell≤P.delta)
    (hr : 0<r) (hrsq : r^2≤2*P.delta) (i : (S).Node) :
    0<(S).radius r i ∧ (S).radius r i≤1 ∧ ell*((S).radius r i)^2≤P.delta := by
  have hd := PrivateSourceScalarAbsorption.delta_le_hundredth P hK hc (by linarith) (by linarith) hy
  have hri := (S).radius_pos r hr i
  have hle := (S).radius_le r hr.le i
  have hs : ((S).radius r i)^2≤r^2 := by nlinarith
  have hcurv : ell*((S).radius r i)^2≤P.delta*(2*P.delta) :=
    mul_le_mul hellδ (hs.trans hrsq) (sq_nonneg _) P.delta_pos.le
  exact ⟨hri,by nlinarith,by nlinarith [mul_le_mul_of_nonneg_right hd P.delta_pos.le]⟩

omit hK hc hsmall hC hy in
/-- Actual physical cooling variances, including the largest dyadic level,
provide the radius premise used above. -/
theorem physical_radius_sq {v : ℝ≥0} (hv : (v:ℝ)≤2*P.delta^2) :
    (CoolingExecutable.radius P.delta v)^2≤2*P.delta := by
  unfold CoolingExecutable.radius
  rw [Real.sq_sqrt (div_nonneg v.coe_nonneg P.delta_pos.le)]
  exact (div_le_iff₀ P.delta_pos).2 (by nlinarith)
end AcceleratedLogConcave.Root.CoolingSourceRootGuards
