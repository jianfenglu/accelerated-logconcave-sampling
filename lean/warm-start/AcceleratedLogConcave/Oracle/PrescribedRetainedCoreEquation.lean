import AcceleratedLogConcave.Oracle.PrescribedRetainedQuantitativeInduction

/-! Exact active recursion of the already constructed retained law. Each lower
package is the same reachable law on its actual source child path. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.PrescribedRetainedCoreEquation
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall
open RecursiveRetainedAccuracy PrescribedRetainedChildPaths
open PrescribedRetainedQuantitativeInduction
set_option maxHeartbeats 1200000
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
  {d : ℕ} (ell r0 σ0 : ℝ) (hell : 0≤ell) (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hrootRadius : ell*r0^2≤P.delta)
  {V : Point d → ℝ} (scale : ℝ) (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v≤ell*‖v‖^2)

local notation "hR" => PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy
local notation "C" => source P hR
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hF" => (show ContDiff ℝ 2 (scaledPotential V scale) from by unfold scaledPotential; fun_prop)
local notation "hG" => ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp (hV.continuous_fderiv (by norm_num))).measurable
local notation "hm2" => P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch)
local notation "hm" => (show 0<P.m from by have := hm2; omega)
local notation "hs" => CubicSchedulePayments.actual_scalar_payments P hK hc hcsmall hC baseHy
local notation "hy0" => (CubicSchedulePayments.prerequisites P hK hc hcsmall hC baseHy).1
local notation "hpsieq" => (show (C).M.psi=P.delta^(4*P.t) from P.psi_eq_R_pow.symm)
variable {p : State} {depth cost : ℕ}
  (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
    (PrescribedRecursiveStability.root P r0 σ0) p depth cost)
  (hq : 1/2<p.precision)
local notation "theta" => PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp

/-- The literal lower law on the corresponding reached source path. -/
def mainLaws (i : Fin (ScalarSchedulePayment.n P hR)) :=
  reachableLaw P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup
    (main_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i)

/-- The literal lower law on the corresponding reached source path. -/
def finalLaws (i : Fin P.m) :=
  reachableLaw P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup
    (final_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i)

/-- The literal lower law on the corresponding reached source path. -/
def privateMainLaws (i : Fin (ScalarSchedulePayment.ns P hR)) :=
  reachableLaw P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup
    (privateMain_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i)

/-- The literal lower law on the corresponding reached source path. -/
def privateFinalLaws (i : Fin (ScalarSchedulePayment.ns P hR)) :=
  reachableLaw P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup
    (privateFinal_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i)

/-- The existing source step, fed only the four exact recursively selected
lower packages. This alias introduces no alternative joint. -/
def activeStep :=
  RecursiveRetainedCoupling.step (C).M hm hF hell hlo hup P.t (P.t_pos hc)
    (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.w P.NP
    (step_quarter P hc hcsmall) scale (P.K:ℝ) P.Ds_pos P.delta_pos le_rfl
    (ScalarSchedulePayment.I P hR) P.Hs (by rfl)
    (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC)
    hs.2.2.2.1 theta p.precision
    (PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp)
    hm2 (P.delta_le_one hy0) hpsieq hs.2.2.2.2.2.1.2.2.2 rfl
    (gradient V) hG hq
    (mainLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq)
    (finalLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq)
    (privateMainLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq)
    (privateFinalLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq)

/-- Equality of complete law packages, including source and reference fields. -/
theorem active_eq_step :
  reachableLaw P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp =
    activeStep P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq := by
  unfold reachableLaw PrescribedRetainedCoupling.law activeStep
  rw [RecursiveRetainedCoupling.core.eq_def]
  simp only [dite_eq_right (not_le_of_gt hq)]
  rfl

end AcceleratedLogConcave.Oracle.PrescribedRetainedCoreEquation
