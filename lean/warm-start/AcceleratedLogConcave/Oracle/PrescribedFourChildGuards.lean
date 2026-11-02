import AcceleratedLogConcave.Oracle.PrescribedRetainedChildPaths
import AcceleratedLogConcave.Oracle.PrescribedRecursiveStability

/-! Deterministic guards of the four literal lower families used by the
prescribed retained core. Original scaled-potential Hessian and root scalar
caps supply all fixed-tape stability; the actual support budget supplies
QueryShift and whole Gaussian shift mass, including terminal overshoots. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped NNReal
namespace AcceleratedLogConcave.Oracle.PrescribedFourChildGuards
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall FixedTapeStability
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy
local notation "C" => source P hR
local notation "e" => (C).nodes
local notation "a" => anchors P hR
local notation "z" => seeds P hR
local notation "s" => (C).snodes
variable {D : ℕ} (scale : ℝ) {V : Point D → ℝ} (hV : ContDiff ℝ 2 V)
  (ell : ℝ≥0)
  (hlo : ∀ x v,0≤fderiv ℝ (fderiv ℝ (scaledPotential V scale)) x v v)
  (hup : ∀ x v,fderiv ℝ (fderiv ℝ (scaledPotential V scale)) x v v≤(ell:ℝ)*‖v‖^2)
  (r0 σ0 : ℝ) (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hrootRadius : (ell:ℝ)*r0^2≤P.delta) (hrootRatio : (ell:ℝ)*(r0/σ0)≤P.delta)
  {p : State} {depth cost : ℕ}
  (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
    (PrescribedRecursiveStability.root P r0 σ0) p depth cost)
  (hq : 1/2<p.precision)

local notation "main" => MeanMainBatchCoupling.recursiveMain (C).M e a z (C).mesh s P.Ds P.delta P.t P.w P.NP
  (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.width p.precision
local notation "final" => MeanMainBatchCoupling.recursiveFinal (C).M e a z (C).mesh s P.Ds P.delta P.t P.w P.NP
  (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.width p.precision
local notation "privateMainP" => PrivateRecursiveBatchBudget.main (C).M e a z (C).mesh s P.Ds P.delta P.t P.w P.NP
  (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.precision
local notation "privateFinalP" => PrivateRecursiveBatchBudget.final (C).M e a z (C).mesh s P.Ds P.delta P.t P.w P.NP
  (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.precision

include hV hlo hup hr0 hσ0 hrootRadius hrootRatio hp hq in
/-- Actual mean-main calls use their own child width and q-1/4. All guards follow from the original source/root data. -/
theorem meanMain (i : Fin (ScalarSchedulePayment.n P hR)) :
    ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      ((C).M.radius p.radius (e i)) (main i).shiftVector ∧
    CovarianceSetup.shiftSq (main i).shiftVector≤P.Ds^2 ∧
    ChildStable (main i).program (main i).coefficient (gradient V) (2*(ell:ℝ)) := by
  have hm : 0<P.m := by have := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega
  have hpos := hp.positive hm P.Ds_pos P.delta_pos hr0 hσ0
  have hqK := PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp
  have hquery := CubicExecutableWorkShift.queryShift_and_mass P hK hc hcsmall hC baseHy scale
    ((C).M.radius p.radius (e i)) (RecursiveMeanPublicTable.mainWidth (ScalarSchedulePayment.n P hR) p.radius (C).M.R P.Ds (SourceMeanExecutable.rowBound (m := P.m) p.radius p.width P.delta P.t P.w)) (p.precision-1/4)
    ((C).M.radius_pos p.radius hpos.1 (e i)) (by linarith)
  have hnorm := PrescribedRecursiveStability.normalized_gradient scale ell hV hlo hup
  have hstab := PrescribedRecursiveStability.meanMain_childStable P hK hc hcsmall hC hy scale (gradient V) ell hnorm
    r0 σ0 hr0 hσ0 hrootRadius hrootRatio hp hq i
  exact ⟨hquery.1,hquery.2.2,hstab⟩

include hV hlo hup hr0 hσ0 hrootRadius hrootRatio hp hq in
/-- Actual paid-final calls use q-t and the distinct physical final width. All guards follow from the original source/root data. -/
theorem activeFinal (i : Fin P.m) :
    ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (p.radius*(C).M.R) (final i).shiftVector ∧
    CovarianceSetup.shiftSq (final i).shiftVector≤P.Ds^2 ∧
    ChildStable (final i).program (final i).coefficient (gradient V) (2*(ell:ℝ)) := by
  have hm : 0<P.m := by have := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega
  have hpos := hp.positive hm P.Ds_pos P.delta_pos hr0 hσ0
  have hqK := PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp
  have hquery := CubicExecutableWorkShift.queryShift_and_mass P hK hc hcsmall hC baseHy scale
    (p.radius*(C).M.R) (RecursiveMeanPublicTable.finalWidth (C).M.R p.width) (p.precision-P.t)
    (mul_pos hpos.1 (C).M.R_pos) (by have := P.t_pos hc; linarith)
  have hnorm := PrescribedRecursiveStability.normalized_gradient scale ell hV hlo hup
  have hstab := PrescribedRecursiveStability.activeFinal_childStable P hK hc hcsmall hC hy scale (gradient V) ell hnorm
    r0 σ0 hr0 hσ0 hrootRadius hrootRatio hp hq i
  exact ⟨hquery.1,hquery.2.2,hstab⟩

include hV hlo hup hr0 hσ0 hrootRadius hrootRatio hp hq in
/-- Actual private-main calls retain their literal q-1/4 precision and private width. All guards follow from the original source/root data. -/
theorem privateMain (i : Fin (ScalarSchedulePayment.ns P hR)) :
    ChildAbsorption.QueryShift (privateMainP i).program (privateMainP i).enumeration (privateMainP i).coefficient
      ((C).S.radius p.radius (s i)) (privateMainP i).shiftVector ∧
    CovarianceSetup.shiftSq (privateMainP i).shiftVector≤P.Ds^2 ∧
    ChildStable (privateMainP i).program (privateMainP i).coefficient (gradient V) (2*(ell:ℝ)) := by
  have hm : 0<P.m := by have := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega
  have hpos := hp.positive hm P.Ds_pos P.delta_pos hr0 hσ0
  have hqK := PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp
  have hquery := CubicExecutableWorkShift.queryShift_and_mass P hK hc hcsmall hC baseHy scale
    ((C).S.radius p.radius (s i)) (RecursiveMeanPublicTable.mainWidth (ScalarSchedulePayment.ns P hR) p.radius (C).M.R P.Ds (p.radius^2)) (p.precision-1/4)
    ((C).S.radius_pos p.radius hpos.1 (s i)) (by linarith)
  have hnorm := PrescribedRecursiveStability.normalized_gradient scale ell hV hlo hup
  have hstab := PrescribedRecursiveStability.privateMain_childStable P hK hc hcsmall hC hy scale (gradient V) ell hnorm
    r0 σ0 hr0 hσ0 hrootRadius hrootRatio hp hq i
  exact ⟨hquery.1,hquery.2.2,hstab⟩

include hV hlo hup hr0 hσ0 hrootRadius hrootRatio hp hq in
/-- All actual private-final calls have their distinct final width and q-1/4. All guards follow from the original source/root data. -/
theorem privateFinal (i : Fin (ScalarSchedulePayment.ns P hR)) :
    ChildAbsorption.QueryShift (privateFinalP i).program (privateFinalP i).enumeration (privateFinalP i).coefficient
      ((C).S.radius p.radius (s i)) (privateFinalP i).shiftVector ∧
    CovarianceSetup.shiftSq (privateFinalP i).shiftVector≤P.Ds^2 ∧
    ChildStable (privateFinalP i).program (privateFinalP i).coefficient (gradient V) (2*(ell:ℝ)) := by
  have hm : 0<P.m := by have := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega
  have hpos := hp.positive hm P.Ds_pos P.delta_pos hr0 hσ0
  have hqK := PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp
  have hquery := CubicExecutableWorkShift.queryShift_and_mass P hK hc hcsmall hC baseHy scale
    ((C).S.radius p.radius (s i)) (SourceExecutableTables.samplingFinalWidth (C).S p.radius) (p.precision-1/4)
    ((C).S.radius_pos p.radius hpos.1 (s i)) (by linarith)
  have hnorm := PrescribedRecursiveStability.normalized_gradient scale ell hV hlo hup
  have hstab := PrescribedRecursiveStability.privateFinal_childStable P hK hc hcsmall hC hy scale (gradient V) ell hnorm
    r0 σ0 hr0 hσ0 hrootRadius hrootRatio hp hq i
  exact ⟨hquery.1,hquery.2.2,hstab⟩

end AcceleratedLogConcave.Oracle.PrescribedFourChildGuards
