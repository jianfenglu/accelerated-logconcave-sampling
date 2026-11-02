import AcceleratedLogConcave.Oracle.PrescribedTerminalAccuracy
import AcceleratedLogConcave.Oracle.MeanOriginalBounds

/-! Original analytic data on the literal executable mean geometry. The
partitions and mesh caps are supplied by the prescribed source schedule.
Reachable curvature is derived from the original root radius, not assumed
separately at every recursive call. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
namespace AcceleratedLogConcave.Oracle.PrescribedMeanNumericalData
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall

variable (P : SourceSchedule) (hR : P.R ≤ 1/2)
  {D : ℕ} {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (x : Point D) (r σ : ℝ) (hr : 0<r) (hσ : 0<σ) (hsmall : r^2*ell≤1/2)

/-- Exact executable geometry; no partition cast or alternate numerical
sampler occurs in this datum. -/
def datum : MeanFlowLp.Data (Fin D) P.m where
  F := F
  hF := hF
  ell := ell
  hell := hell
  hlo := hlo
  hup := hup
  x := x
  r := r
  hr := hr
  hsmall := hsmall
  G := (source P hR).M
  sigma := σ
  hsigma := hσ

@[simp] theorem datum_geometry :
    (datum P hR hF hell hlo hup x r σ hr hσ hsmall).G=(source P hR).M := rfl

/-- Every actual partition in the executable satisfies the smooth receiver's
mesh conditions, with its same order and geometric step. -/
theorem mesh (hm : 2≤P.m) (hh : P.h0≤1/2) :
    MeanCollocationLp.MeshConditions (datum P hR hF hell hlo hup x r σ hr hσ hsmall) P.h0 := by
  exact SourceMeanGeometry.meshConditions _ P.R (P.R^4) P.h0 P.R_pos hR
    (pow_pos P.R_pos 4) P.h0_pos hm (pow_le_one₀ P.R_pos.le (by linarith)) hh rfl

/-- Analytic receiver row mass is exactly the scalar envelope used by the
actual executable matrix; no alternate coefficient is introduced. -/
theorem rowMass_eq :
    MeanCollocationLp.rowMass (datum P hR hF hell hlo hup x r σ hr hσ hsmall) P.h0 =
      SourceMeanExecutable.rowBound (m := P.m) r σ P.delta P.t P.w := by
  rw [RecursiveCall.source_rowBound_eq _ _ _ _ _ P.delta_pos]
  change 256*(P.m:ℝ)^5*r/(σ*P.R^4*P.h0)+4*r^2 = _
  rw [← P.psi_eq_R_pow]
  rfl

section Reachable
variable (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1)
  (by linarith : 1≤P.Csch) hy
local notation "radiusGuard" => CubicSchedulePayments.radius_guard P hK hc hcsmall hC baseHy

/-- The fixed cubic resolution pays all scalar restrictions of the actual
mean mesh. No mesh certificate is an input. -/
theorem scheduled_mesh :
    MeanCollocationLp.MeshConditions
      (datum P radiusGuard hF hell hlo hup x r σ hr hσ hsmall) P.h0 := by
  have hm := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch)
  have hs := (CubicSchedulePayments.actual_scalar_payments P hK hc hcsmall hC baseHy).2.2.2.2.2.1
  exact mesh P radiusGuard hF hell hlo hup x r σ hr hσ hsmall hm hs.2.2.2

include hell in
/-- The actual recursive radius bound pays the curvature domain even at a
terminal edge. There is no positive-curvature or positive-dimension guard. -/
theorem reachable_curvature {r0 σ0 : ℝ} (hr0 : 0<r0) (hσ0 : 0<σ0)
    (hroot : ell*r0^2≤P.delta) {p : State} {depth cost : ℕ}
    (hp : Path (source P radiusGuard) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    p.radius^2*ell≤1/2 := by
  have hm := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch)
  have hpos := hp.positive (by omega) P.Ds_pos P.delta_pos hr0 hσ0
  have hr := PrescribedTerminalAccuracy.radius_le_root hp (by omega) P.Ds_pos P.delta_pos hr0 hσ0
  have hs := (CubicSchedulePayments.actual_scalar_payments P hK hc hcsmall hC baseHy).2.2.2.2.2.1
  have hdelta : P.delta≤1/2 := hs.2.1.trans (hs.2.2.1.trans hs.2.2.2)
  change p.radius≤r0 at hr
  have hsquare : p.radius^2≤r0^2 := by nlinarith [hpos.1]
  calc
    p.radius^2*ell ≤ r0^2*ell := mul_le_mul_of_nonneg_right hsquare hell
    _ ≤ P.delta := by simpa only [mul_comm] using hroot
    _ ≤ 1/2 := hdelta

variable {r0 σ0 : ℝ} (hr0 : 0<r0) (hσ0 : 0<σ0) (hroot : ell*r0^2≤P.delta)
  {p : State} {depth cost : ℕ}

/-- Numerical datum for an actual reachable call. Every local positivity and
curvature condition is derived from the original root and prescribed path. -/
def reachableDatum (hp : Path (source P radiusGuard) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) : MeanFlowLp.Data (Fin D) P.m :=
  let hm := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch)
  let hpos : 0<p.radius ∧ 0<p.width := hp.positive (by omega : 0<P.m) P.Ds_pos P.delta_pos hr0 hσ0
  datum P radiusGuard hF hell hlo hup x p.radius p.width hpos.1 hpos.2
    (reachable_curvature P hell hK hc hcsmall hC hy hr0 hσ0 hroot hp)

@[simp] theorem reachableDatum_geometry (hp : Path (source P radiusGuard) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    (reachableDatum P hF hell hlo hup x hK hc hcsmall hC hy hr0 hσ0 hroot hp).G =
      (source P radiusGuard).M := rfl

theorem reachable_mesh (hp : Path (source P radiusGuard) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    MeanCollocationLp.MeshConditions
      (reachableDatum P hF hell hlo hup x hK hc hcsmall hC hy hr0 hσ0 hroot hp) P.h0 := by
  exact scheduled_mesh P hF hell hlo hup x p.radius p.width _ _ _ hK hc hcsmall hC hy

include hell hr0 hσ0 hroot in
/-- The literal source row envelope is small at every reachable state,
including the factor two required for actual same-tape child stability. -/
theorem reachable_row_payment
    (hrootRatio : ell*(r0/σ0)≤P.delta)
    (hp : Path (source P radiusGuard) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    2*ell*SourceMeanExecutable.rowBound (m := P.m) p.radius p.width P.delta P.t P.w ≤
      P.delta^((1:ℝ)/3) := by
  have hC1 : 1≤P.Csch := by linarith
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hcsmall hC baseHy).1
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hcsmall hC baseHy
  have hb : RecursiveSize.SizeBound ell P.delta 1 1 r0 σ0 := by
    change ell*r0^2≤1*P.delta^1 ∧ ell*(r0/σ0)≤1*P.delta^1
    simpa only [Real.rpow_one,one_mul] using And.intro hroot hrootRatio
  exact (hp.scalar_smallness ell P.Bsize hb (P.m_ge_two hc hcsmall hC1) hell hr0 hσ0
    P.Ds_pos P.delta_pos (P.delta_le_one hy0) (P.t_pos hc) (P.t_le hc hcsmall)
    (P.w_pos hc).le (P.w_lt_t hc hC1).le (P.Bsize_ge_one hc hcsmall hC1 hy0)
    rfl le_rfl hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2
    ((P.rank_budget hc hcsmall).le.trans (by norm_num)) hs.2.2.2.2.1).1

/-- The actual original-data receiver meets the half-contraction restriction
used by its initializer and benchmark-moment suppliers. -/
theorem reachable_contraction
    (hrootRatio : ell*(r0/σ0)≤P.delta)
    (hp : Path (source P radiusGuard) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    MeanCollocationLp.contraction
      (reachableDatum P hF hell hlo hup x hK hc hcsmall hC hy hr0 hσ0 hroot hp) P.h0≤1/2 := by
  have hrow := reachable_row_payment P hell hK hc hcsmall hC hy hr0 hσ0 hroot hrootRatio hp
  have hd := P.delta_le_one (CubicSchedulePayments.prerequisites P hK hc hcsmall hC baseHy).1
  have ht : P.delta^((1:ℝ)/3)≤1 := Real.rpow_le_one P.delta_pos.le hd (by norm_num)
  unfold MeanCollocationLp.contraction
  change ell*MeanCollocationLp.rowMass (datum P radiusGuard hF hell hlo hup x p.radius p.width _ _ _) P.h0≤1/2
  rw [rowMass_eq]
  linarith

end Reachable
end AcceleratedLogConcave.Oracle.PrescribedMeanNumericalData
