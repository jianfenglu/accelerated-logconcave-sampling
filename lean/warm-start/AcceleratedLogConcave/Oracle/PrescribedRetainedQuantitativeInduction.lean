import AcceleratedLogConcave.Oracle.PrescribedRetainedChildPaths
import AcceleratedLogConcave.Oracle.RecursiveRetainedAccuracyWith

/-! The quantitative induction concerns the exact previously constructed
precision-recursive kernels. Its uniform accuracy constant is four, while
the original terminal base satisfies the stronger constant one. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.PrescribedRetainedQuantitativeInduction
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall
open RecursiveRetainedAccuracy
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
  {d : ℕ} (ell r0 σ0 : ℝ) (hell : 0≤ell) (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hrootRadius : ell*r0^2≤P.delta)
  {V : Point d → ℝ} (scale : ℝ) (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v≤ell*‖v‖^2)

/-- This is an alias of the existing actual kernel's law package at a reached
call, not a new selection of a law or accuracy witness. -/
def reachableLaw {p : State} {depth cost : ℕ}
    (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
      (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :=
  let hF : ContDiff ℝ 2 (scaledPotential V scale) := by unfold scaledPotential; fun_prop
  PrescribedRetainedCoupling.law P hK hc hcsmall hC hy hF hell hlo hup scale (gradient V)
    ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp (hV.continuous_fderiv (by norm_num))).measurable
    (PrescribedRetainedAccuracy.parameters P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp)
    p.precision (PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp)

/-- The source's fixed constant-four physical accuracy motive on that exact
retained joint. -/
def AccurateCall {p : State} {depth cost : ℕ}
    (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
      (PrescribedRecursiveStability.root P r0 σ0) p depth cost) : Prop :=
  let hF : ContDiff ℝ 2 (scaledPotential V scale) := by unfold scaledPotential; fun_prop
  AccurateWith (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M
    (by have hm := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega)
    hF hell hlo hup P.t (P.t_pos hc) 4
    (reachableLaw P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp)
    (gradient V) P.delta

variable (hr1 : r0≤1) (hrootRatio : ell*(r0/σ0)≤P.delta)

include hr1 hrootRatio in
/-- Actual terminal calls satisfy the induction motive by their stronger
original-data unit bound; terminal overshoots need no extra hypothesis. -/
theorem terminal_case {p : State} {depth cost : ℕ}
    (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
      (PrescribedRecursiveStability.root P r0 σ0) p depth cost)
    (hq : p.precision≤1/2) :
    AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp := by
  dsimp only [AccurateCall,reachableLaw]
  apply accurateWith_of_accurate
  · norm_num
  · exact PrescribedRetainedAccuracy.terminal_accurate P hK hc hcsmall hC hy ell r0 σ0 hell
      hr0 hσ0 hrootRadius scale hV hlo hup hr1 hrootRatio hp hq

end AcceleratedLogConcave.Oracle.PrescribedRetainedQuantitativeInduction
