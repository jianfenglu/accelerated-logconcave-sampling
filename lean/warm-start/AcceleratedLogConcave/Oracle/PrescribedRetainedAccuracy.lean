import AcceleratedLogConcave.Oracle.RecursiveRetainedAccuracy
import AcceleratedLogConcave.Oracle.PrescribedMeanNumericalData

/-! Quantitative properties of the exact prescribed retained law construction.
The terminal base transports the original full-seed estimate through the
literal executable equality, including terminal precision overshoots. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrescribedRetainedAccuracy
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall
open RecursiveRetainedAccuracy
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
  {d : ℕ} (ell r0 σ0 : ℝ) (hell : 0≤ell) (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hrootRadius : ell*r0^2≤P.delta)

/-- Admissible physical parameters at an actual reachable call. Positivity
and curvature are derived from the original root and literal call path. -/
def parameters {p : State} {depth cost : ℕ}
    (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
      (PrescribedRecursiveStability.root P r0 σ0) p depth cost) :
    Conditional.SourceParameters (Point d) ell :=
  let hm : 0<P.m := by have h := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega
  let hpos := hp.positive hm P.Ds_pos P.delta_pos hr0 hσ0
  MeanCompletedReference.parentTheta p.radius p.width hpos.1 hpos.2
    (PrescribedMeanNumericalData.reachable_curvature P hell hK hc hcsmall hC hy hr0 hσ0 hrootRadius hp) 0

include hc in
/-- Actual edge accounting keeps every reached precision below the root. -/
theorem precision_le {p : State} {depth cost : ℕ}
    (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
      (PrescribedRecursiveStability.root P r0 σ0) p depth cost) : p.precision≤(P.K:ℝ) := by
  have he := hp.precision_eq
  have ht : 0<P.t := P.t_pos hc
  change p.precision=(P.K:ℝ)-(cost:ℝ)/4-((depth-cost:ℕ):ℝ)*P.t at he
  have hcost : 0≤(cost:ℝ) := Nat.cast_nonneg _
  have hprod : 0≤((depth-cost:ℕ):ℝ)*P.t := mul_nonneg (Nat.cast_nonneg _) ht.le
  linarith

variable {V : Point d → ℝ} (scale : ℝ) (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v≤ell*‖v‖^2)
  (hr1 : r0≤1) (hrootRatio : ell*(r0/σ0)≤P.delta)

include hV hlo hup hr1 hrootRatio in
/-- The exact already constructed recursive kernel obeys original-data
terminal accuracy. There is no supplied terminal accuracy certificate. -/
theorem terminal_accurate {p : State} {depth cost : ℕ}
    (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
      (PrescribedRecursiveStability.root P r0 σ0) p depth cost)
    (hq : p.precision≤1/2) :
    let hF : ContDiff ℝ 2 (scaledPotential V scale) := by unfold scaledPotential; fun_prop
    Accurate (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M
      (by have hm := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega)
      hF hell hlo hup P.t (P.t_pos hc)
      (PrescribedRetainedCoupling.law P hK hc hcsmall hC hy hF hell hlo hup scale (gradient V)
        ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
          (hV.continuous_fderiv (by norm_num))).measurable
        (parameters P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp)
        p.precision (precision_le P hK hc hcsmall hC hy r0 σ0 hp)) (gradient V) P.delta := by
  dsimp only
  unfold PrescribedRetainedCoupling.law
  rw [RecursiveRetainedCoupling.core_terminal (hterminal := hq)]
  rw [RecursiveRetainedAccuracy.accurate_castLaw]
  apply RecursiveRetainedAccuracy.terminal_accurate
  · intro base
    exact PrescribedTerminalAccuracy.terminal_error_memLp P hK hc hcsmall hC hy ell r0 σ0 hell
      scale hV hlo hup hp base
  · intro base
    exact PrescribedTerminalAccuracy.terminal_square_error_le P hK hc hcsmall hC hy ell r0 σ0 hell
      hr0 hr1 hσ0 hrootRadius hrootRatio scale hV hlo hup hp hq base

end AcceleratedLogConcave.Oracle.PrescribedRetainedAccuracy
