import AcceleratedLogConcave.Oracle.RecursiveRetainedCoupling

/-! Actual retained source kernels under the prescribed scalar schedule.
All support budgets and row restrictions are paid by the original cubic
resolution threshold. This constructs source and reference laws only;
quantitative accuracy concerns these same kernels separately. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrescribedRetainedCoupling
open Numerics Numerics.AffineGraph CubicExecutableWorkShift
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := CanonicalTapeMeasurability.tapeSpace d p

variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)

include hK hc hcsmall hC hy in
/-- The literal executable's radius guard, derived from its resolution. -/
theorem radiusGuard : P.R≤1/2 :=
  CubicSchedulePayments.radius_guard P hK hc hcsmall hC
    (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith) (by linarith) hy)

variable {d : ℕ} {F : Point d → ℝ} {ell : ℝ}
  (hF : ContDiff ℝ 2 F) (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (scale : ℝ) (G : Point d → Point d) (hG : Measurable G)

/-- The actual recursive law package. The complete source tape is retained,
and the pair with the original designated input has the prescribed reference
law at every center and every precision up to the original rank. -/
def law (theta : Conditional.SourceParameters (Point d) ell) (q : ℝ) (hq : q≤(P.K:ℝ)) :
    RecursiveRetainedCoupling.At (source P (radiusGuard P hK hc hcsmall hC hy)).M
      (by have hm := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega)
      hF hell hlo hup P.t (P.t_pos hc) theta q
      (data P (radiusGuard P hK hc hcsmall hC hy) hc hcsmall scale theta.radius theta.width q) := by
  let baseHy := PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1)
    (by linarith : 1≤P.Csch) hy
  let C := source P (radiusGuard P hK hc hcsmall hC hy)
  have hm2 := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch)
  have hm : 0<P.m := by omega
  have hy0 := (CubicSchedulePayments.prerequisites P hK hc hcsmall hC baseHy).1
  have hs := CubicSchedulePayments.actual_scalar_payments P hK hc hcsmall hC baseHy
  have hpsieq : C.M.psi=P.delta^(4*P.t) := by
    change P.R^4=P.delta^(4*P.t)
    exact P.psi_eq_R_pow.symm
  exact RecursiveRetainedCoupling.core C.M hm hF hell hlo hup P.t (P.t_pos hc)
    C.nodes (anchors P (radiusGuard P hK hc hcsmall hC hy))
    (seeds P (radiusGuard P hK hc hcsmall hC hy)) C.mesh C.snodes P.Ds P.delta P.w P.NP
    (step_quarter P hc hcsmall) scale (P.K:ℝ) P.Ds_pos P.delta_pos le_rfl
    (ScalarSchedulePayment.I P (radiusGuard P hK hc hcsmall hC hy)) P.Hs (by rfl)
    (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC)
    hs.2.2.2.1 hm2 (P.delta_le_one hy0) hpsieq hs.2.2.2.2.2.1.2.2.2 rfl
    G hG theta q hq

/-- Joint measurability in the actual external center follows from the
constructed kernel, rather than selecting a fixed-center coupling. -/
def kernel (theta : Conditional.SourceParameters (Point d) ell) (q : ℝ) (hq : q≤(P.K:ℝ)) :=
  (law P hK hc hcsmall hC hy hF hell hlo hup scale G hG theta q hq).joint

theorem kernel_markov (theta : Conditional.SourceParameters (Point d) ell) (q : ℝ) (hq : q≤(P.K:ℝ)) :
    IsMarkovKernel (kernel P hK hc hcsmall hC hy hF hell hlo hup scale G hG theta q hq) :=
  (law P hK hc hcsmall hC hy hF hell hlo hup scale G hG theta q hq).markov

theorem kernel_measurable (theta : Conditional.SourceParameters (Point d) ell) (q : ℝ) (hq : q≤(P.K:ℝ)) :
    Measurable (kernel P hK hc hcsmall hC hy hF hell hlo hup scale G hG theta q hq) := Kernel.measurable _

theorem kernel_source (theta : Conditional.SourceParameters (Point d) ell) (q : ℝ) (hq : q≤(P.K:ℝ)) :
    (kernel P hK hc hcsmall hC hy hF hell hlo hup scale G hG theta q hq).fst =
      Kernel.const (Point d)
        (FreshChildRetainedCoupling.sourceLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
          (data P (radiusGuard P hK hc hcsmall hC hy) hc hcsmall scale theta.radius theta.width q).program) :=
  (law P hK hc hcsmall hC hy hF hell hlo hup scale G hG theta q hq).source

theorem kernel_reference (theta : Conditional.SourceParameters (Point d) ell) (q : ℝ)
    (hq : q≤(P.K:ℝ)) (base : Point d) :
    ((kernel P hK hc hcsmall hC hy hF hell hlo hup scale G hG theta q hq) base).map
      (fun z => (z.1.1,z.2)) =
      (stdGaussian (Point d)) ⊗ₘ
        ((Conditional.RecursiveReference.referenceFamily hF hell hlo hup
          (source P (radiusGuard P hK hc hcsmall hC hy)).M
          (by have hm := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega)
          P.t (P.t_pos hc) q).kernel.comap
          (fun p => (MeanCompletedReference.parentTheta theta.radius theta.width
            theta.radius_pos theta.width_pos theta.small base,p)) measurable_prodMk_left) :=
  (law P hK hc hcsmall hC hy hF hell hlo hup scale G hG theta q hq).retained base

end AcceleratedLogConcave.Oracle.PrescribedRetainedCoupling
