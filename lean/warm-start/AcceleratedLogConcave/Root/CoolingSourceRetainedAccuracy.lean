import AcceleratedLogConcave.Root.CoolingSourceRetainedCoupling
import AcceleratedLogConcave.Root.CoolingSourceRootGuards
import AcceleratedLogConcave.Oracle.RecursiveRetainedAccuracyWith
import AcceleratedLogConcave.Oracle.PrescribedRecursiveStability

/-! Public cooling accuracy is derived from the actual recursive mean
children at precision K. The retained public source and all source residuals
are unchanged. Only strictly lower mean accuracy, not public accuracy, is an
induction input. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Root.CoolingSourceRetainedAccuracy
open Oracle Numerics Numerics.AffineGraph TapeLowering
open CanonicalTapeLaw CanonicalTapeMeasurability SourceExecutableTables
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
private theorem payment_nonneg {d m n : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r : ℝ) (hr : 0<r) (N : ℕ) {F : Point d → ℝ} (hF : ContDiff ℝ 2 F)
    {ell : ℝ} (hell : 0≤ell) (hlo : ∀ z w,0≤fderiv ℝ (fderiv ℝ F) z w w)
    (hup : ∀ z w,fderiv ℝ (fderiv ℝ F) z w w≤ell*‖w‖^2)
    (x : Point d) (κ κf : ℝ≥0) (am : ℕ → Fin n → ℝ) (af : Fin n → ℝ) :
    0≤(r*((κf:ℝ)*PrivateCompletedRms.mainBudget S e r N hr hF hell hlo hup x κ am)+
      ∑ i, |samplingFinalWeight S e r i| * PrivateCompletedRms.childPayment S e r hr hF hell hlo hup x i (af i))+
      PrivateCompletedRms.quadratureBudget S r hr hF hell hlo hup := by
  let d0 := PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr
  have hcell : 0≤AffineResidual.cellBudget S.mesh m
      (SamplingGaussianJetLp.cellDerivativeBudget d0 S.mesh m) := by
    unfold AffineResidual.cellBudget
    apply Finset.sum_nonneg
    intro c _
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (S.mesh.length_pos c).le _))
      (SamplingGaussianJetLp.cellDerivativeBudget_nonneg d0 S.mesh m c)) (Nat.cast_nonneg _)
  unfold PrivateCompletedRms.mainBudget PrivateCompletedRms.initializerBudget PrivateCompletedRms.quadratureBudget
    Collocation.forcingSum SharedLayerRms.childRowBudget PrivateCompletedRms.childPayment
  positivity [hcell,S.samplingEnd_pos,PrivateSamplingOriginalBounds.replyBudget_nonneg d0 x,
    PrivateCompletedRms.residualBudget_nonneg S r hr hF hell hlo hup]

variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "C" => CubicExecutableWorkShift.source P hR
local notation "S" => CoolingPrescribedPayments.geometry P hR
local notation "e" => CoolingPrescribedPayments.nodes P
local notation "nc" => Fintype.card ((CoolingPrescribedPayments.mesh P).Source P.m)
local notation "Q" => CoolingPrescribedPayments.setup P hR hc hsmall
variable (h : ℝ) (v : ℝ≥0) (hh : 0<h) (hv : 0<v)
local notation "r" => CoolingExecutable.radius h v
local notation "hr" => CoolingExecutable.radius_pos hh hv
local notation "main" => CoolingExecutable.main Q h v P.K
local notation "final" => CoolingExecutable.final Q h v P.K
variable {d : ℕ} {F : Point d → ℝ} {ell : ℝ}
  (hF : ContDiff ℝ 2 F) (hell : 0≤ell)
  (hlo : ∀ z w,0≤fderiv ℝ (fderiv ℝ F) z w w)
  (hup : ∀ z w,fderiv ℝ (fderiv ℝ F) z w w≤ell*‖w‖^2)
  (G : Point d → Point d) (hG : Measurable G)
  (hellδ : ell≤P.delta) (hsq : (CoolingExecutable.radius h v)^2≤2*P.delta)
  (hnormal : LipschitzWith ⟨ell,hell⟩ (fun x => Real.sqrt h • G (Real.sqrt h • x)))
local notation "sigmaM" => RecursiveMeanPublicTable.mainWidth nc r P.R P.Ds (r^2)
local notation "sigmaF" => samplingFinalWidth S r
local notation "kappa" => PrivateSourceScalarAbsorption.twiceNonneg ell hell
local notation "mainMass" => (fun i => (CoolingSourceRetainedCoupling.main_shift P hK hc hsmall hC hy h v hh hv i).2)
local notation "finalMass" => (fun i => (CoolingSourceRetainedCoupling.final_shift P hK hc hsmall hC hy h v hh hv i).2)
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d

include hnormal hellδ hsq hh hv in
/-- Actual public main stability follows from the original normalized oracle
and concrete public root guards, on every complete child tape. -/
theorem main_childStable (i : Fin nc) :
    FixedTapeStability.ChildStable (main i).program (main i).coefficient G (kappa:ℝ) := by
  have hm : 0<P.m := by have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch); omega
  have hrad := CoolingSourceRootGuards.radius_guards P hK hc hsmall hC hy hell hellδ hr hsq (e i)
  have hwidth := RecursiveExecutableDomain.sampling_main_width_pos S e r P.Ds hm hr P.Ds_pos
  exact PrescribedRecursiveStability.reachable_childStable P hK hc hsmall hC hy
    (Real.sqrt h) G ⟨ell,hell⟩ hnormal ((S).radius r (e i)) sigmaM hrad.1 hwidth hrad.2.2
    (CoolingSourceRootGuards.main_ratio P hK hc hsmall hC hy hell hellδ hr hsq (e i))
    (RecursiveCall.Path.refl _)

include hnormal hellδ hsq hh hv in
theorem final_childStable (i : Fin nc) :
    FixedTapeStability.ChildStable (final i).program (final i).coefficient G (kappa:ℝ) := by
  have hrad := CoolingSourceRootGuards.radius_guards P hK hc hsmall hC hy hell hellδ hr hsq (e i)
  have hwidth := RecursiveExecutableDomain.sampling_final_width_pos S r hr
  exact PrescribedRecursiveStability.reachable_childStable P hK hc hsmall hC hy
    (Real.sqrt h) G ⟨ell,hell⟩ hnormal ((S).radius r (e i)) sigmaF hrad.1 hwidth hrad.2.2
    (CoolingSourceRootGuards.final_ratio P hK hc hsmall hC hy hell hellδ hr hsq (e i))
    (RecursiveCall.Path.refl _)

include hc hsmall hC in
private theorem m_pos : 0<P.m := by
  have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  omega
local notation "hm" => m_pos P hc hsmall hC

/-- Literal normalized public error on the entire retained original seed. -/
def error (x : Point d)
    (z : (Point d × Tape d (CoolingExecutable.data Q h v P.K).program) × Point d) : Point d :=
  PrivateRetainedAccuracy.error (G := G) S e r P.Ds main final P.NP x z

/-- This is the literal public program's error at its actual normalized
entering center. The retained designated source input is unused by that
sampler; it is still retained in full by the joint kernel. -/
theorem error_eq_execute (x : Point d)
    (z : (Point d × Tape d (CoolingExecutable.data Q h v P.K).program) × Point d) :
    error (G := G) P hK hc hsmall hC hy h v ((Real.sqrt h)⁻¹ • x) z =
      (show Point d from (CoolingExecutable.execute Q h v P.K G x z.1.2).value)-z.2 := by
  have he := FixedTapeSampling.build_momentum_eq S e r P.Ds main final P.NP G
    ((Real.sqrt h)⁻¹ • x) (0 : Point d) z.1.1 z.1.2
  exact congrArg (fun w : Point d => w-z.2) he

include hnormal hellδ hsq hh hv in
/-- The constructed public conditional coupling obeys the concrete tau=1
payment, using accuracy only for its actual recursive mean children at K. -/
theorem square_error_bound (hp : (CoolingExecutable.radius h v)^2*ell≤1/2)
    (hmain : ∀ i, RecursiveRetainedAccuracy.AccurateWith (C).M hm hF hell hlo hup P.t (P.t_pos hc) 4
      (CoolingSourceRetainedCoupling.mainLaw P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp i) G P.delta)
    (hfinal : ∀ i, RecursiveRetainedAccuracy.AccurateWith (C).M hm hF hell hlo hup P.t (P.t_pos hc) 4
      (CoolingSourceRetainedCoupling.finalLaw P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp i) G P.delta)
    (x : Point d) :
    ∃ _hi : MemLp (error (G := G) P hK hc hsmall hC hy h v x) 2
      ((CoolingSourceRetainedCoupling.kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) x),
      (∫ z, ‖error (G := G) P hK hc hsmall hC hy h v x z‖^2
        ∂((CoolingSourceRetainedCoupling.kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) x))≤
        (3*P.delta^(P.K:ℝ)*Gibbs.primitiveScale F x)^2 := by
  have hd := PrivateSourceScalarAbsorption.delta_le_hundredth P hK hc (by linarith) (by linarith) hy
  have hr1 : r≤1 := by nlinarith [sq_nonneg r]
  let am := fun (_k : ℕ) (_i : Fin nc) => 4*sigmaM*P.delta^(P.K:ℝ)
  let af := fun (_i : Fin nc) => 4*sigmaF*P.delta^(P.K:ℝ)
  let Jf := CoolingSourceRetainedCoupling.finalLower P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp
  let J := CoolingSourceRetainedCoupling.mainLower P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp
  obtain ⟨hmem,hbound⟩ := PrivateRetainedAccuracy.square_error_bound (G := G) (hG := hG)
    S e r P.Ds main final P.NP hr P.Ds_pos mainMass finalMass L rfl hF hell hlo hup Jf J
    (by have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch); omega) hp x kappa kappa am af
    (fun i => (CoolingSourceRetainedCoupling.main_shift P hK hc hsmall hC hy h v hh hv i).1)
    (fun i => (CoolingSourceRetainedCoupling.final_shift P hK hc hsmall hC hy h v hh hv i).1)
    (main_childStable P hK hc hsmall hC hy h v hh hv hell G hellδ hsq hnormal)
    (final_childStable P hK hc hsmall hC hy h v hh hv hell G hellδ hsq hnormal)
    (fun k hk i y => (hmain i y).1)
    (fun k hk i y => by
      calc
        _ ≤ (4*(sigmaM*P.delta^(P.K:ℝ)*Gibbs.primitiveScale F y))^2 := (hmain i y).2
        _ = _ := by dsimp only [am]; ring)
    (fun i y => (hfinal i y).1)
    (fun i y => by
      calc
        _ ≤ (4*(sigmaF*P.delta^(P.K:ℝ)*Gibbs.primitiveScale F y))^2 := (hfinal i y).2
        _ = _ := by dsimp only [af]; ring)
  have hpay := CoolingSourceScalarPayments.retained_payment_le P hK hc hsmall hC hy hF hell hlo hup
    r hr hr1 hellδ x
  have hnonneg := payment_nonneg S e r hr P.NP hF hell hlo hup x kappa kappa am af
  refine ⟨hmem,hbound.trans ?_⟩
  exact (sq_le_sq₀ hnonneg (by positivity [P.delta_pos,Gibbs.primitiveScale_nonneg F x])).2 hpay

end AcceleratedLogConcave.Root.CoolingSourceRetainedAccuracy
