import AcceleratedLogConcave.Root.CoolingSourceRetainedAccuracy
import AcceleratedLogConcave.Oracle.PrescribedRetainedFullAccuracy

/-! The actual public cooling coupling under the physical source schedule.
All recursive mean accuracy inputs are discharged by the full precision
induction on the same prescribed kernels. Original-gradient execution, full
source seeds, and the true public child precision K are preserved. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Root.CoolingSourceConditionalAccuracy
open Oracle Numerics Numerics.AffineGraph TapeLowering
open CanonicalTapeLaw CanonicalTapeMeasurability SourceExecutableTables RecursiveCall
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "hyPrivate" => MeanSourceScalarAbsorption.private_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hyPrivate
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "C" => CubicExecutableWorkShift.source P hR
local notation "S" => CoolingPrescribedPayments.geometry P hR
local notation "e" => CoolingPrescribedPayments.nodes P
local notation "nc" => Fintype.card ((CoolingPrescribedPayments.mesh P).Source P.m)
local notation "Q" => CoolingPrescribedPayments.setup P hR hc hsmall
variable (v : ℝ≥0) (hv : 0<v) (hvUpper : (v:ℝ)≤2*P.delta^2)
  {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  {ell : ℝ} (hell : 0≤ell) (hellδ : ell≤P.delta)
  (hlo : ∀ z w,0≤fderiv ℝ (fderiv ℝ (scaledPotential V (Real.sqrt P.delta))) z w w)
  (hup : ∀ z w,fderiv ℝ (fderiv ℝ (scaledPotential V (Real.sqrt P.delta))) z w w≤ell*‖w‖^2)
local notation "r" => CoolingExecutable.radius P.delta v
local notation "hr" => CoolingExecutable.radius_pos P.delta_pos hv
local notation "F" => scaledPotential V (Real.sqrt P.delta)

include hV in
private theorem scaled_contDiff : ContDiff ℝ 2 (scaledPotential V (Real.sqrt P.delta)) := by
  unfold scaledPotential
  fun_prop
include hV in
private theorem oracle_measurable : Measurable (gradient V) :=
  ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
    (hV.continuous_fderiv (by norm_num))).measurable
local notation "hF" => scaled_contDiff P hV
local notation "hG" => oracle_measurable hV

include hK hc hsmall hC hy hvUpper hell hellδ in
/-- Actual physical radius and curvature, derived from the public variance
range rather than supplied as a sampler-domain assertion. -/
theorem physical : (CoolingExecutable.radius P.delta v)^2*ell≤1/2 := by
  have hs := CoolingSourceRootGuards.physical_radius_sq P hvUpper
  have hd := PrivateSourceScalarAbsorption.delta_le_hundredth P hK hc (by linarith) (by linarith) hyPrivate
  have hm := mul_le_mul hs hellδ hell (by positivity [P.delta_pos] : 0≤2*P.delta)
  nlinarith [mul_le_mul_of_nonneg_right hd P.delta_pos.le]
local notation "hp" => physical P hK hc hsmall hC hy v hvUpper hell hellδ
local notation "sigmaM" => RecursiveMeanPublicTable.mainWidth nc r P.R P.Ds (r^2)
local notation "sigmaF" => samplingFinalWidth S r
include hc hsmall hC in
private theorem m_pos : 0<P.m := by
  have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  omega
local notation "hm" => m_pos P hc hsmall hC

include hvUpper hellδ hv hlo hup in
/-- Public main accuracy comes from the full induction at its literal root
parameters; no lower kernel or quantitative certificate is supplied. -/
theorem main_accurate (i : Fin nc) :
    RecursiveRetainedAccuracy.AccurateWith (C).M hm hF hell hlo hup P.t (P.t_pos hc) 4
      (CoolingSourceRetainedCoupling.mainLaw P hK hc hsmall hC hyPrivate P.delta v P.delta_pos hv
        hF hell hlo hup (gradient V) hG hp i) (gradient V) P.delta := by
  have hs := CoolingSourceRootGuards.physical_radius_sq P hvUpper
  have hg := CoolingSourceRootGuards.radius_guards P hK hc hsmall hC hyPrivate hell hellδ hr hs (e i)
  have hw := RecursiveExecutableDomain.sampling_main_width_pos S e r P.Ds hm hr P.Ds_pos
  exact PrescribedRetainedFullAccuracy.accurate P hK hc hsmall hC hyPrivate ell
    ((S).radius r (e i)) sigmaM hell hg.1 hw hg.2.2 (Real.sqrt P.delta) hV hlo hup
    hy hg.2.1 hellδ (CoolingSourceRootGuards.main_ratio P hK hc hsmall hC hyPrivate hell hellδ hr hs (e i))
    (RecursiveCall.Path.refl _)

include hvUpper hellδ hv hlo hup in
theorem final_accurate (i : Fin nc) :
    RecursiveRetainedAccuracy.AccurateWith (C).M hm hF hell hlo hup P.t (P.t_pos hc) 4
      (CoolingSourceRetainedCoupling.finalLaw P hK hc hsmall hC hyPrivate P.delta v P.delta_pos hv
        hF hell hlo hup (gradient V) hG hp i) (gradient V) P.delta := by
  have hs := CoolingSourceRootGuards.physical_radius_sq P hvUpper
  have hg := CoolingSourceRootGuards.radius_guards P hK hc hsmall hC hyPrivate hell hellδ hr hs (e i)
  have hw := RecursiveExecutableDomain.sampling_final_width_pos S r hr
  exact PrescribedRetainedFullAccuracy.accurate P hK hc hsmall hC hyPrivate ell
    ((S).radius r (e i)) sigmaF hell hg.1 hw hg.2.2 (Real.sqrt P.delta) hV hlo hup
    hy hg.2.1 hellδ (CoolingSourceRootGuards.final_ratio P hK hc hsmall hC hyPrivate hell hellδ hr hs (e i))
    (RecursiveCall.Path.refl _)

include hvUpper hellδ hv hlo hup in
/-- Concrete conditional public error bound on the constructed full-source
coupling. It has no public or child accuracy premises. -/
theorem square_error_bound (x : Point d) :
    ∃ _hi : MemLp (CoolingSourceRetainedAccuracy.error (G := gradient V) P hK hc hsmall hC hyPrivate P.delta v x) 2
      ((CoolingSourceRetainedCoupling.kernel P hK hc hsmall hC hyPrivate P.delta v P.delta_pos hv
        hF hell hlo hup (gradient V) hG hp) x),
      (∫ z, ‖CoolingSourceRetainedAccuracy.error (G := gradient V) P hK hc hsmall hC hyPrivate P.delta v x z‖^2
        ∂((CoolingSourceRetainedCoupling.kernel P hK hc hsmall hC hyPrivate P.delta v P.delta_pos hv
          hF hell hlo hup (gradient V) hG hp) x))≤
        (3*P.delta^(P.K:ℝ)*Gibbs.primitiveScale F x)^2 := by
  exact CoolingSourceRetainedAccuracy.square_error_bound P hK hc hsmall hC hyPrivate P.delta v P.delta_pos hv
    hF hell hlo hup (gradient V) hG hellδ (CoolingSourceRootGuards.physical_radius_sq P hvUpper)
    (PrescribedRecursiveStability.normalized_gradient (Real.sqrt P.delta) ⟨ell,hell⟩ hV hlo hup) hp
    (main_accurate P hK hc hsmall hC hy v hv hvUpper hV hell hellδ hlo hup)
    (final_accurate P hK hc hsmall hC hy v hv hvUpper hV hell hellδ hlo hup) x

end AcceleratedLogConcave.Root.CoolingSourceConditionalAccuracy
