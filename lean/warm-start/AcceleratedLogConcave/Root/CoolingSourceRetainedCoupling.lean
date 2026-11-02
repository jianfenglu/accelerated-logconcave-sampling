import AcceleratedLogConcave.Root.CoolingSourceScalarPayments
import AcceleratedLogConcave.Oracle.PrescribedRetainedCoupling
import AcceleratedLogConcave.Oracle.PrivateRetainedAccuracy

/-! The literal public cooling execution, augmented using the already
constructed recursive mean kernels at its actual child precision K. The
complete original public tape is retained. No public accuracy is an input. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Root.CoolingSourceRetainedCoupling
open Oracle Numerics Numerics.AffineGraph TapeLowering
open CanonicalTapeLaw CanonicalTapeMeasurability SourceExecutableTables
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
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

/-- The actual public main child keeps precision K and the inherited source
mean's own private geometry. -/
theorem main_eq_data (i : Fin nc) : main i =
    CubicExecutableWorkShift.data P hR hc hsmall (Real.sqrt h) ((S).radius r (e i))
      (RecursiveMeanPublicTable.mainWidth nc r P.R P.Ds (r^2)) (P.K:ℝ) := rfl

theorem final_eq_data (i : Fin nc) : final i =
    CubicExecutableWorkShift.data P hR hc hsmall (Real.sqrt h) ((S).radius r (e i))
      (samplingFinalWidth S r) (P.K:ℝ) := rfl

include hh hv

/-- The concrete support-height payment covers the whole public main child,
including all its consumed and residual source coordinates. -/
theorem main_shift (i : Fin nc) :
    ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      ((S).radius r (e i)) (main i).shiftVector ∧
      CovarianceSetup.shiftSq (main i).shiftVector≤P.Ds^2 := by
  have hs := CubicExecutableWorkShift.queryShift_and_mass P hK hc hsmall hC baseHy
    (Real.sqrt h) ((S).radius r (e i))
    (RecursiveMeanPublicTable.mainWidth nc r P.R P.Ds (r^2)) (P.K:ℝ)
    ((S).radius_pos r hr (e i)) le_rfl
  exact ⟨hs.1,hs.2.2⟩

theorem final_shift (i : Fin nc) :
    ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      ((S).radius r (e i)) (final i).shiftVector ∧
      CovarianceSetup.shiftSq (final i).shiftVector≤P.Ds^2 := by
  have hs := CubicExecutableWorkShift.queryShift_and_mass P hK hc hsmall hC baseHy
    (Real.sqrt h) ((S).radius r (e i)) (samplingFinalWidth S r) (P.K:ℝ)
    ((S).radius_pos r hr (e i)) le_rfl
  exact ⟨hs.1,hs.2.2⟩

variable {d : ℕ} {F : Point d → ℝ} {ell : ℝ}
  (hF : ContDiff ℝ 2 F) (hell : 0≤ell)
  (hlo : ∀ z w,0≤fderiv ℝ (fderiv ℝ F) z w w)
  (hup : ∀ z w,fderiv ℝ (fderiv ℝ F) z w w≤ell*‖w‖^2)
  (G : Point d → Point d) (hG : Measurable G)
omit hh hv in
include hc hsmall hC in
private theorem m_pos : 0<P.m := by
  have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  omega
local notation "hm" => m_pos P hc hsmall hC
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d

/-- Exact recursive mean law used by a public main occurrence; its source is
that same child's complete canonical seed. -/
def mainLaw (hp : r^2*ell≤1/2) (i : Fin nc) :=
  PrescribedRetainedCoupling.law P hK hc hsmall hC hy hF hell hlo hup (Real.sqrt h) G hG
    (PrivateRecursiveBatchBudget.mainParameters S e r P.Ds ell hm hr P.Ds_pos hell hp i (0 : Point d)) (P.K:ℝ) le_rfl

def finalLaw (hp : r^2*ell≤1/2) (i : Fin nc) :=
  PrescribedRetainedCoupling.law P hK hc hsmall hC hy hF hell hlo hup (Real.sqrt h) G hG
    (PrivateRecursiveBatchBudget.finalParameters S e r ell hr hell hp i (0 : Point d)) (P.K:ℝ) le_rfl

/-- Lower reference disintegration for the actual reached public main batch.
Its Gaussian marginal is proved from the recursive reference invariant. -/
def mainLower (hp : r^2*ell≤1/2) (k : ℕ) (hk : k<P.NP) :=
  PrivateChronologicalCoupling.recursiveLower S e r P.Ds main final P.NP hr P.Ds_pos
    (fun i => (main_shift P hK hc hsmall hC hy h v hh hv i).2)
    L hF hell hlo hup (C).M hm P.t (P.t_pos hc) (fun _ => (P.K:ℝ)) (PrivateRecursiveBatchBudget.mainParameters S e r P.Ds ell hm hr P.Ds_pos hell hp)
    (fun i => (mainLaw P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp i).joint)
    (fun i => (mainLaw P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp i).markov)
    (fun i => (mainLaw P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp i).source)
    (fun i y => (mainLaw P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp i).retained y)
    (PrivateChronologicalCoupling.stage S e r P.Ds main final P.NP k hk.le).1
    (PrivateChronologicalCoupling.stage_positive S e r P.Ds main final P.NP k hk)

/-- The actual public paid-final batch uses the same canonical lower kernels,
without turning its original designated child inputs into references. -/
def finalLower (hp : r^2*ell≤1/2) :=
  FreshChildBatchCoupling.Lower.ofRecursiveReference L
    (PrivateFinalCoupling.data S e r P.Ds main final P.NP hr P.Ds_pos
      (fun i => (final_shift P hK hc hsmall hC hy h v hh hv i).2)
      (PrivateChronologicalCoupling.terminalCursor S e r P.Ds main final P.NP).old)
    hF hell hlo hup (C).M hm P.t (P.t_pos hc) (fun _ => (P.K:ℝ)) (PrivateRecursiveBatchBudget.finalParameters S e r ell hr hell hp)
    (fun i => (finalLaw P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp i).joint)
    (fun i => (finalLaw P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp i).markov)
    (fun i => (finalLaw P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp i).source)
    (fun i y => (finalLaw P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp i).retained y)

local notation "mainMass" => (fun i => (main_shift P hK hc hsmall hC hy h v hh hv i).2)
local notation "finalMass" => (fun i => (final_shift P hK hc hsmall hC hy h v hh hv i).2)

/-- Constructed normalized public joint, with the complete original canonical
source seed. Every conditional is the actual recursive mean law above. -/
def kernel (hp : r^2*ell≤1/2) :=
  PrivateCompletedReference.retainedKernel S e r P.Ds main final P.NP hr P.Ds_pos
    mainMass finalMass L rfl hF hell hlo hup
    (finalLower P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp)
    (mainLower P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp)

instance kernel_markov (hp : r^2*ell≤1/2) : IsMarkovKernel
    (kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) := by
  unfold kernel
  infer_instance

/-- Exact original public full-seed projection, including all residual
uniforms and the literal final reserve draw. -/
theorem kernel_source (hp : r^2*ell≤1/2) (x : Point d) :
    ((kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) x).map Prod.fst =
      FreshChildRetainedCoupling.sourceLaw L (CoolingExecutable.data Q h v P.K).program := by
  exact PrivateCompletedReference.retainedKernel_source S e r P.Ds main final P.NP hr P.Ds_pos
    mainMass finalMass L rfl hF hell hlo hup
    (finalLower P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp)
    (mainLower P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) x

/-- The public tau=1 reference has its exact conditional forward law, jointly
with the original designated source Gaussian. -/
theorem kernel_reference (hp : r^2*ell≤1/2) (x : Point d) :
    ((kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) x).map
      (fun z => (z.1.1,z.2)) =
      (stdGaussian (Point d)).prod
        (Channels.forward (Conditional.baseLaw F x r) ⟨1,by norm_num⟩) := by
  have hj := PrivateCompletedReference.retainedKernel_reference S e r P.Ds main final P.NP hr P.Ds_pos
    mainMass finalMass L rfl hF hell hlo hup
    (finalLower P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp)
    (mainLower P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) hm x
  unfold kernel
  simpa only [CoolingPrescribedPayments.public_tau,one_pow] using hj

end AcceleratedLogConcave.Root.CoolingSourceRetainedCoupling
