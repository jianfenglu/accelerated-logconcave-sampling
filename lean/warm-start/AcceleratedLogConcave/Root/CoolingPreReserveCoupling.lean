import AcceleratedLogConcave.Root.CoolingSourceRetainedCoupling
import AcceleratedLogConcave.Root.CoolingSourceRetainedAccuracy
import AcceleratedLogConcave.Root.CoolingReserveLaw
import AcceleratedLogConcave.Oracle.PrivateCompletedPreReserve

/-! The actual public pre-reserve coupling. Both readouts come from the
constructed retained source kernel and its complete original tape. Its right
marginal is the literal public preKernel; its left marginal is the exact
three-quarter reference law, proved using the same reserve coordinate. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Root.CoolingPreReserveCoupling
open Oracle Numerics Numerics.AffineGraph TapeLowering
open CanonicalTapeLaw CanonicalTapeMeasurability SourceExecutableTables
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
private theorem id_prod_map_apply {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (κ : Kernel X Y) [IsMarkovKernel κ] (f : X × Y → Z) (hf : Measurable f) (x : X) :
    ((Kernel.id ×ₖ κ).map f) x = (κ x).map (fun y => f (x,y)) := by
  rw [Kernel.map_apply _ hf,Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl

variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "S" => CoolingPrescribedPayments.geometry P hR
local notation "e" => CoolingPrescribedPayments.nodes P
local notation "Q" => CoolingPrescribedPayments.setup P hR hc hsmall
variable (h : ℝ) (v : ℝ≥0) (hh : 0<h) (hv : 0<v)
local notation "r" => CoolingExecutable.radius h v
local notation "hr" => CoolingExecutable.radius_pos hh hv
local notation "main" => CoolingExecutable.main Q h v P.K
local notation "final" => CoolingExecutable.final Q h v P.K
variable {d : ℕ}
local notation "Host" => (CoolingExecutable.data Q h v P.K).program
local notation "Seed" => (Point d × Tape d Host) × Point d
variable {F : Point d → ℝ} {ell : ℝ}
  (hF : ContDiff ℝ 2 F) (hell : 0≤ell)
  (hlo : ∀ z w,0≤fderiv ℝ (fderiv ℝ F) z w w)
  (hup : ∀ z w,fderiv ℝ (fderiv ℝ F) z w w≤ell*‖w‖^2)
  (G : Point d → Point d) (hG : Measurable G)
  (hp : (CoolingExecutable.radius h v)^2*ell≤1/2)
local notation "K" => CoolingSourceRetainedCoupling.kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp
local notation "mainMass" => (fun i => (CoolingSourceRetainedCoupling.main_shift P hK hc hsmall hC hy h v hh hv i).2)
local notation "finalMass" => (fun i => (CoolingSourceRetainedCoupling.final_shift P hK hc hsmall hC hy h v hh hv i).2)
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d

/-- The actual retained reference before the actual final reserve. -/
def reference (z : Seed) : Point d :=
  PrivateCompletedPreReserve.preReference S e r P.Ds main final P.NP z

theorem reference_measurable : Measurable (reference (d := d) P hK hc hsmall hC hy h v) :=
  PrivateCompletedPreReserve.preReference_measurable S e r P.Ds main final P.NP

include hG in
private theorem actual_pre_measurable :
    Measurable (fun z : Point d × Seed => CoolingExecutable.preReserve Q h v P.K G z.1 z.2.1.2) := by
  have hrun := CanonicalTapeMeasurability.program_point_of_measurable Host G hG
    (fun _ : Point d × Seed => (CoolingExecutable.data Q h v P.K).coefficient)
    (fun z : Point d × Seed => (Real.sqrt h)⁻¹ • z.1)
    (fun _ : Point d × Seed => (0 : Point d)) (fun z : Point d × Seed => z.2.1.2)
    measurable_const (measurable_fst.const_smul ((Real.sqrt h)⁻¹)) measurable_const measurable_snd.fst.snd
  have hres := (PrivateCompletedPreReserve.reserve_measurable S e r P.Ds main final P.NP).comp
    (show Measurable (fun z : Point d × Seed => z.2.1.2) from measurable_snd.fst.snd)
  convert hrun.sub (hres.const_smul (1/2 : ℝ)) using 1
  funext z
  change CoolingExecutable.preReserve Q h v P.K G z.1 z.2.1.2 =
    (show Point d from (CoolingExecutable.execute Q h v P.K G z.1 z.2.1.2).value)-
      (1/2 : ℝ) • CoolingExecutable.reserve Q h v P.K z.2.1.2
  rw [CoolingExecutable.execute_value_eq_preReserve_add_reserve]
  module

/-- Both actual readouts are measurable in the external physical center and
the same complete retained source sample. -/
def readout (z : Point d × Seed) : Point d × Point d :=
  (reference P hK hc hsmall hC hy h v z.2,CoolingExecutable.preReserve Q h v P.K G z.1 z.2.1.2)

include hG in
theorem readout_measurable : Measurable (readout (G := G) P hK hc hsmall hC hy h v) :=
  ((reference_measurable P hK hc hsmall hC hy h v).comp measurable_snd).prodMk
    (actual_pre_measurable P hK hc hsmall hC hy h v G hG)

include hh hv hF hell hlo hup hG hp

/-- Concrete public pre-reserve coupling, without supplied coupling kernels
or current public correctness assertions. -/
def kernel : Kernel (Point d) (Point d × Point d) :=
  ((Kernel.id : Kernel (Point d) (Point d)) ×ₖ
    ((CoolingSourceRetainedCoupling.kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp).comap
      (fun x : Point d => (Real.sqrt h)⁻¹ • x) (by fun_prop))).map
      (readout (G := G) P hK hc hsmall hC hy h v)

instance kernel_markov : IsMarkovKernel
    (kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) := by
  unfold kernel
  exact Kernel.IsMarkovKernel.map _ (readout_measurable P hK hc hsmall hC hy h v G hG)

include hG in
theorem kernel_apply (x : Point d) :
    (kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) x =
      (K ((Real.sqrt h)⁻¹ • x)).map (fun z : Seed =>
        (reference P hK hc hsmall hC hy h v z,CoolingExecutable.preReserve Q h v P.K G x z.1.2)) := by
  exact id_prod_map_apply
    ((CoolingSourceRetainedCoupling.kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp).comap
      (fun x : Point d => (Real.sqrt h)⁻¹ • x) (by fun_prop))
    (readout (G := G) P hK hc hsmall hC hy h v)
    (readout_measurable P hK hc hsmall hC hy h v G hG) x

include hh hv in
/-- Exact pre-reserve reference marginal from the actual chronological joint. -/
theorem reference_law (x : Point d) :
    (K ((Real.sqrt h)⁻¹ • x)).map (reference P hK hc hsmall hC hy h v) =
      Channels.forward (Conditional.baseLaw F ((Real.sqrt h)⁻¹ • x) r) (3/4) := by
  have hm : 0<P.m := by have := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch); omega
  have hj := PrivateCompletedPreReserve.retained_preReference_law S e r P.Ds main final P.NP
    hr P.Ds_pos mainMass finalMass L rfl hF hell hlo hup
    (CoolingSourceRetainedCoupling.finalLower P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp)
    (CoolingSourceRetainedCoupling.mainLower P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp)
    hm ((Real.sqrt h)⁻¹ • x)
  have he : (⟨3*(S).τ^2/4,by positivity⟩ : ℝ≥0)=(3/4:ℝ≥0) := by
    ext
    change (3:ℝ)*1^2/4=3/4
    norm_num
  rw [he] at hj
  exact hj

include hG in
/-- The implemented marginal is the literal public pre-reserve kernel, with
canonical/native semantics connected by identity on the entire original tape. -/
theorem actual_law (x : Point d) :
    (K ((Real.sqrt h)⁻¹ • x)).map
      (fun z : Seed => CoolingExecutable.preReserve Q h v P.K G x z.1.2) =
      CoolingExecutable.preKernel Q h v P.K G x := by
  have hsrc := CoolingSourceRetainedCoupling.kernel_source P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp ((Real.sqrt h)⁻¹ • x)
  have hfst : MeasurePreserving (Prod.fst : Seed → Point d × Tape d Host) _ _ := ⟨measurable_fst,hsrc⟩
  let _ : IsProbabilityMeasure (CanonicalTapeLaw.tapeLaw L Host) := CanonicalTapeLaw.tapeLaw_probability L Host
  have ht : MeasurePreserving (Prod.snd : Point d × Tape d Host → Tape d Host)
      ((stdGaussian (Point d)).prod (CanonicalTapeLaw.tapeLaw L Host))
      (CanonicalTapeLaw.tapeLaw L Host) := measurePreserving_snd
  have hm : Measurable (fun ω : Tape d Host => CoolingExecutable.preReserve Q h v P.K G x ω) := by
    have hrun := CanonicalTapeMeasurability.program_point_of_measurable Host G hG
      (fun _ : Tape d Host => (CoolingExecutable.data Q h v P.K).coefficient)
      (fun _ : Tape d Host => (Real.sqrt h)⁻¹ • x)
      (fun _ : Tape d Host => (0 : Point d)) (fun ω : Tape d Host => ω)
      measurable_const measurable_const measurable_const measurable_id
    have hres := PrivateCompletedPreReserve.reserve_measurable S e r P.Ds main final P.NP (d := d)
    convert hrun.sub (hres.const_smul (1/2 : ℝ)) using 1
    funext ω
    change CoolingExecutable.preReserve Q h v P.K G x ω =
      (show Point d from (CoolingExecutable.execute Q h v P.K G x ω).value)-
        (1/2 : ℝ) • CoolingExecutable.reserve Q h v P.K ω
    rw [CoolingExecutable.execute_value_eq_preReserve_add_reserve]
    module
  have hpremap : MeasurePreserving (fun ω : Tape d Host => CoolingExecutable.preReserve Q h v P.K G x ω)
      (CanonicalTapeLaw.tapeLaw L Host)
      ((CanonicalTapeLaw.tapeLaw L Host).map (CoolingExecutable.preReserve Q h v P.K G x)) := ⟨hm,rfl⟩
  have he := (hpremap.comp (ht.comp hfst)).map_eq
  exact he.trans ((Probability.CanonicalNativeTapeLaw.map_native_eq d Host
    (CoolingExecutable.preReserve Q h v P.K G x)).symm.trans
      (CoolingReserveLaw.preKernel_apply Q h v P.K hG x).symm)

include hG in
theorem kernel_fst (x : Point d) :
    ((kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) x).map Prod.fst =
      Channels.forward (Conditional.baseLaw F ((Real.sqrt h)⁻¹ • x) r) (3/4) := by
  have hpair := (readout_measurable P hK hc hsmall hC hy h v G hG).comp
    (show Measurable (fun z : Seed => (x,z)) from measurable_const.prodMk measurable_id)
  calc
    _ = ((K ((Real.sqrt h)⁻¹ • x)).map (fun z : Seed =>
        (reference P hK hc hsmall hC hy h v z,CoolingExecutable.preReserve Q h v P.K G x z.1.2))).map Prod.fst :=
      congrArg (fun μ : Measure (Point d × Point d) => μ.map Prod.fst)
        (kernel_apply P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp x)
    _ = _ := (Measure.map_map measurable_fst hpair).trans
      (reference_law P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp x)

include hG in
theorem kernel_snd (x : Point d) :
    ((kernel P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp) x).map Prod.snd =
      CoolingExecutable.preKernel Q h v P.K G x := by
  have hpair := (readout_measurable P hK hc hsmall hC hy h v G hG).comp
    (show Measurable (fun z : Seed => (x,z)) from measurable_const.prodMk measurable_id)
  calc
    _ = ((K ((Real.sqrt h)⁻¹ • x)).map (fun z : Seed =>
        (reference P hK hc hsmall hC hy h v z,CoolingExecutable.preReserve Q h v P.K G x z.1.2))).map Prod.snd :=
      congrArg (fun μ : Measure (Point d × Point d) => μ.map Prod.snd)
        (kernel_apply P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp x)
    _ = _ := (Measure.map_map measurable_snd hpair).trans
      (actual_law P hK hc hsmall hC hy h v hh hv hF hell hlo hup G hG hp x)

omit hh hv hF hell hlo hup hG hp in
/-- Removing the same reserve from both readouts leaves the literal public
execution error unchanged, up to the orientation of the coupling pair. -/
theorem difference_eq_error (x : Point d) (z : Seed) :
    reference P hK hc hsmall hC hy h v z-CoolingExecutable.preReserve Q h v P.K G x z.1.2 =
      -CoolingSourceRetainedAccuracy.error (G := G) P hK hc hsmall hC hy h v ((Real.sqrt h)⁻¹ • x) z := by
  rw [CoolingSourceRetainedAccuracy.error_eq_execute]
  rw [CoolingExecutable.execute_value_eq_preReserve_add_reserve]
  unfold reference PrivateCompletedPreReserve.preReference
  change (z.2-(1/2 : ℝ) • CoolingExecutable.reserve Q h v P.K z.1.2)-
      CoolingExecutable.preReserve Q h v P.K G x z.1.2 =
    -(CoolingExecutable.preReserve Q h v P.K G x z.1.2+
      (1/2 : ℝ) • CoolingExecutable.reserve Q h v P.K z.1.2-z.2)
  module

end AcceleratedLogConcave.Root.CoolingPreReserveCoupling
