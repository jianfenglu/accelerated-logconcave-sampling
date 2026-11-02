import AcceleratedLogConcave.Conditional.RecursiveReferenceFamily
import AcceleratedLogConcave.Conditional.MeanReferenceVarianceAssembly

/-! Sharp directional centering innovation on the actual source flow. This
uses the momentum equation and stationarity, preserving the conditional-mean
covariance rather than replacing it by a dimension or operator-norm bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory ProbabilityTheory Filter
open scoped ContDiff ENNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional.RecursiveReference

/-- Scalar Jensen on a stationary time-one average, with the required product
integrability established from the actual invariant measure. -/
private theorem stationary_timeAverage_sq_le
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {flow : ℝ → Ω → Ω} (hc : Continuous (fun q : ℝ × Ω ↦ flow q.1 q.2))
    (hp : ∀ τ, MeasurePreserving (flow τ) μ μ)
    {f : Ω → ℝ} (hf : Continuous f) (hi : Integrable (fun z ↦ (f z)^2) μ) :
    (∫ z, (∫ τ in (0 : ℝ)..1, f (flow τ z))^2 ∂μ) ≤ ∫ z, (f z)^2 ∂μ := by
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  let Q : ℝ × Ω → ℝ := fun q ↦ (f (flow q.1 q.2))^2
  have hcQ : Continuous Q := (hf.comp hc).pow 2
  have hQi (τ : ℝ) : (∫ z, Q (τ,z) ∂μ) = ∫ z, (f z)^2 ∂μ :=
    MeanReferenceVariance.integral_comp_preserving (hp τ) (hf.pow 2).stronglyMeasurable
  have hQ : Integrable Q (ν.prod μ) := by
    apply (integrable_prod_iff hcQ.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun τ ↦ (hp τ).integrable_comp_of_integrable hi), ?_⟩
    have he : (fun τ ↦ ∫ z, ‖Q (τ,z)‖ ∂μ) = fun _ ↦ ∫ z, (f z)^2 ∂μ := by
      funext τ
      simp only [Q, Real.norm_eq_abs, abs_pow, sq_abs]
      exact hQi τ
    rw [he]
    exact integrable_const _
  have hint : Integrable (fun z ↦ ∫ τ, Q (τ,z) ∂ν) μ := hQ.integral_prod_right
  calc
    _ ≤ ∫ z, ∫ τ, Q (τ,z) ∂ν ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun _ ↦ sq_nonneg _)) hint
      exact Eventually.of_forall fun z ↦ by
        have h := Centering.norm_intervalIntegral_sq_le
          (hf.comp (hc.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ ↦ z)))))
          (by norm_num : (0 : ℝ) ≤ 1)
        simpa only [Real.norm_eq_abs, sq_abs, one_mul,
          intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), Q, ν, Function.comp_def, id_eq] using h
    _ = ∫ τ, ∫ z, Q (τ,z) ∂μ ∂ν := (integral_integral_swap hQ).symm
    _ = ∫ z, (f z)^2 ∂μ := by simp [hQi,ν]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
variable {F : EuclideanSpace ℝ ι → ℝ} {ell : ℝ} (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)

/-- The exact centering momentum innovation has the sharp directional
conditional-mean covariance budget. All hypotheses of the generic stationary
average estimate are discharged by the actual source flow. -/
theorem sourceCentering_directional_innovation_le
    (theta : SourceParameters E ell) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) (v : E) :
    (∫ z, ⟪v, theta.width •
      ((Centering.sourceCenteringFlow hF hell hlo hup theta.center theta.radius_pos hb hb1
        theta.small theta.width_pos z 1).snd-z.snd)⟫^2
      ∂Kinetic.coupledPhaseMeasure (interpolationLaw F theta.center theta.radius b)) ≤
      ∫ y, ⟪v, conditionalMean F theta.center theta.radius b y-
        conditionalMean F theta.center theta.radius 0 0⟫^2
          ∂interpolationLaw F theta.center theta.radius b := by
  let ξ := interpolationLaw F theta.center theta.radius b
  let μ := Kinetic.coupledPhaseMeasure ξ
  let u := conditionalMean F theta.center theta.radius 0 0
  let M := conditionalMean F theta.center theta.radius b
  let flow := Centering.sourceCenteringFlow hF hell hlo hup theta.center theta.radius_pos hb hb1
    theta.small theta.width_pos
  let f : Centering.Phase E → ℝ := fun z ↦ ⟪v, M z.fst-u⟫
  let := interpolationLaw_isProbabilityMeasure hF hlo theta.center theta.radius b
  have hM : Continuous M :=
    (contDiff_one_conditionalMean hF hlo hup theta.center theta.radius (by linarith) hb1).continuous
  have hf : Continuous f := continuous_const.inner
    ((hM.comp (WithLp.prod_continuous_ofLp 2 E E).fst).sub continuous_const)
  have hflow : Continuous (fun q : ℝ × Centering.Phase E ↦ flow q.2 q.1) := by
    have hc := (Centering.continuous_sourceCenteringFlow_parameters hF hell hlo hup hb hb1).comp
      ((continuous_const : Continuous (fun _ : ℝ × Centering.Phase E ↦ theta)).prodMk
        (continuous_fst.prodMk continuous_snd))
    exact hc
  have hpres (τ : ℝ) : MeasurePreserving (fun z ↦ flow z τ) μ μ :=
    Centering.sourceCenteringHomeomorph_measurePreserving hF hell hlo hup theta.center
      theta.radius_pos hb hb1 theta.small theta.width_pos τ
  have hfst : MeasurePreserving (fun z : Centering.Phase E ↦ z.fst) μ ξ := by
    refine ⟨(WithLp.prod_continuous_ofLp 2 E E).fst.measurable, ?_⟩
    dsimp only [μ]
    rw [Kinetic.coupledPhaseMeasure,Measure.map_map (by fun_prop) (by fun_prop)]
    change (ξ.prod (stdGaussian E)).map Prod.fst = ξ
    simp
  have hmem : MemLp (fun y ↦ M y-u) 2 ξ :=
    (memLp_two_conditionalMean hF hell hlo hup theta.center theta.radius_pos hb hb1 theta.small).sub
      (memLp_const u)
  have hfi : Integrable (fun z ↦ (f z)^2) μ :=
    ((hmem.const_inner v).comp_measurePreserving hfst).integrable_sq
  have hbound := stationary_timeAverage_sq_le hflow hpres hf hfi
  have heq (z : Centering.Phase E) :
      ⟪v, theta.width • ((flow z 1).snd-z.snd)⟫ = ∫ τ in (0 : ℝ)..1, f (flow z τ) := by
    have hi := Centering.sourceCenteringFlow_output_identity hF hell hlo hup theta.center
      theta.radius_pos hb hb1 theta.small theta.width_pos z
    have hMc : Continuous (fun τ ↦ M (flow z τ).fst) :=
      hM.comp ((WithLp.prod_continuous_ofLp 2 E E).fst.comp
        (hflow.comp (continuous_id.prodMk continuous_const)))
    have hfcurve : Continuous (fun τ ↦ M (flow z τ).fst-u) := hMc.sub continuous_const
    have hv : theta.width • ((flow z 1).snd-z.snd) =
        ∫ τ in (0 : ℝ)..1, (M (flow z τ).fst-u) := by
      rw [smul_sub,intervalIntegral.integral_sub (hMc.intervalIntegrable 0 1)
        (continuous_const.intervalIntegrable 0 1),intervalIntegral.integral_const]
      simp only [sub_zero,one_smul]
      apply sub_eq_sub_iff_add_eq_add.mpr
      calc
        theta.width • (flow z 1).snd + u = u + theta.width • (flow z 1).snd := add_comm _ _
        _ = theta.width • z.snd + ∫ τ in (0 : ℝ)..1, M (flow z τ).fst := hi.symm
        _ = (∫ τ in (0 : ℝ)..1, M (flow z τ).fst) + theta.width • z.snd := add_comm _ _
    rw [hv]
    change (innerSL ℝ v) (∫ τ in (0 : ℝ)..1, (M (flow z τ).fst-u)) = _
    rw [← (innerSL ℝ v).intervalIntegral_comp_comm (hfcurve.intervalIntegrable 0 1)]
    rfl
  change (∫ z, ⟪v, theta.width • ((flow z 1).snd-z.snd)⟫^2 ∂μ) ≤
    ∫ y, ⟪v, M y-u⟫^2 ∂ξ
  simp_rw [heq]
  apply hbound.trans_eq
  exact MeanReferenceVariance.integral_comp_preserving hfst
    ((continuous_const.inner (hM.sub continuous_const)).pow 2).stronglyMeasurable


open Numerics Numerics.MeanFlowLp Numerics.AffineGraph MeanReferenceLayer

/-- The actual parent execution starts its centering path from the independent
source position and designated Gaussian G0. -/
theorem initialCenterPhase_preserving {m : ℕ} (d : Data ι m) (C : Children d) :
    MeasurePreserving
      (fun z : MeanReferenceVariance.Execution ι m ↦
        WithLp.toLp 2 (z.1.2.1,active d C z.1 none))
      (averagedJoint d C)
      (Kinetic.coupledPhaseMeasure (Numerics.MeanBenchmarkCoupling.positionLaw d)) := by
  have hs : MeasurePreserving (splitState d C)
      ((stdGaussian E).prod (freshLaw d))
      ((MeanReferenceLayer.baseLaw d).prod (Measure.pi (fun _ : Fin m ↦ stdGaussian E))) :=
    ⟨measurable_splitState d C,splitState_law d C⟩
  have hpair := measurePreserving_fst.comp
    (measurePreserving_fst.comp (hs.comp (MeanReferenceVariance.host_preserving d C)))
  have hLp : MeasurePreserving (MeasurableEquiv.toLp 2 (E × E))
      ((Numerics.MeanBenchmarkCoupling.positionLaw d).prod (stdGaussian E))
      (Kinetic.coupledPhaseMeasure (Numerics.MeanBenchmarkCoupling.positionLaw d)) :=
    ⟨(MeasurableEquiv.toLp 2 (E × E)).measurable,rfl⟩
  exact hLp.comp hpair

/-- The sharp centering budget occurs in the actual assembled recursive
execution. It does not depend on a directional bound for the children. -/
theorem assembly_center_directional_le {m : ℕ} (d : Data ι m) (C : Children d) (v : E) :
    (d.sigma/2)^2 * (∫ z, ⟪v,MeanReferenceVariance.centerIncrement d C z⟫^2
      ∂averagedJoint d C) ≤
      ∫ y, ⟪v,conditionalMean d.F d.x d.r (backwardEnd d.G.R) y-
        conditionalMean d.F d.x d.r 0 0⟫^2
        ∂Numerics.MeanBenchmarkCoupling.positionLaw d := by
  let theta : SourceParameters E d.ell :=
    ⟨(d.x,d.r,d.sigma/2),d.hr,half_pos d.hsigma,d.hsmall⟩
  let flow := Centering.sourceCenteringFlow d.hF d.hell d.hlo d.hup d.x d.hr
    d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one d.hsmall (half_pos d.hsigma)
  let f : Centering.Phase E → ℝ := fun z ↦
    ⟪v,(d.sigma/2) • ((flow z 1).snd-z.snd)⟫^2
  have hcflow : Continuous (fun z : Centering.Phase E ↦ flow z 1) :=
    (Centering.sourceCenteringHomeomorph d.hF d.hell d.hlo d.hup d.x d.hr
      d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one d.hsmall (half_pos d.hsigma) 1).continuous
  have hcf : Continuous f := by
    apply Continuous.pow _ 2
    exact continuous_const.inner
      ((((WithLp.prod_continuous_ofLp 2 E E).snd.comp hcflow).sub
        (WithLp.prod_continuous_ofLp 2 E E).snd).const_smul (d.sigma/2))
  have heq : (d.sigma/2)^2 * (∫ z, ⟪v,MeanReferenceVariance.centerIncrement d C z⟫^2
      ∂averagedJoint d C) =
      ∫ z, f (WithLp.toLp 2 (z.1.2.1,active d C z.1 none)) ∂averagedJoint d C := by
    simp only [f,inner_smul_right,mul_pow,integral_const_mul]
    rfl
  rw [heq,MeanReferenceVariance.integral_comp_preserving
    (initialCenterPhase_preserving d C) hcf.stronglyMeasurable]
  exact sourceCentering_directional_innovation_le d.hF d.hell d.hlo d.hup theta
    d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one v


/-- Every actual final child center samples the same stationary source
position, before the physical affine center map is applied. -/
theorem statePosition_preserving {m : ℕ} (d : Data ι m) (i : Fin m) :
    MeasurePreserving
      (fun b : BaseState ι ↦ (CenteringFlowLp.phase (kernelData d)
        (d.sigma/2) (half_pos d.hsigma) (GaussLegendre.node m i)
          (WithLp.toLp 2 b.1)).fst)
      (MeanReferenceLayer.baseLaw d) (Numerics.MeanBenchmarkCoupling.positionLaw d) := by
  have hLp : MeasurePreserving (MeasurableEquiv.toLp 2 (E × E))
      ((Numerics.MeanBenchmarkCoupling.positionLaw d).prod (stdGaussian E))
      (CenteringFlowLp.seedMeasure (kernelData d)) :=
    ⟨(MeasurableEquiv.toLp 2 (E × E)).measurable,rfl⟩
  exact (CenteringFlowLp.position_preserving (kernelData d)).comp
    ((CenteringFlowLp.phase_preserving (kernelData d) (d.sigma/2) (half_pos d.hsigma)
      (GaussLegendre.node m i)).comp (hLp.comp measurePreserving_fst))

/-- Integrating a genuine scalar observable at the actual child center uses
the stationary source law, uniformly over the entire fixed final inventory. -/
theorem integral_stateCenter {m : ℕ} (d : Data ι m) (i : Fin m) (B : E → ℝ)
    (hB : StronglyMeasurable B) :
    (∫ b, B (stateCenter d i b) ∂MeanReferenceLayer.baseLaw d) =
      ∫ y, B (d.x+(d.r*backwardEnd d.G.R) • y)
        ∂Numerics.MeanBenchmarkCoupling.positionLaw d :=
  MeanReferenceVariance.integral_comp_preserving (statePosition_preserving d i)
    (hB.comp_measurable (show Measurable (fun y : E ↦ d.x+(d.r*backwardEnd d.G.R) • y) by fun_prop))


/-- Standalone directional innovation of a retained family under its specified
Gaussian input. The inner law retains the supplied input p. -/
def directionalMoment (C : Family ι ell) (theta : SourceParameters E ell) (v : E) : ℝ :=
  ∫ p : E, ∫ p' : E, ⟪v,p'-p⟫^2 ∂C.kernel (theta,p) ∂stdGaussian E

omit [DecidableEq ι] in
/-- Genuine square integrability of the retained pair, established from its
two Gaussian marginals. This is used for Fubini, not as a curvature bound. -/
theorem directionalPair_integrable (C : Family ι ell) (theta : SourceParameters E ell) (v : E) :
    Integrable (fun z : E × E ↦ ⟪v,z.2-z.1⟫^2)
      ((stdGaussian E) ⊗ₘ C.kernel.comap (fun p ↦ (theta,p)) measurable_prodMk_left) := by
  let Q := C.kernel.comap (fun p ↦ (theta,p)) measurable_prodMk_left
  let := C.markov
  let : IsMarkovKernel Q := by dsimp [Q]; infer_instance
  have hf : MeasurePreserving (Prod.fst : E × E → E) ((stdGaussian E) ⊗ₘ Q) (stdGaussian E) :=
    ⟨measurable_fst,Measure.fst_compProd _ _⟩
  have hs : MeasurePreserving (Prod.snd : E × E → E) ((stdGaussian E) ⊗ₘ Q) (stdGaussian E) := by
    refine ⟨measurable_snd, ?_⟩
    rw [← Measure.snd,Measure.snd_compProd]
    exact C.invariant theta
  exact (((IsGaussian.memLp_two_id.comp_measurePreserving hs).sub
    (IsGaussian.memLp_two_id.comp_measurePreserving hf)).const_inner v).integrable_sq

omit [DecidableEq ι] in
theorem directionalMoment_eq_integral_pair (C : Family ι ell)
    (theta : SourceParameters E ell) (v : E) :
    directionalMoment C theta v =
      ∫ z : E × E, ⟪v,z.2-z.1⟫^2
        ∂((stdGaussian E) ⊗ₘ C.kernel.comap (fun p ↦ (theta,p)) measurable_prodMk_left) := by
  let := C.markov
  rw [Measure.integral_compProd (directionalPair_integrable C theta v)]
  rfl

/-- The standalone retained innovation is precisely the actual recursive
assembly innovation, including the original parent input on both sides. -/
theorem referenceFamily_directionalMoment_assembly {m : ℕ}
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (q : ℝ) (hq : 1/2 < q)
    (theta : SourceParameters E ell) (v : E) :
    theta.width^2 * directionalMoment (referenceFamily hF hell hlo hup G hm t ht q) theta v =
      let d := TerminalChildrenParentFamily.data hF hell hlo hup G theta
      let C := sourceChildren hF hell hlo hup G hm
        (referenceFamily hF hell hlo hup G hm t ht (q-t)) theta
      ∫ z, ⟪v,theta.width • (recombine d C z.1 z.2-z.1.1)⟫^2 ∂averagedJoint d C := by
  have hr := referenceFamily_retained hF hell hlo hup G hm t ht q hq theta
  dsimp only at hr ⊢
  rw [directionalMoment_eq_integral_pair,← hr,
    integral_map (measurable_fst.fst.prodMk (continuous_recombine _ _).measurable).aemeasurable
      (by fun_prop)]
  simp only [inner_smul_right,mul_pow,integral_const_mul]

end AcceleratedLogConcave.Conditional.RecursiveReference
