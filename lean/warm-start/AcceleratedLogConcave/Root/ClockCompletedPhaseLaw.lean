import AcceleratedLogConcave.Root.ClockPhaseGaussianKL
import AcceleratedLogConcave.Root.ClockFinalReferenceLaw
import AcceleratedLogConcave.Root.ClockFinalCorrectionReadout
import AcceleratedLogConcave.Root.OuterRootLiteralScore

/-! The actual completed root coupling followed by the phase's two fresh
Gaussian blocks. The implementation copies the whole original source sample;
the comparison uses the true conditional path and the returned final references.
Its prescribed reference-kernel identification is a separate paired-law join. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal
namespace AcceleratedLogConcave.Root.ClockCompletedPhaseLaw
open Oracle Oracle.TapeLowering Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open ClockChronologicalCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}
local notation "host" => Host P hR hc hsmall clock label
local notation "Source" => (Point d × Point d) × Tape d host
local notation "Sample" => (History P d × Tape d host) × (ClockNoisyLayer.Index P→Point d)
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d
local notation "γ" => stdGaussian (Point d)

def original (z : Sample) : Source := ClockChronologicalCoupling.original P hR hc hsmall clock label z.1

theorem original_measurable : Measurable (original (d:=d) P hR hc hsmall clock label) :=
  (ClockChronologicalCoupling.original_measurable P hR hc hsmall clock label).comp measurable_fst

def sourceInput (z : Source) : Point d × Point d := ((Real.sqrt P.delta) • z.1.1,z.1.2)

theorem sourceInput_measurable : Measurable (sourceInput (d:=d) P hR hc hsmall clock label) :=
  (measurable_fst.fst.const_smul (Real.sqrt P.delta)).prodMk measurable_fst.snd

def sourceRoot (G : Point d→Point d) (z : Source) : Point d :=
  ClockPhysicalReadout.physicalOutput z.1.2
    (ClockRetainedTapeLaw.publicPrefixMeasurableEquiv P hR hc hsmall clock label z.2).1
    (ClockFinalCorrectionReadout.output P hR hc hsmall clock label G z.1.1 z.1.2 z.2)

include hc hsmall in
theorem sourceRoot_measurable (G : Point d→Point d) (hG : Measurable G) :
    Measurable (sourceRoot P hR hc hsmall clock label G) := by
  have hrun := CanonicalTapeMeasurability.program_point_of_measurable host G hG
    (fun _ : Source => ClockRetainedFinalSplice.table P hR hc hsmall clock)
    (fun z : Source => z.1.1) (fun z : Source => z.1.2) (fun z : Source => z.2)
    measurable_const measurable_fst.fst measurable_fst.snd measurable_snd
  have hE : Measurable (fun z : Source =>
      (ClockRetainedTapeLaw.publicPrefixMeasurableEquiv P hR hc hsmall clock label z.2).1) :=
    ((ClockRetainedTapeLaw.publicPrefixMeasurableEquiv P hR hc hsmall clock label (d:=d)).measurable.comp
      (show Measurable (fun z : Source => z.2) from measurable_snd)).fst
  have hP : Measurable (fun z : Source => z.1.2) := measurable_fst.snd
  have hH := (hP.const_smul ClockPublicSetup.noise).add
    (hE.const_smul (-ClockPublicSetup.s))
  exact hP.add ((hrun.sub hH).const_smul ClockPublicSetup.noise)

/-- The physical source readout keeps the literal first Gaussian and the
complete executed root result. -/
theorem sourceRoot_eq_readoutResult (G : Point d→Point d) (p : Point d × Point d)
    (ω : Tape d host) :
    sourceRoot P hR hc hsmall clock label G (p,ω)=
      (ClockPhysicalReadout.readoutResult p.2 ω.2.2.1
        (run host G ⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,p.1,p.2⟩ Env.empty ω)).value := by
  unfold sourceRoot ClockFinalCorrectionReadout.output ClockPhysicalReadout.readoutResult
  apply congrArg (fun e0 => ClockPhysicalReadout.physicalOutput p.2 e0
    (run host G ⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,p.1,p.2⟩ Env.empty ω).value)
  rfl

variable (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
  {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "joint" => ClockFinalBatchCoupling.completedKernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
local notation "obs" => ClockFinalReferenceLaw.referenceObservation (V:=V) P hR hc hsmall clock label hK hC hy
local notation "obsMeas" => ClockFinalReferenceLaw.referenceObservation_measurable P hR hc hsmall clock label hK hC hy hV

/-- Same actual source law, extended by the actual main and final lower joints. -/
def law (ν : Measure (Point d × Point d)) : Measure Sample :=
  joint ∘ₘ (ν.prod (tapeLaw L host))

instance law_probability (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν) := by
  let _ : IsProbabilityMeasure (tapeLaw L host) := tapeLaw_probability L host
  unfold law
  infer_instance

/-- The full input and original tape are preserved, before either fresh phase draw. -/
theorem original_law (ν : Measure (Point d × Point d)) :
    (law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν).map
      (original P hR hc hsmall clock label)=ν.prod (tapeLaw L host) := by
  rw [law,Measure.map_comp _ _ (original_measurable P hR hc hsmall clock label)]
  unfold original
  rw [ClockFinalBatchCoupling.completed_original,Measure.id_comp]

/-- True physical endpoint with the same returned final Gaussian correction.
The deterministic primitive-mean row is handled by quadrature error, not omitted
from the actual program or identified with the exact path. -/
def referenceRoot (z : Sample) : Point d :=
  ClockPublicSetup.s • OuterRootPhysicalPath.rawY hV P.delta_pos hlo hup
    (obs z).1.1.1 (obs z).1.1.2 clock+
    ClockPublicSetup.noise • ClockFinalReferenceLaw.gaussianCorrection
      (V:=V) P hR hc hsmall clock label hK hC hy z

private theorem rawY_measurable : Measurable (fun z : Point d × Point d =>
    OuterRootPhysicalPath.rawY hV P.delta_pos hlo hup z.1 z.2 clock) := by
  let D := OuterRootOriginalData.data hV P.delta_pos hlo hup
  have hm : Measurable (fun z : Point d × Point d =>
      (Numerics.ConditionalSmoothing.jointPath D clock z).2) :=
    ((Numerics.ConditionalSmoothing.continuous_jointPath D).measurable.comp
      (measurable_const.prodMk measurable_id)).snd
  have he : (fun z : Point d × Point d => OuterRootPhysicalPath.rawY hV P.delta_pos hlo hup z.1 z.2 clock)=
      (fun z => (Numerics.ConditionalSmoothing.jointPath D clock z).2) := by
    funext z
    exact ((Numerics.ConditionalSmoothing.jointPath_snd_eq_source D z.1 z.2 clock.property).trans
      (OuterRootLiteralScore.path_eq_rawY hV P.delta_pos hlo hup z.1 z.2 clock.property)).symm
  rw [he]
  exact hm

theorem referenceRoot_measurable : Measurable (referenceRoot P hR hc hsmall clock label hK hC hy hV hlo hup) :=
  ((rawY_measurable P clock hV hlo hup).comp ((obsMeas).fst.fst)).const_smul ClockPublicSetup.s |>.add
    ((ClockFinalReferenceLaw.gaussianCorrection_measurable P hR hc hsmall clock label hK hC hy hV).const_smul ClockPublicSetup.noise)

/-- Literal physical root readout, on the complete original retained tape. -/
def actualRoot (z : Sample) : Point d :=
  sourceRoot P hR hc hsmall clock label (gradient V) (original P hR hc hsmall clock label z)

include hV in
theorem actualRoot_measurable : Measurable (actualRoot (V:=V) P hR hc hsmall clock label) :=
  (sourceRoot_measurable P hR hc hsmall clock label (gradient V)
    (ClockOriginalGradientKernel.originalGradient_measurable hV)).comp
      (original_measurable P hR hc hsmall clock label)

/-- Literal fixed-clock phase on one complete original root sample and the
two new Gaussian blocks. No returned reference enters this implementation. -/
def sourcePhase (Γ : ℝ) (G : Point d→Point d) (z : Source × (Point d × Point d)) :
    (Point d × Point d) × (Point d × Point d) :=
  let inp := sourceInput P hR hc hsmall clock label z.1
  (inp,ClockPhaseGaussianKL.phaseOutput P.delta Γ clock inp.1
    (sourceRoot P hR hc hsmall clock label G z.1) z.2.1 z.2.2)

include hc hsmall in
theorem sourcePhase_measurable (Γ : ℝ) (G : Point d→Point d) (hG : Measurable G) :
    Measurable (sourcePhase P hR hc hsmall clock label Γ G) := by
  have hi := (sourceInput_measurable (d:=d) P hR hc hsmall clock label).comp
    (show Measurable (fun z : Source × (Point d × Point d) => z.1) from measurable_fst)
  have hw := (sourceRoot_measurable P hR hc hsmall clock label G hG).comp
    (show Measurable (fun z : Source × (Point d × Point d) => z.1) from measurable_fst)
  exact hi.prodMk ((hi.fst.add ((hw.add measurable_snd.fst).const_smul
    (Real.sqrt (2*P.delta^2)*(ClockPublicSetup.s*(clock:ℝ))))).prodMk
      ((hw.const_smul (Real.exp (-Γ))).add (measurable_snd.snd.const_smul
        (Real.sqrt (1-Real.exp (-2*Γ))))))

/-- Actual full-source fixed-clock phase law, retaining its physical input. -/
def implementedLaw (ν : Measure (Point d × Point d)) (Γ : ℝ) (G : Point d→Point d) :
    Measure ((Point d × Point d) × (Point d × Point d)) :=
  (((ν.prod (tapeLaw L host)).prod ((γ).prod γ))).map
    (sourcePhase P hR hc hsmall clock label Γ G)

/-- Projecting the actual augmented root and fresh pair of Gaussians is exactly
the implementation law on the original full tape. -/
theorem implemented_projection (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν]
    (Γ : ℝ) (G : Point d→Point d) (hG : Measurable G) :
    ((law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν).prod ((γ).prod γ)).map
      (fun z => sourcePhase P hR hc hsmall clock label Γ G
        (original P hR hc hsmall clock label z.1,z.2))=
      implementedLaw P hR hc hsmall clock label ν Γ G := by
  have hp : MeasurePreserving (original P hR hc hsmall clock label)
      (law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν)
      (ν.prod (tapeLaw L host)) :=
    ⟨original_measurable P hR hc hsmall clock label,
      original_law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν⟩
  have hprod := hp.prod (MeasurePreserving.id ((γ).prod γ))
  have hm := sourcePhase_measurable P hR hc hsmall clock label Γ G hG
  calc
    _ = (((law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν).prod ((γ).prod γ)).map
        (Prod.map (original P hR hc hsmall clock label) id)).map
          (sourcePhase P hR hc hsmall clock label Γ G) := (Measure.map_map hm hprod.measurable).symm
    _ = _ := congrArg (fun μ => μ.map (sourcePhase P hR hc hsmall clock label Γ G)) hprod.map_eq

/-- Exact anchored-tape implementation used by the public uniform-clock
phase. The whole transported source tape and both fresh draws are unchanged. -/
theorem sourcePhase_anchor_eq_output (Γ : ℝ) (G : Point d→Point d)
    (u : UniformValue) (x : Point d × Point d)
    (ω : Tape d (ClockRetainedFinalSplice.code P hR hc hsmall ClockRetainedTapeTransport.anchorClock label))
    (z1 z2 : Point d) :
    let c := ClockUniformDraw.clockOfUniform u
    sourcePhase P hR hc hsmall c label Γ G
      ((ClockFinitePhaseKernel.normalizedInput P x,
        ClockRetainedTapeTransport.anchorTapeEquiv P hR hc hsmall c d label ω),(z1,z2))=
      (x,ClockFinitePhaseKernel.output P hR hc hsmall label Γ G (x,(((u,ω),z1),z2))) := by
  dsimp only
  let c := ClockUniformDraw.clockOfUniform u
  let t := ClockRetainedTapeTransport.anchorTapeEquiv P hR hc hsmall c d label ω
  have hi : sourceInput P hR hc hsmall c label (ClockFinitePhaseKernel.normalizedInput P x,t)=x := by
    apply Prod.ext
    · change (Real.sqrt P.delta) • ((Real.sqrt P.delta)⁻¹ • x.1)=x.1
      rw [smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr P.delta_pos).ne',one_smul]
    · rfl
  have hw : ClockPhysicalExecutionKernel.output P hR hc hsmall label G
      (ClockFinitePhaseKernel.normalizedInput P x,(u,ω))=
      sourceRoot P hR hc hsmall c label G (ClockFinitePhaseKernel.normalizedInput P x,t) := by
    rw [sourceRoot_eq_readoutResult]
    exact ClockPhysicalExecutionKernel.output_transport P hR hc hsmall label G
      (ClockFinitePhaseKernel.normalizedInput P x,(u,ω))
  change (sourceInput P hR hc hsmall c label (ClockFinitePhaseKernel.normalizedInput P x,t),
    ClockPhaseGaussianKL.phaseOutput P.delta Γ c
      (sourceInput P hR hc hsmall c label (ClockFinitePhaseKernel.normalizedInput P x,t)).1
      (sourceRoot P hR hc hsmall c label G (ClockFinitePhaseKernel.normalizedInput P x,t)) z1 z2)=_
  rw [hi,← hw]
  rfl

include hV hlo hup in
/-- The actual completed-source conditional gives a phase KL bound while
retaining the physical original input. No reference-kernel identity or current
accuracy conclusion is assumed in this reserve/refresh step. -/
theorem completed_phase_KL (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν]
    {Γ : ℝ} (hΓ : 0<Γ) :
    let μ := law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν
    let inp := fun z : Sample => sourceInput P hR hc hsmall clock label (original P hR hc hsmall clock label z)
    klDiv ((μ.prod ((γ).prod γ)).map (fun z =>
      (inp z.1,ClockPhaseGaussianKL.phaseOutput P.delta Γ clock (inp z.1).1
        (referenceRoot P hR hc hsmall clock label hK hC hy hV hlo hup z.1) z.2.1 z.2.2)))
      ((μ.prod ((γ).prod γ)).map (fun z =>
        (inp z.1,ClockPhaseGaussianKL.phaseOutput P.delta Γ clock (inp z.1).1
          (actualRoot (V:=V) P hR hc hsmall clock label z.1) z.2.1 z.2.2)))≤
      ∫⁻ z,ENNReal.ofReal (‖referenceRoot P hR hc hsmall clock label hK hC hy hV hlo hup z-
        actualRoot (V:=V) P hR hc hsmall clock label z‖^2/(2*(1-Real.exp (-2*Γ)))) ∂μ := by
  dsimp only
  have hi := (sourceInput_measurable (d:=d) P hR hc hsmall clock label).comp
    (original_measurable P hR hc hsmall clock label)
  exact ClockPhaseGaussianKL.phase_retained _ P.delta hΓ _ _ _
    (referenceRoot_measurable P hR hc hsmall clock label hK hC hy hV hlo hup)
    (actualRoot_measurable P hR hc hsmall clock label hV) hi.fst
    (fun _ => (clock:ℝ)) measurable_const _ hi
/-- The retained comparison bound with its implemented side already
identified with the actual full-source fixed-clock phase law. -/
theorem implemented_phase_KL (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν]
    {Γ : ℝ} (hΓ : 0<Γ) :
    let μ := law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν
    let inp := fun z : Sample => sourceInput P hR hc hsmall clock label (original P hR hc hsmall clock label z)
    klDiv ((μ.prod ((γ).prod γ)).map (fun z =>
      (inp z.1,ClockPhaseGaussianKL.phaseOutput P.delta Γ clock (inp z.1).1
        (referenceRoot P hR hc hsmall clock label hK hC hy hV hlo hup z.1) z.2.1 z.2.2)))
      (implementedLaw P hR hc hsmall clock label ν Γ (gradient V))≤
      ∫⁻ z,ENNReal.ofReal (‖referenceRoot P hR hc hsmall clock label hK hC hy hV hlo hup z-
        actualRoot (V:=V) P hR hc hsmall clock label z‖^2/(2*(1-Real.exp (-2*Γ)))) ∂μ := by
  dsimp only
  have he := implemented_projection P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν Γ
    (gradient V) (ClockOriginalGradientKernel.originalGradient_measurable hV)
  calc
    _ = klDiv _ (((law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν).prod ((γ).prod γ)).map
        (fun z => sourcePhase P hR hc hsmall clock label Γ (gradient V)
          (original P hR hc hsmall clock label z.1,z.2))) := congrArg (fun μ => klDiv _ μ) he.symm
    _ ≤ _ := completed_phase_KL P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν hΓ
end AcceleratedLogConcave.Root.ClockCompletedPhaseLaw
