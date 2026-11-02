import AcceleratedLogConcave.Root.ClockCompletedPhaseLaw
import AcceleratedLogConcave.Probability.PathEntropy

/-! Jointly measurable fixed-uniform sections of the literal public phase.
Their average is exactly the public phase kernel. No clock-indexed coupling is
selected: only the already measurable implementation sections are constructed. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace AcceleratedLogConcave.Root.ClockPhaseSections
open Oracle Oracle.TapeLowering Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (label : ℕ) {d : ℕ}
local notation "host" => ClockRetainedFinalSplice.code P hR hc hsmall ClockRetainedTapeTransport.anchorClock label
local notation "Rest" => Tape d host × (Point d × Point d)
local notation "Input" => Point d × Point d
local notation "γ" => stdGaussian (Point d)
local notation "LA" => ClockPublicSetupTapeLaw.standardLaws d
local instance tape_probability : IsProbabilityMeasure (tapeLaw LA host) := tapeLaw_probability LA host

def restLaw : Measure Rest := (tapeLaw LA host).prod ((γ).prod γ)

instance rest_probability : IsProbabilityMeasure (restLaw (d:=d) P hR hc hsmall label) := by
  unfold restLaw
  infer_instance

def output (Γ : ℝ) (G : Point d→Point d) (z : (Input × UniformValue) × Rest) : Input :=
  ClockFinitePhaseKernel.output P hR hc hsmall label Γ G
    (z.1.1,(((z.1.2,z.2.1),z.2.2.1),z.2.2.2))

theorem output_measurable (Γ : ℝ) (G : Point d→Point d) (hG : Measurable G) :
    Measurable (output P hR hc hsmall label Γ G) :=
  (ClockFinitePhaseKernel.output_measurable P hR hc hsmall label Γ G hG).comp
    (show Measurable (fun z : (Input × UniformValue) × Rest =>
      (z.1.1,(((z.1.2,z.2.1),z.2.2.1),z.2.2.2))) by fun_prop)

/-- Both the entering physical phase point and the true uniform primitive are
parameters of this single measurable kernel. -/
def sections (Γ : ℝ) (G : Point d→Point d) (hG : Measurable G) :
    Kernel (Input × UniformValue) Input :=
  Channels.freshKernel (restLaw (d:=d) P hR hc hsmall label)
    (output P hR hc hsmall label Γ G) (output_measurable P hR hc hsmall label Γ G hG)

instance sections_markov (Γ : ℝ) (G : Point d→Point d) (hG : Measurable G) :
    IsMarkovKernel (sections P hR hc hsmall label Γ G hG) := by unfold sections; infer_instance

/-- Only reassociate the same original uniform, full root tape and fresh pair. -/
def splitDraw (z : ClockFinitePhaseKernel.Draw P hR hc hsmall (d:=d) label) : UniformValue × Rest :=
  (z.1.1.1,(z.1.1.2,(z.1.2,z.2)))

theorem splitDraw_preserving : MeasurePreserving (splitDraw (d:=d) P hR hc hsmall label)
    (ClockFinitePhaseKernel.drawLaw P hR hc hsmall label)
    ((volume : Measure UniformValue).prod (restLaw (d:=d) P hR hc hsmall label)) :=
  (measurePreserving_prodAssoc (volume : Measure UniformValue) (tapeLaw LA host) ((γ).prod γ)).comp
    (measurePreserving_prodAssoc ((volume : Measure UniformValue).prod (tapeLaw LA host)) γ γ)

private theorem fresh_product_comp {X U Z Y : Type*} [MeasurableSpace X] [MeasurableSpace U]
    [MeasurableSpace Z] [MeasurableSpace Y] (μ : Measure U) [SFinite μ] (ν : Measure Z)
    [IsProbabilityMeasure ν] (f : (X × U) × Z→Y) (hf : Measurable f) (x : X) :
    (μ.prod ν).map (fun z => f ((x,z.1),z.2))=
      ((Channels.freshKernel ν f hf).comap (fun u => (x,u)) measurable_prodMk_left) ∘ₘ μ := by
  have hm : Measurable (fun z : U × Z => f ((x,z.1),z.2)) :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  ext s hs
  rw [Measure.map_apply hm hs,Measure.prod_apply (hs.preimage hm),Measure.bind_apply hs (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro u
  change ν ((fun z => f ((x,u),z)) ⁻¹' s)=
    (ν.map (fun z => f ((x,u),z))) s
  exact (Measure.map_apply (show Measurable (fun z : Z => f ((x,u),z)) from
    hf.comp measurable_prodMk_left) hs).symm

/-- Averaging the measurable sections gives exactly the actual public phase
kernel, with the genuine uniform primitive and every full tape coordinate. -/
theorem kernel_eq_average (Γ : ℝ) (G : Point d→Point d) (hG : Measurable G) (x : Input) :
    ClockFinitePhaseKernel.kernel P hR hc hsmall label Γ G hG x=
      ((sections P hR hc hsmall label Γ G hG).comap (fun u => (x,u)) measurable_prodMk_left) ∘ₘ
        (volume : Measure UniformValue) := by
  have hm : Measurable (fun z : UniformValue × Rest => output P hR hc hsmall label Γ G ((x,z.1),z.2)) :=
    (output_measurable P hR hc hsmall label Γ G hG).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  calc
    _ = ((ClockFinitePhaseKernel.drawLaw P hR hc hsmall label).map
        (splitDraw P hR hc hsmall label)).map
          (fun z => output P hR hc hsmall label Γ G ((x,z.1),z.2)) := by
      rw [Measure.map_map hm (splitDraw_preserving P hR hc hsmall label).measurable]
      rfl
    _ = ((volume : Measure UniformValue).prod (restLaw (d:=d) P hR hc hsmall label)).map
        (fun z => output P hR hc hsmall label Γ G ((x,z.1),z.2)) :=
      congrArg (fun μ => μ.map (fun z => output P hR hc hsmall label Γ G ((x,z.1),z.2)))
        (splitDraw_preserving P hR hc hsmall label).map_eq
    _ = _ := fresh_product_comp volume (restLaw (d:=d) P hR hc hsmall label) _
      (output_measurable P hR hc hsmall label Γ G hG) x
def inputScale (x : Input) : Input := ((Real.sqrt P.delta) • x.1,x.2)

theorem inputScale_measurable : Measurable (inputScale (d:=d) P) :=
  (measurable_fst.const_smul (Real.sqrt P.delta)).prodMk measurable_snd

private theorem mapped_fresh_joint {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace W] (μ : Measure X) [SFinite μ]
    (ν : Measure Z) [IsProbabilityMeasure ν] (f : X→Y) (hf : Measurable f)
    (g : Y × Z→W) (hg : Measurable g) :
    (μ.map f) ⊗ₘ Channels.freshKernel ν g hg =
      (μ.prod ν).map (fun z => (f z.1,g (f z.1,z.2))) := by
  rw [Channels.compProd_freshKernel]
  have hp : (μ.map f).prod ν=(μ.prod ν).map (Prod.map f id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map μ ν hf measurable_id
  rw [hp,Measure.map_map (measurable_fst.prodMk hg) (hf.prodMap measurable_id)]
  rfl

private theorem implemented_anchor_map (Γ : ℝ) (G : Point d→Point d) (hG : Measurable G)
    (u : UniformValue) (ν : Measure Input) [IsProbabilityMeasure ν] :
    ClockCompletedPhaseLaw.implementedLaw P hR hc hsmall (ClockUniformDraw.clockOfUniform u) label ν Γ G=
      (ν.prod (restLaw (d:=d) P hR hc hsmall label)).map (fun z =>
        ClockCompletedPhaseLaw.sourcePhase P hR hc hsmall (ClockUniformDraw.clockOfUniform u) label Γ G
          ((z.1,ClockRetainedTapeTransport.anchorTapeEquiv P hR hc hsmall
            (ClockUniformDraw.clockOfUniform u) d label z.2.1),z.2.2)) := by
  have hl : Probability.CanonicalNativeTapeLaw.primitiveLaws d=LA := rfl
  unfold ClockCompletedPhaseLaw.implementedLaw
  rw [hl]
  let c := ClockUniformDraw.clockOfUniform u
  let pc := ClockRetainedFinalSplice.code P hR hc hsmall c label
  let _ : IsProbabilityMeasure (tapeLaw LA pc) := tapeLaw_probability LA pc
  let noise := (γ).prod γ
  let T := ClockRetainedTapeTransport.anchorTapeEquiv P hR hc hsmall c d label
  have ht : MeasurePreserving T (tapeLaw LA host) (tapeLaw LA pc) :=
    ⟨T.measurable,ClockRetainedTapeTransport.map_anchorTapeLaw P hR hc hsmall c d label LA⟩
  let g : Input × (Tape d pc × (Point d × Point d))→Input × Input := fun z =>
    ClockCompletedPhaseLaw.sourcePhase P hR hc hsmall c label Γ G ((z.1,z.2.1),z.2.2)
  have hg : Measurable g := (ClockCompletedPhaseLaw.sourcePhase_measurable P hR hc hsmall c label Γ G hG).comp
    (show Measurable (fun z : Input × (Tape d pc × (Point d × Point d)) => ((z.1,z.2.1),z.2.2)) by fun_prop)
  have hassoc := measurePreserving_prodAssoc ν (tapeLaw LA pc) noise
  have hmap := (MeasurePreserving.id ν).prod (ht.prod (MeasurePreserving.id noise))
  calc
    _ = (ν.prod ((tapeLaw LA pc).prod noise)).map g := by
      rw [← hassoc.map_eq,Measure.map_map hg hassoc.measurable]
      rfl
    _ = _ := by
      rw [← hmap.map_eq,Measure.map_map hg hmap.measurable]
      rfl

/-- The concrete completed law's implemented fixed-clock readout is the
actual measurable public section, at the physical input law. This retains the
input/output joint law, rather than merely identifying an output marginal. -/
theorem implemented_joint_section (Γ : ℝ) (G : Point d→Point d) (hG : Measurable G)
    (u : UniformValue) (ν : Measure Input) [IsProbabilityMeasure ν] :
    ClockCompletedPhaseLaw.implementedLaw P hR hc hsmall (ClockUniformDraw.clockOfUniform u) label ν Γ G=
      (ν.map (inputScale P)) ⊗ₘ
        ((sections P hR hc hsmall label Γ G hG).comap (fun x => (x,u)) measurable_prodMk_right) := by
  have hleft := implemented_anchor_map P hR hc hsmall label Γ G hG u ν
  have hF : Measurable (fun z : Input × Rest => output P hR hc hsmall label Γ G ((z.1,u),z.2)) :=
    (output_measurable P hR hc hsmall label Γ G hG).comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hk : (sections P hR hc hsmall label Γ G hG).comap (fun x => (x,u)) measurable_prodMk_right=
      Channels.freshKernel (restLaw (d:=d) P hR hc hsmall label)
        (fun z : Input × Rest => output P hR hc hsmall label Γ G ((z.1,u),z.2)) hF := by
    ext x : 1
    rfl
  rw [hk,mapped_fresh_joint ν (restLaw (d:=d) P hR hc hsmall label)
    (inputScale P) (inputScale_measurable P) _ hF]
  calc
    _ = _ := hleft
    _ = _ := by
      apply Measure.map_congr
      apply Filter.Eventually.of_forall
      intro z
      have hi : ClockFinitePhaseKernel.normalizedInput P (inputScale P z.1)=z.1 := by
        apply Prod.ext
        · change (Real.sqrt P.delta)⁻¹ • ((Real.sqrt P.delta) • z.1.1)=z.1.1
          rw [smul_smul,inv_mul_cancel₀ (Real.sqrt_pos.mpr P.delta_pos).ne',one_smul]
        · rfl
      have he := ClockCompletedPhaseLaw.sourcePhase_anchor_eq_output P hR hc hsmall label Γ G u
        (inputScale P z.1) z.2.1 z.2.2.1 z.2.2.2
      rw [hi] at he
      exact he
private theorem mixture_KL {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] (μ : Measure U) [IsFiniteMeasure μ]
    (κ η : Kernel U Y) [IsMarkovKernel κ] [IsMarkovKernel η] :
    InformationTheory.klDiv (κ ∘ₘ μ) (η ∘ₘ μ)≤
      ∫⁻ u,InformationTheory.klDiv (κ u) (η u) ∂μ := by
  have h := InformationTheory.klDiv_map_le (μ ⊗ₘ κ) (μ ⊗ₘ η) measurable_snd
  change InformationTheory.klDiv (μ ⊗ₘ κ).snd (μ ⊗ₘ η).snd≤_ at h
  rw [Measure.snd_compProd,Measure.snd_compProd,Probability.klDiv_compProd_same_eq_lintegral] at h
  exact h

/-- Fixed-clock input-averaged KL estimates may be integrated using the
actual measurable phase sections. No measurable choice of the root couplings
as a function of the clock is required. -/
theorem averaged_KL_le (Γ : ℝ) (G : Point d→Point d) (hG : Measurable G)
    (ν : Measure Input) [SFinite ν] (reference : Kernel (Input × UniformValue) Input)
    [IsMarkovKernel reference] :
    (∫⁻ x,InformationTheory.klDiv
      (((reference.comap (fun u => (x,u)) measurable_prodMk_left)) ∘ₘ (volume : Measure UniformValue))
      (ClockFinitePhaseKernel.kernel P hR hc hsmall label Γ G hG x) ∂ν)≤
      ∫⁻ u,∫⁻ x,InformationTheory.klDiv (reference (x,u))
        (sections P hR hc hsmall label Γ G hG (x,u)) ∂ν ∂(volume : Measure UniformValue) := by
  have hp (x : Input) : InformationTheory.klDiv
      ((reference.comap (fun u => (x,u)) measurable_prodMk_left) ∘ₘ (volume : Measure UniformValue))
      (ClockFinitePhaseKernel.kernel P hR hc hsmall label Γ G hG x)≤
      ∫⁻ u,InformationTheory.klDiv (reference (x,u))
        (sections P hR hc hsmall label Γ G hG (x,u)) ∂(volume : Measure UniformValue) := by
    rw [kernel_eq_average]
    exact mixture_KL volume _ _
  calc
    _ ≤ ∫⁻ x,∫⁻ u,InformationTheory.klDiv (reference (x,u))
        (sections P hR hc hsmall label Γ G hG (x,u)) ∂(volume : Measure UniformValue) ∂ν :=
      lintegral_mono hp
    _ = _ := lintegral_lintegral_swap
      (Probability.measurable_klDiv_kernel reference (sections P hR hc hsmall label Γ G hG)).aemeasurable
end AcceleratedLogConcave.Root.ClockPhaseSections
