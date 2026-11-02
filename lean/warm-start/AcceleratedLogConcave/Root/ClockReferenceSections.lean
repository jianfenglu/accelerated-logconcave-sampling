import AcceleratedLogConcave.Root.ClockReferencePhaseLaw
import Mathlib.Probability.Kernel.CompProdEqIff

/-! Measurable source reference sections, retaining the original input and
averaging to the same accepted physical reference phase. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockReferenceSections
open Oracle Oracle.CubicExecutableWorkShift Kinetic Kinetic.Reheating
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
local notation "E" => Point d
local notation "Input" => E × E
local notation "PhaseTape" => ((GaussianPhase E × E) × E) × E
local notation "Fphys" => OuterRootFlowIdentification.family hV hm P.delta_pos hlo hup
local notation "ell" => Real.sqrt (2*P.delta^2)
local notation "s" => ClockPublicSetup.s
local notation "n" => ClockPublicSetup.noise
local notation "hsn" => source_split_coefficients
local notation "H" => ClockReferencePhaseLaw.heatFamily P hV hm hlo hup
private theorem variance_pos : 0<2*P.delta^2 := by nlinarith [sq_pos_of_pos P.delta_pos]
private theorem variance_lt : 2*P.delta^2<2*(2*P.delta^2) := by nlinarith [sq_pos_of_pos P.delta_pos]
include hc hsmall hC in
private theorem order_pos : 0<P.m := by
  have h := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  omega
local notation "Q" => OriginalReferenceMixing.referenceKernel hV (inv_pos.mpr hm) P.delta_pos
  (FinalMeanScheduledData.delta_half P hK hc hsmall hC hy)
  (by simpa only [inv_inv] using hlo) hup (source P hR).M (order_pos P hc hsmall hC)
  P.t (P.t_pos hc) P.K
local notation "ν" => ((Fphys).law 0).prod (stdGaussian E)

def readout (Γ : ℝ) (z : ClockLaw.Clock × PhaseTape) : Input × Input := by
  letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  exact (ReferencePhaseLaw.input z,ReferencePhaseLaw.output H (variance_pos P) (variance_lt P) ell Γ z)

theorem readout_measurable (Γ : ℝ) : Measurable (readout P hV hm hlo hup Γ) := by
  letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  exact ReferencePhaseLaw.input_measurable.prodMk
    (ReferencePhaseLaw.output_measurable H (variance_pos P) (variance_lt P) ell Γ)

/-- The complete accepted reference input/output joint as one measurable
clock-indexed kernel; no clock-indexed coupling selection occurs. -/
def jointKernel (Γ : ℝ) : Kernel ClockLaw.Clock (Input × Input) :=
  ((Kernel.id ×ₖ frameTape Fphys ell s n hsn Q).map
    (readout P hV hm hlo hup Γ))
instance jointKernel_markov (Γ : ℝ) : IsMarkovKernel
    (jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ) :=
  Kernel.IsMarkovKernel.map _ (readout_measurable P hV hm hlo hup Γ)

theorem jointKernel_apply (Γ : ℝ) (clock : ClockLaw.Clock) :
    jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ clock=
      (frameTape Fphys ell s n hsn Q clock).map
        (ClockReferencePhaseLaw.referenceFrameOutput P hV hm hlo hup clock Γ) := by
  rw [jointKernel,Kernel.map_apply _ (readout_measurable P hV hm hlo hup Γ),Kernel.prod_apply,
    Kernel.id_apply,Measure.dirac_prod,Measure.map_map
      (readout_measurable P hV hm hlo hup Γ) measurable_prodMk_left]
  rfl

/-- Every fixed-clock reference retains precisely the same full visible input. -/
theorem jointKernel_fst (Γ : ℝ) :
    (jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ).fst=Kernel.const ClockLaw.Clock ν := by
  letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  ext clock : 1
  rw [Kernel.fst_apply,jointKernel_apply,Measure.map_map measurable_fst
    (ClockReferencePhaseLaw.referenceFrameOutput_measurable P hV hm hlo hup clock Γ)]
  exact (ReferencePhaseLaw.input_preserving_fixed_clock H (variance_pos P) (variance_lt P) ell Q clock).map_eq

/-- Actual jointly measurable conditional reference sections, ordered exactly
as the executable sections: (physical input, original uniform primitive). -/
def sections (Γ : ℝ) : Kernel (Input × UniformValue) Input :=
  (jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ).condKernel.comap
    (fun z => (ClockUniformDraw.clockOfUniform z.2,z.1))
    ((ClockUniformDraw.measurable_clockOfUniform.comp measurable_snd).prodMk measurable_fst)
instance sections_markov (Γ : ℝ) : IsMarkovKernel
    (sections P hR hc hsmall hK hC hy hV hm hlo hup Γ) := by unfold sections; infer_instance

/-- Exact conditional disintegration of each concrete source reference joint. -/
theorem section_joint (Γ : ℝ) (u : UniformValue) :
    ν ⊗ₘ (sections P hR hc hsmall hK hC hy hV hm hlo hup Γ).comap
      (fun x => (x,u)) measurable_prodMk_right=
      jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ (ClockUniformDraw.clockOfUniform u) := by
  have h := congrArg (fun k : Kernel ClockLaw.Clock (Input × Input) => k (ClockUniformDraw.clockOfUniform u))
    ((jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ).disintegrate
      (jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ).condKernel)
  rw [jointKernel_fst] at h
  change ((Kernel.const ClockLaw.Clock ν) ⊗ₖ
    (jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ).condKernel) (ClockUniformDraw.clockOfUniform u)=_ at h
  refine Eq.trans ?_ h
  ext S hS
  rw [Measure.compProd_apply hS,Kernel.compProd_apply hS]
  rfl

/-- Average the same measurable conditional sections over the actual uniform. -/
def averaged (Γ : ℝ) : Kernel Input Input :=
  (sections P hR hc hsmall hK hC hy hV hm hlo hup Γ) ∘ₖ
    ((Kernel.id : Kernel Input Input) ×ₖ Kernel.const Input (volume : Measure UniformValue))
instance averaged_markov (Γ : ℝ) : IsMarkovKernel
    (averaged P hR hc hsmall hK hC hy hV hm hlo hup Γ) := by unfold averaged; infer_instance

/-- Each average is the literal mixture of the measurable uniform sections. -/
theorem averaged_apply (Γ : ℝ) (x : Input) {t : Set Input} (ht : MeasurableSet t) :
    averaged P hR hc hsmall hK hC hy hV hm hlo hup Γ x t=
      ∫⁻ u,sections P hR hc hsmall hK hC hy hV hm hlo hup Γ (x,u) t ∂(volume : Measure UniformValue) := by
  rw [averaged,Kernel.comp_apply' _ _ _ ht,Kernel.lintegral_id_prod
    ((sections P hR hc hsmall hK hC hy hV hm hlo hup Γ).measurable_coe ht)]
  rfl

/-- The original input is retained when averaging over the actual uniform. -/
theorem averaged_joint (Γ : ℝ) :
    ν ⊗ₘ averaged P hR hc hsmall hK hC hy hV hm hlo hup Γ=
      jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ ∘ₘ sourceClockLaw := by
  apply Measure.ext_prod
  intro a b ha hb
  rw [Measure.compProd_apply_prod ha hb,
    Measure.bind_apply (ha.prod hb) (Kernel.aemeasurable _),
    ← ClockUniformDraw.map_uniform_clock,
    lintegral_map ((jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ).measurable_coe (ha.prod hb))
      ClockUniformDraw.measurable_clockOfUniform]
  simp_rw [averaged_apply P hR hc hsmall hK hC hy hV hm hlo hup Γ _ hb,
    ← section_joint P hR hc hsmall hK hC hy hV hm hlo hup Γ,
    Measure.compProd_apply_prod ha hb]
  exact lintegral_lintegral_swap
    ((sections P hR hc hsmall hK hC hy hV hm hlo hup Γ).measurable_coe hb).aemeasurable

/-- The same accepted original-frame jointTape, now averaged over the clock. -/
theorem jointKernel_average (Γ : ℝ) :
    letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
    jointKernel P hR hc hsmall hK hC hy hV hm hlo hup Γ ∘ₘ sourceClockLaw=
      (ReferencePhaseLaw.jointTape H (variance_pos P) (variance_lt P) ell Q).map
        (readout P hV hm hlo hup Γ) := by
  letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  rw [jointKernel,← Measure.map_comp _ _ (readout_measurable P hV hm hlo hup Γ)]
  congr 1
  exact (Measure.compProd_eq_comp_prod sourceClockLaw (frameTape Fphys ell s n hsn Q)).symm

/-- The actual clock-average reference is precisely the accepted phase kernel
on its full physical position/momentum base. -/
theorem averaged_joint_phase (Γ : ℝ) :
    letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
    ν ⊗ₘ averaged P hR hc hsmall hK hC hy hV hm hlo hup Γ=
      ν ⊗ₘ ReferencePhaseLaw.phaseKernel H (variance_pos P) (variance_lt P) ell Γ Q := by
  letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  rw [averaged_joint,jointKernel_average]
  exact (ReferencePhaseLaw.phaseKernel_disintegration H (variance_pos P) (variance_lt P) ell Γ Q).symm

/-- Equality of actual kernels almost everywhere, derived from the full joint. -/
theorem averaged_eq_phase_ae (Γ : ℝ) :
    letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
    averaged P hR hc hsmall hK hC hy hV hm hlo hup Γ =ᵐ[ν]
      ReferencePhaseLaw.phaseKernel H (variance_pos P) (variance_lt P) ell Γ Q := by
  letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  exact Kernel.ae_eq_of_compProd_eq (averaged_joint_phase P hR hc hsmall hK hC hy hV hm hlo hup Γ)

local instance canonicalTapeSpace {c : ℕ} {CtxP : Ctx} {τ : Ty}
    (p : Prog c CtxP τ) : MeasurableSpace (Tape d p) :=
  CanonicalTapeMeasurability.tapeSpace d p

/-- Concrete completed reference comparison equals these very sections,
including the original visible input and both fresh Gaussian draws. -/
theorem completed_joint_section (label : ℕ)
    (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y) (Γ : ℝ) (u : UniformValue) :
    let clock := ClockUniformDraw.clockOfUniform u
    let μX := OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup
    let μ := ClockCompletedPhaseLaw.law P hR hc hsmall clock label hK hC hy hV
      (OuterRootFlowIdentification.lower_nonneg hm hlo) hup hyMean (μX.prod (stdGaussian E))
    let inp := fun z => ClockCompletedPhaseLaw.sourceInput P hR hc hsmall clock label
      (ClockCompletedPhaseLaw.original P hR hc hsmall clock label z)
    (μ.prod ((stdGaussian E).prod (stdGaussian E))).map (fun z =>
      (inp z.1,ClockPhaseGaussianKL.phaseOutput P.delta Γ clock (inp z.1).1
        (ClockCompletedPhaseLaw.referenceRoot P hR hc hsmall clock label hK hC hy hV
          (OuterRootFlowIdentification.lower_nonneg hm hlo) hup z.1) z.2.1 z.2.2))=
      ν ⊗ₘ (sections P hR hc hsmall hK hC hy hV hm hlo hup Γ).comap
        (fun x => (x,u)) measurable_prodMk_right := by
  dsimp only
  exact (ClockReferencePhaseLaw.reference_phase_law P hR hc hsmall hK hC hy hV hm hlo hup
    (ClockUniformDraw.clockOfUniform u) label hyMean Γ).trans
      ((jointKernel_apply P hR hc hsmall hK hC hy hV hm hlo hup Γ (ClockUniformDraw.clockOfUniform u)).symm.trans
        (section_joint P hR hc hsmall hK hC hy hV hm hlo hup Γ u).symm)

/-- Literal source mixing length convention for the averaged reference kernel. -/
theorem averaged_eq_source_phase_ae (Γ : ℝ) :
    letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
    averaged P hR hc hsmall hK hC hy hV hm hlo hup Γ =ᵐ[ν]
      ReferencePhaseLaw.phaseKernel H (variance_pos P) (variance_lt P) (Real.sqrt 2*P.delta) Γ Q := by
  letI := Gibbs.originalGibbs_probability_of_hessian_lower hV (inv_pos.mpr hm) (by simpa only [inv_inv] using hlo)
  simpa only [ClockReferencePhaseLaw.length_eq P] using
    averaged_eq_phase_ae P hR hc hsmall hK hC hy hV hm hlo hup Γ

end AcceleratedLogConcave.Root.ClockReferenceSections
