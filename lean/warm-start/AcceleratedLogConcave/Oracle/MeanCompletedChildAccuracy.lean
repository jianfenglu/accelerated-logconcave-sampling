import AcceleratedLogConcave.Oracle.MeanMainErrorTransport
import AcceleratedLogConcave.Oracle.MeanCompletedAugmentedLaws
import AcceleratedLogConcave.Oracle.MeanAllNodeMoments
import AcceleratedLogConcave.Oracle.PrivateCompletedRms

/-! Actual completed mean-main child payments. The lower retained full-seed
error is averaged at the literal benchmark center. Its varying primitive
scale is integrated using the original common-seed flow law and proved node
moments, while the complete original source remains retained. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanCompletedChildAccuracy
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling MeanChronologicalSuffix
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)
  (r Ds : ℝ) (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  {A : Type*} [MeasurableSpace A]
  (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
  (x P referencePosition : A → Point d) (hx : Measurable x) (hP : Measurable P)
  (hreference : Measurable referencePosition)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (σ : ℝ) (hσ : 0<σ) (hsmall : r^2*ell≤1/2) (δ t w : ℝ)
local instance : MeasurableSpace
    (Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) := prefixSpace d _

local notation "Xmain" => History (d := d) M nodes anchors seeds main final sampling N A ×
  Tape d (Host M nodes anchors seeds main final sampling N)
local notation "centersM" => MeanChronologicalHost.center M nodes anchors seeds main final sampling N x P referencePosition hF hell hlo hup r σ hr hσ hsmall
local notation "hcentersM" => MeanChronologicalHost.center_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference hF hell hlo hup r σ hr hσ hsmall

local notation "C" => Coarse (d := d) M nodes anchors seeds main final sampling N A
local notation "D" => MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall
local notation "seed" => MeanChronologicalFinalObservation.benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall
local notation "rho" => RecursiveMeanPublicTable.centerNoise r M.R Ds
local notation "childWidth" => CovarianceSetup.sigma n rho (rowBound (m := m) r σ δ t w)

omit [MeasurableSpace A] in
/-- All main nodes use the same literal source flow seed, including its
retained private reference and original assembly/flow draws. -/
theorem center_eq_rawReference (base : Point d) (c : C) (hc : x c.1=base) (i : Fin n) :
    centersM i c = MeanResidualBridge.rawReference (D base) (nodes i) (seed base c) := by
  simp only [MeanChronologicalHost.center,MeanJointReference.reference,
    MeanChronologicalHost.phaseInput,MeanChronologicalFinalObservation.benchmarkSeed,
    MeanJointReference.seed]
  rw [←hc]

variable (base : Point d)
  (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
  (hbase : ∀ᵐ c ∂μ,x c.1=base)
  (hseed : MeasurePreserving
    (MeanChronologicalFinalObservation.benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)
    μ (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)))

omit [IsProbabilityMeasure μ] in
include hx hP hreference in
/-- The constructed assembly/private incoming inventory supplies the exact
phase-seed marginal needed for averaging, by projection of its full joint. -/
theorem seed_preserving_of_incoming
    (hincoming : μ.map (MeanCompletedAugmentedLaws.incomingAugmented M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      ((stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure (D base))).prod
        (Measure.pi fun _ : Fin m => stdGaussian (Point d))) :
    MeasurePreserving (seed base) μ (MeanFlowLp.seedMeasure (D base)) := by
  have hp : MeasurePreserving
      (MeanCompletedAugmentedLaws.incomingAugmented M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)
      μ (((stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure (D base))).prod
        (Measure.pi fun _ : Fin m => stdGaussian (Point d))) :=
    ⟨MeanCompletedAugmentedLaws.incomingAugmented_measurable M nodes anchors seeds main final sampling N r hr
      x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base,hincoming⟩
  exact (measurePreserving_snd.comp measurePreserving_fst).comp hp

omit [IsProbabilityMeasure μ] in
include hbase hseed in
/-- The actual incoming joint law pays the varying main-node scale. This
uses only its phase-seed projection, with no independence from original P. -/
theorem node_scale_moment (i : Fin n) (h₀ : ℝ)
    (hmesh : MeanCollocationLp.MeshConditions (D base) h₀)
    (hhalf : MeanCollocationLp.contraction (D base) h₀≤1/2) :
    Integrable (fun c => (Gibbs.primitiveScale F (centersM i c))^2) μ ∧
      (∫ c, (Gibbs.primitiveScale F (centersM i c))^2 ∂μ) ≤
        MeanAllNodeMoments.scaleSquareBudget (D base) h₀ := by
  let f := fun s => MeanBenchmarkMoments.nodeScale (D base) (nodes i) s ^ 2
  have hi : Integrable f (MeanFlowLp.seedMeasure (D base)) :=
    MeanBenchmarkMoments.node_scale_square_integrable (D base) (nodes i)
  have he : (fun c => (Gibbs.primitiveScale F (centersM i c))^2) =ᵐ[μ] f ∘ seed base := by
    filter_upwards [hbase] with c hc
    rw [center_eq_rawReference M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base c hc i]
    rfl
  refine ⟨(hseed.integrable_comp_of_integrable hi).congr he.symm,?_⟩
  rw [integral_congr_ae he]
  have himap : AEStronglyMeasurable f (μ.map (seed base)) := by
    rw [hseed.map_eq]
    exact hi.aestronglyMeasurable
  have ht := integral_map (μ := μ) hseed.aemeasurable himap
  rw [hseed.map_eq] at ht
  exact ht.symm.trans_le (MeanAllNodeMoments.node_scale_square_le (D base) h₀ hmesh hhalf (nodes i))


variable (J : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    (stage M nodes anchors seeds main final sampling N k hk.le).1
    (stage_positive M nodes anchors seeds main final sampling N k hk)))
  (G : Point d → Point d) (hG : Measurable G)
local notation "lowerErr" => MeanMainErrorTransport.lowerError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G
local notation "stageErr" => MeanMainErrorTransport.stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G

include hx hP hreference hG hbase hseed in
/-- The concrete main batch averages the LOWER accuracy payment over its
actual retained source phase, using the original-data node moment. -/
theorem averaged_main_error_bound (k : ℕ) (hk : k<N) (i : Fin n)
    (amplitude h₀ : ℝ) (hmesh : MeanCollocationLp.MeshConditions (D base) h₀)
    (hhalf : MeanCollocationLp.contraction (D base) h₀≤1/2)
    (hfiber : ∀ y : Point d,
      MemLp (FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
        (Gibbs.primitiveMean F y (M.radius r (nodes i))) childWidth) 2 ((J k hk).joint i y))
    (hbound : ∀ y : Point d,
      (∫ z, ‖FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
        (Gibbs.primitiveMean F y (M.radius r (nodes i))) childWidth z‖^2 ∂(J k hk).joint i y) ≤
          (amplitude*Gibbs.primitiveScale F y)^2) :
    MemLp (lowerErr i) 2 (μ ⊗ₘ ((J k hk).joint i).comap (centersM i) (hcentersM i)) ∧
      (∫ z, ‖lowerErr i z‖^2 ∂μ ⊗ₘ ((J k hk).joint i).comap (centersM i) (hcentersM i)) ≤
        amplitude^2*MeanAllNodeMoments.scaleSquareBudget (D base) h₀ := by
  let B := data M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    (stage M nodes anchors seeds main final sampling N k hk.le).1
    (stage_positive M nodes anchors seeds main final sampling N k hk)
  have hmeas := MeanMainErrorTransport.lowerError_measurable M nodes anchors seeds main final sampling N r Ds hr
    x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w G hG i
  obtain ⟨hi,hscale⟩ := node_scale_moment M nodes anchors seeds main final sampling N r hr x P referencePosition
    hF hell hlo hup σ hσ hsmall base μ hbase hseed i h₀ hmesh hhalf
  have hcost : Integrable (fun c => (amplitude*Gibbs.primitiveScale F (centersM i c))^2) μ := by
    simpa only [mul_pow] using hi.const_mul (amplitude^2)
  obtain ⟨hm,hpay⟩ := FreshChildBatchErrorTransfer.averaged_error_memLp_of_bound L B (J k hk)
    centersM hcentersM μ i (lowerErr i) hmeas.stronglyMeasurable
    (Filter.Eventually.of_forall fun c => hfiber (centersM i c))
    (fun c => amplitude*Gibbs.primitiveScale F (centersM i c)) hcost
    (Filter.Eventually.of_forall fun c => hbound (centersM i c))
  refine ⟨hm,hpay.trans ?_⟩
  simp only [mul_pow]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hscale (sq_nonneg amplitude)

variable (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))
    (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
    (Jfinal : DesignatedChildBatchCoupling.Lower L
      (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))
local notation "completedLaw" => MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG J Jfinal ∘ₘ ρ

include hx hP hreference hG ha hA hsplit hbase hseed in
/-- The actual completed program preserves every earlier main-child error,
so LOWER accuracy and the proved source moment supply its genuine L2 input. -/
theorem completed_main_error_bound (k : ℕ) (hk : k<N) (i : Fin n)
    (amplitude h₀ : ℝ) (hmesh : MeanCollocationLp.MeshConditions (D base) h₀)
    (hhalf : MeanCollocationLp.contraction (D base) h₀≤1/2)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (M.radius r (nodes i)) (main i).shiftVector)
    (hfiber : ∀ y : Point d,
      MemLp (FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
        (Gibbs.primitiveMean F y (M.radius r (nodes i))) childWidth) 2 ((J k hk).joint i y))
    (hbound : ∀ y : Point d,
      (∫ z, ‖FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
        (Gibbs.primitiveMean F y (M.radius r (nodes i))) childWidth z‖^2 ∂(J k hk).joint i y) ≤
          (amplitude*Gibbs.primitiveScale F y)^2) :
    ∃ hi : MemLp ((stageErr k hk i) ∘ Prod.fst) 2 completedLaw,
      (∫ z, ‖stageErr k hk i z.1‖^2 ∂completedLaw) ≤
        amplitude^2*MeanAllNodeMoments.scaleSquareBudget (D base) h₀ ∧
      ‖hi.toLp ((stageErr k hk i) ∘ Prod.fst)‖ ≤
        Real.sqrt (amplitude^2*MeanAllNodeMoments.scaleSquareBudget (D base) h₀) := by
  obtain ⟨hm,hpay⟩ := averaged_main_error_bound M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    L x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base μ hbase hseed J G hG
    k hk i amplitude h₀ hmesh hhalf hfiber hbound
  have hf : Measurable (fun z : Xmain × (Fin m → Point d) => stageErr k hk i z.1) :=
    (MeanMainErrorTransport.stageError_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L
    x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w G hG k hk i).comp measurable_fst
  have hg := MeanMainErrorTransport.lowerError_measurable M nodes anchors seeds main final sampling N r Ds hr
    x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w G hG i
  have hlaw := MeanMainErrorTransport.completed_error_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J G hG ha hA ρ μ hsplit base hfinalMass Jfinal k hk i hshift
  obtain ⟨hi,he⟩ := PrivateCompletedRms.memLp_integral_of_law _ _ _ _ hf hg hlaw hm
  have hp := he.le.trans hpay
  refine ⟨hi,hp,?_⟩
  apply FreshChildBatchErrorTransfer.norm_toLp_le_of_square_integral _ _ hi _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (le_trans (integral_nonneg fun _ => sq_nonneg _) hp)]
  exact hp

end AcceleratedLogConcave.Oracle.MeanCompletedChildAccuracy
