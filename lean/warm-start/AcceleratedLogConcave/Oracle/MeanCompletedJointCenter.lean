import AcceleratedLogConcave.Oracle.MeanCompletedReference

/-! Actual jointly measurable mean final conditional. Its benchmark center
is read from the retained original center, before any fixed-center law is used. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanCompletedJointCenter
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer MeanChronologicalCoupling MeanChronologicalFinalObservation
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
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




variable (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
  (G : Point d → Point d) (hG : Measurable G)
local instance : MeasurableSpace (Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)) := prefixSpace d _
local instance : MeasurableSpace (Prefix d (afterBatch (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))) := prefixSpace d _




variable (Jall : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))
  (Jfinal : DesignatedChildBatchCoupling.Lower L (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))



/-- Every final benchmark center uses the actual retained original center. -/
def finishKernel := MeanFinalBatchCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w) (fun _ => measurable_const) (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst) L hL Jfinal (fun z : MeanChronologicalCoupling.History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) => z.1.1) measurable_fst.fst (fun i => MeanChronologicalHost.center M nodes anchors seeds main final sampling N x P referencePosition hF hell hlo hup r σ hr hσ hsmall (centerIndex M nodes i)) (fun i => MeanChronologicalHost.center_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference hF hell hlo hup r σ hr hσ hsmall (centerIndex M nodes i)) (MeanChronologicalFinalProjection.finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) (MeanChronologicalFinalProjection.finalComparison_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)
instance finishKernel_markov : IsMarkovKernel (finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jfinal) := by
  unfold finishKernel
  infer_instance

theorem finishKernel_original : (finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jfinal).fst=Kernel.id :=
  MeanFinalBatchCoupling.original_preserved M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w) (fun _ => measurable_const) (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst) L hL Jfinal (fun z : MeanChronologicalCoupling.History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) => z.1.1) measurable_fst.fst (fun i => MeanChronologicalHost.center M nodes anchors seeds main final sampling N x P referencePosition hF hell hlo hup r σ hr hσ hsmall (centerIndex M nodes i)) (fun i => MeanChronologicalHost.center_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference hF hell hlo hup r σ hr hσ hsmall (centerIndex M nodes i)) (MeanChronologicalFinalProjection.finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) (MeanChronologicalFinalProjection.finalComparison_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)

omit [MeasurableSpace A] in
/-- Exact agreement with the fixed-center reference analysis on its literal
center support; no probability or conditional independence enters. -/
theorem center_eq_fixed (base : Point d)
    (c : MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling N A) (hc : x c.1=base) (i : Fin m) :
    MeanChronologicalHost.center M nodes anchors seeds main final sampling N x P referencePosition hF hell hlo hup r σ hr hσ hsmall (centerIndex M nodes i) c =
      MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) i
        (benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base c) := by
  simp only [MeanChronologicalHost.center,centerIndex,Equiv.apply_symm_apply,
    MeanJointReference.reference,MeanChronologicalHost.phaseInput,
    MeanBenchmarkMoments.finalCenter,benchmarkSeed,MeanJointReference.seed]
  rw [← hc]
  rfl

def finalConditional := MeanFinalBatchCoupling.referenceConditional M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w) (fun _ => measurable_const) (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst) L hL Jfinal (fun z : MeanChronologicalCoupling.History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) => z.1.1) measurable_fst.fst (fun i => MeanChronologicalHost.center M nodes anchors seeds main final sampling N x P referencePosition hF hell hlo hup r σ hr hσ hsmall (centerIndex M nodes i)) (fun i => MeanChronologicalHost.center_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference hF hell hlo hup r σ hr hσ hsmall (centerIndex M nodes i)) (MeanChronologicalFinalProjection.finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) (MeanChronologicalFinalProjection.finalComparison_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)

theorem finalConditional_eq_fixed (base : Point d)
    (z : MeanChronologicalCoupling.History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (afterBatch (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)))
    (hc : x z.1.1.1=base) :
    finalConditional M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jfinal z =
      MeanFinalBatchCoupling.referenceConditional M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w) (fun _ => measurable_const) (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst) L hL Jfinal (MeanChronologicalFinalProjection.finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass) (MeanChronologicalFinalProjection.finalCoarse_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base hfinalMass) (MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (MeanBenchmarkMoments.finalCenter_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (MeanChronologicalFinalProjection.finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) (MeanChronologicalFinalProjection.finalComparison_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) z := by
  unfold finalConditional MeanFinalBatchCoupling.referenceConditional
  rw [Kernel.comap_apply,Kernel.comap_apply]
  unfold DesignatedChildBatchCoupling.referenceBatch
  rw [Conditional.MeanReferenceLayer.finiteProduct_apply m _ (fun _ => inferInstance),
    Conditional.MeanReferenceLayer.finiteProduct_apply m _ (fun _ => inferInstance)]
  congr 1
  apply funext
  intro i
  simp only [Kernel.comap_apply,MeanFinalBatchCoupling.observation]
  rw [center_eq_fixed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base z.1.1 hc i]
  rfl

theorem finishKernel_eq_fixed (base : Point d)
    (z : MeanChronologicalCoupling.History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N))
    (hc : x z.1.1.1=base) :
    finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jfinal z =
      MeanCompletedCoupling.finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jfinal z := by
  unfold finishKernel MeanCompletedCoupling.finishKernel MeanFinalBatchCoupling.kernel CausalTailHistory.onTape
  rw [Kernel.prod_apply,Kernel.prod_apply,Kernel.comap_apply,Kernel.comap_apply]
  congr 1
  exact finalConditional_eq_fixed M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jfinal base _ hc

/-- Complete finite mean augmentation with a jointly measurable final
conditional, preserving every original seed coordinate. -/
def kernel := finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jfinal ∘ₖ
  MeanChronologicalCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall
instance kernel_markov : IsMarkovKernel (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jall Jfinal) := by
  unfold kernel
  infer_instance

theorem kernel_original : (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jall Jfinal).map (MeanCompletedCoupling.original M nodes anchors seeds main final sampling N)=Kernel.id := by
  have hf : (finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jfinal).map (MeanCompletedCoupling.original M nodes anchors seeds main final sampling N)=Kernel.deterministic
      (MeanChronologicalCoupling.original M nodes anchors seeds main final sampling N) (MeanChronologicalCoupling.original_measurable M nodes anchors seeds main final sampling N) := by
    change (finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jfinal).map ((MeanChronologicalCoupling.original M nodes anchors seeds main final sampling N) ∘ Prod.fst)=_
    rw [Kernel.map_comp_right _ measurable_fst (MeanChronologicalCoupling.original_measurable M nodes anchors seeds main final sampling N),
      ← Kernel.fst_eq,finishKernel_original,Kernel.id_map]
  rw [kernel,Kernel.map_comp,hf,Kernel.deterministic_comp_eq_map,MeanChronologicalCoupling.kernel_original]

/-- The dynamic and fixed-center constructions agree on every incoming law
whose literal original center is base. -/
theorem law_eq_fixed (base : Point d) (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (hρ : ∀ᵐ z ∂ρ,x z.1=base) :
    kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jall Jfinal ∘ₘ ρ = MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ := by
  have hp : MeasurePreserving (MeanChronologicalCoupling.original M nodes anchors seeds main final sampling N) (MeanChronologicalCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ) ρ := by
    refine ⟨MeanChronologicalCoupling.original_measurable M nodes anchors seeds main final sampling N,?_⟩
    rw [Measure.map_comp _ _ (MeanChronologicalCoupling.original_measurable M nodes anchors seeds main final sampling N),
      MeanChronologicalCoupling.kernel_original,Measure.id_comp]
  have hs := hp.quasiMeasurePreserving.ae hρ
  rw [kernel,MeanCompletedCoupling.kernel,← Measure.comp_assoc,← Measure.comp_assoc]
  apply Measure.comp_congr
  filter_upwards [hs] with z hz
  exact finishKernel_eq_fixed M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jfinal base z hz

theorem center_ae (base : Point d) (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (hρ : ∀ᵐ z ∂ρ,x z.1=base) :
    ∀ᵐ z ∂kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jall Jfinal ∘ₘ ρ,x z.1.1.1.1=base := by
  have hp : MeasurePreserving (MeanCompletedCoupling.original M nodes anchors seeds main final sampling N) (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jall Jfinal ∘ₘ ρ) ρ := by
    refine ⟨MeanCompletedCoupling.original_measurable M nodes anchors seeds main final sampling N,?_⟩
    rw [Measure.map_comp _ _ (MeanCompletedCoupling.original_measurable M nodes anchors seeds main final sampling N),kernel_original,Measure.id_comp]
  exact hp.quasiMeasurePreserving.ae hρ

/-- Actual physical affine reference readout, with its center read from the
retained original sample. Only the scalar widths use the harmless zero-center data. -/
def coarseScore (c : MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling N A) : Point d :=
  (MeanJointReference.phase M hF hell hlo hup r σ hr hσ hsmall 1
    (MeanChronologicalHost.phaseInput M nodes anchors seeds main final sampling N x P referencePosition c)).snd

include hx hP hreference in
theorem coarseScore_measurable : Measurable (coarseScore M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall) :=
  (MeanJointReference.continuous_score M hF hell hlo hup r σ hr hσ hsmall 1).measurable.comp
    (MeanChronologicalHost.phaseInput_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference)

private def affineOutput (sigma width beta : ℝ) (z : (Point d × Point d) × (Fin m → Point d)) : Point d :=
  sigma⁻¹ • ((sigma/2) • z.1.1+
    (∑ i,(GaussLegendre.weight m i*width) • z.2 i)+beta • z.1.2)

private theorem affine_measurable (sigma width beta : ℝ) :
    Measurable (affineOutput (d := d) (m := m) sigma width beta) := by
  unfold affineOutput
  fun_prop

def coarseOutput (z : MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling N A × (Fin m → Point d)) : Point d :=
  affineOutput σ (Conditional.TerminalChildrenParentFamily.childScale (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall (0 : Point d)))
    (Conditional.TerminalChildrenParentFamily.beta (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall (0 : Point d)))
      ((coarseScore M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall z.1,MeanCompletedAugmentedLaws.staticGE M nodes anchors seeds main final sampling N P z.1),z.2)

include hx hP hreference in
theorem coarseOutput_measurable : Measurable (coarseOutput (d := d) M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall) := by
  have hc := (coarseScore_measurable M nodes anchors seeds main final sampling N r hr x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall).comp
    (measurable_fst : Measurable (Prod.fst : MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling N A × (Fin m → Point d) → _))
  have hge : Measurable (fun z : MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling N A × (Fin m → Point d) =>
      MeanCompletedAugmentedLaws.staticGE M nodes anchors seeds main final sampling N P z.1) :=
    (MeanCompletedAugmentedLaws.staticGE_measurable M nodes anchors seeds main final sampling N P hP).comp measurable_fst
  exact (affine_measurable σ
    (Conditional.TerminalChildrenParentFamily.childScale (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall (0 : Point d)))
    (Conditional.TerminalChildrenParentFamily.beta (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall (0 : Point d)))).comp
      ((hc.prodMk hge).prodMk measurable_snd)

def readout (z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin m → Point d)) : Point d := coarseOutput M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall (z.1.1.1,z.2)

include hx hP hreference in
theorem readout_measurable : Measurable (readout (d := d) M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall) :=
  (coarseOutput_measurable M nodes anchors seeds main final sampling N r hr x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall).comp
    (measurable_fst.fst.fst.prodMk measurable_snd)

omit [MeasurableSpace A] in
theorem readout_eq_fixed (base : Point d) (hm : 0<m) (ht : 0<t) (q : ℝ)
    (z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin m → Point d)) (hc : x z.1.1.1.1=base) :
    readout M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall z =
      MeanCompletedReference.readout M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hm ht q z := by
  unfold MeanCompletedReference.readout
  rw [MeanCompletedReconstruction.retainedPairs_readout]
  unfold readout coarseOutput affineOutput coarseScore Conditional.MeanReferenceSeedLaw.referenceOutput
  dsimp only [Conditional.MeanReferenceSeedLaw.seedBase,MeanCompletedReference.referenceChildren,
    Conditional.RecursiveReference.sourceChildren]
  have hphase : MeanJointReference.phase M hF hell hlo hup r σ hr hσ hsmall 1
      (MeanChronologicalHost.phaseInput M nodes anchors seeds main final sampling N x P referencePosition z.1.1.1) =
    MeanFlowLp.phase (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) 1
      (benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base z.1.1.1) := by
    unfold MeanJointReference.phase MeanFlowLp.phase benchmarkSeed MeanJointReference.seed
    rw [← hc]
    rfl
  rw [hphase]
  rfl

/-- Exact original-input/reference law of the jointly measurable construction. -/
theorem kernel_retained_reference_law (base : Point d) (hm : 0<m) (ht : 0<t) (q : ℝ)
    (hq : (1/2 : ℝ)<q)
    (hretained : ∀ i y, (Jfinal.joint i y).map (fun z => (z.1.1,z.2)) =
      (stdGaussian (Point d)) ⊗ₘ
        ((Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-t)).kernel.comap
          (fun p => (Conditional.RecursiveReference.childParameters hell M (MeanCompletedReference.parentTheta r σ hr hσ hsmall base) y,p)) measurable_prodMk_left))
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
    (hρ : ∀ᵐ z ∂ρ,x z.1=base)
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))
    (hincoming : μ.map (MeanCompletedAugmentedLaws.incomingAugmented M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      ((stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base))).prod
        (Measure.pi fun _ : Fin m => stdGaussian (Point d))) :
    (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jall Jfinal ∘ₘ ρ).map (fun z => (P z.1.1.1.1,
      readout M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall z)) =
        (stdGaussian (Point d)) ⊗ₘ
          ((Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht q).kernel.comap
            (fun p => (MeanCompletedReference.parentTheta r σ hr hσ hsmall base,p)) measurable_prodMk_left) := by
  have he := law_eq_fixed M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jall Jfinal base ρ hρ
  have hc := center_ae M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jall Jfinal base ρ hρ
  rw [he] at hc ⊢
  refine (Measure.map_congr ?_).trans
    (MeanCompletedReference.kernel_retained_reference_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal hm ht q hq hretained ha hA ρ μ hsplit hincoming)
  filter_upwards [hc] with z hz
  exact Prod.ext rfl (readout_eq_fixed M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w hfinalMass G base hm ht q z hz)

end AcceleratedLogConcave.Oracle.MeanCompletedJointCenter
