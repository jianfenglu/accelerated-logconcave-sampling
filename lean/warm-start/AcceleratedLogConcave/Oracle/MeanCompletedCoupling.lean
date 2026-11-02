import AcceleratedLogConcave.Oracle.MeanChronologicalFinalProjection
import AcceleratedLogConcave.Oracle.MeanFinalBatchJointLaw
import AcceleratedLogConcave.Oracle.MeanBenchmarkMoments

/-! Full mean-main and designated-final augmentation on the unchanged
original source. The retained Pi/reference pair law is derived from the actual
incoming source joint law and constructed finite chronology. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanCompletedCoupling
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling MeanChronologicalFinalObservation MeanChronologicalFinalProjection
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




variable (base : Point d)
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
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

/-- The actual designated paid-final conditional. It reads the stored Pi,
comparison center inventory and same complete final child tapes. -/
def finishKernel := MeanFinalBatchCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w)
  (fun _ => measurable_const) (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst) L hL Jfinal
  (finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass) (finalCoarse_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base hfinalMass) (MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (MeanBenchmarkMoments.finalCenter_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) (finalComparison_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)

instance finishKernel_markov : IsMarkovKernel (finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jfinal) := by unfold finishKernel; infer_instance

theorem finishKernel_original : (finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jfinal).fst=Kernel.id :=
  MeanFinalBatchCoupling.original_preserved M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w)
    (fun _ => measurable_const) (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst) L hL Jfinal
    (finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass) (finalCoarse_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base hfinalMass) (MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (MeanBenchmarkMoments.finalCenter_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) (finalComparison_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)

/-- Actual finite main chronology followed by the actual retained designated
final batch. The original incoming sample and entire original tape remain. -/
def kernel := finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jfinal ∘ₖ MeanChronologicalCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall

instance kernel_markov : IsMarkovKernel (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal) := by unfold kernel; infer_instance

def original (z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin m → Point d)) :=
  MeanChronologicalCoupling.original M nodes anchors seeds main final sampling N z.1

theorem original_measurable : Measurable (original (d := d) (A := A) M nodes anchors seeds main final sampling N) :=
  (MeanChronologicalCoupling.original_measurable M nodes anchors seeds main final sampling N).comp measurable_fst

theorem kernel_original : (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal).map (original M nodes anchors seeds main final sampling N)=Kernel.id := by
  have hf : (finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jfinal).map (original M nodes anchors seeds main final sampling N)=Kernel.deterministic
      (MeanChronologicalCoupling.original M nodes anchors seeds main final sampling N) (MeanChronologicalCoupling.original_measurable M nodes anchors seeds main final sampling N) := by
    change (finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jfinal).map ((MeanChronologicalCoupling.original M nodes anchors seeds main final sampling N) ∘ Prod.fst)=_
    rw [Kernel.map_comp_right _ measurable_fst (MeanChronologicalCoupling.original_measurable M nodes anchors seeds main final sampling N),
      ← Kernel.fst_eq,finishKernel_original,Kernel.id_map]
  rw [kernel,Kernel.map_comp,hf,Kernel.deterministic_comp_eq_map,MeanChronologicalCoupling.kernel_original]

def retainedPairs := MeanFinalBatchJointLaw.retainedPairs M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w) (finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass) (finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)

theorem kernel_retained_pairs_law
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))
    (hincoming : μ.map (incomingInventory M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)).prod (Measure.pi fun _ : Fin m => stdGaussian (Point d))) :
    (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ).map (retainedPairs M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G)=
      (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) ⊗ₘ DesignatedChildBatchJointTransfer.averagedPairs L hL (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) Jfinal
        (MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (MeanBenchmarkMoments.finalCenter_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) := by
  obtain ⟨ν,hν,hcut,_,hprojection⟩ := kernel_final_observation_laws M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall ha hA ρ μ hsplit hincoming
  let _ : IsProbabilityMeasure ν := hν
  have hp := MeanFinalBatchJointLaw.retained_pairs_law M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w)
    (fun _ => measurable_const) (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst) L hL Jfinal
    (finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass) (finalCoarse_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base hfinalMass) (MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (MeanBenchmarkMoments.finalCenter_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) (finalComparison_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)
    (MeanChronologicalCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ) ν hcut (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) hprojection
  simpa only [kernel,← Measure.comp_assoc,finishKernel,retainedPairs,finalObservation] using hp



/-- Both the entire original source and its complete unread correction tape
remain after all reference augmentation. No incoming Gaussian law is needed
for this whole-tail assertion. -/
theorem kernel_whole_correction
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :
    ∃ (η : Measure ((History (d := d) M nodes anchors seeds main final sampling N A × Prefix d
      (afterBatch (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))) × (Fin m → Point d))),
      IsProbabilityMeasure η ∧
      (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ).map (CausalTailHistory.unpackExtended
        (afterBatch (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)))=
          η.prod (tapeLaw L (MeanFinalBatchCoupling.suffix M nodes anchors seeds main final sampling N)) := by
  obtain ⟨ν,hν,hcut,_⟩ := MeanChronologicalFinalLaws.kernel_finalBatch_laws M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall
    hfinalMass ha hA ρ μ hsplit
  let _ : IsProbabilityMeasure ν := hν
  let _ : ∀ i,IsProbabilityMeasure (tapeLaw L (DesignatedChildBatchCoupling.program (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) i)) :=
    fun i => tapeLaw_probability L _
  let _ : IsProbabilityMeasure (advancedLaw L (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) ν) := by
    unfold advancedLaw
    infer_instance
  let η := (advancedLaw L (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) ν) ⊗ₘ (MeanFinalBatchCoupling.referenceConditional M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w) (fun _ => measurable_const) (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst) L hL Jfinal (finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass) (finalCoarse_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base hfinalMass) (MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (MeanBenchmarkMoments.finalCenter_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) (finalComparison_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))
  have hη : IsProbabilityMeasure η := by dsimp [η]; infer_instance
  refine ⟨η,hη,?_⟩
  have hp := MeanFinalBatchCoupling.whole_suffix M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w)
    (fun _ => measurable_const) (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst) L hL Jfinal
    (finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass) (finalCoarse_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base hfinalMass) (MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (MeanBenchmarkMoments.finalCenter_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) (finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) (finalComparison_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)
    (MeanChronologicalCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ) ν hcut
  simpa only [kernel,← Measure.comp_assoc,finishKernel] using hp

end AcceleratedLogConcave.Oracle.MeanCompletedCoupling
