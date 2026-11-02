import AcceleratedLogConcave.Oracle.MeanCompletedJointCenter
import AcceleratedLogConcave.Oracle.MeanIncomingPrivateReferenceLaw

/-! Standalone joint-center coupling from literal private augmentation,
finite mean chronology and paid designated-final conditionals. Every canonical
source coordinate is retained, including uniforms and residual draws. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanStandaloneRetainedCoupling
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable {m n a h sn d : ℕ} (M : MeanGeometry m)
  (nodes : Fin n ≃ M.MeanNode) (anchors : Fin a ≃ M.Anchor)
  (seeds : Fin h ≃ Fin m × M.Kernel) (main : Fin n → ExecutableData)
  (final : Fin m → ExecutableData) (meanN : ℕ)
  (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
  (snodes : Fin sn ≃ (RecursiveExecutable.privateGeometry M mesh).Node)
  (r Ds σ : ℝ) (hr : 0<r) (hDs : 0<Ds) (hσ : 0<σ)
  (smain sfinal : Fin sn → ExecutableData) (privateN : ℕ)
  (hprivateMass : ∀ i,CovarianceSetup.shiftSq (smain i).shiftVector≤Ds^2)
  (hprivateFinalMass : ∀ i,CovarianceSetup.shiftSq (sfinal i).shiftVector≤Ds^2)
  (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (hsmall : r^2*ell≤1/2)
  (JprivateFinal : FreshChildBatchCoupling.Lower L
    (PrivateFinalCoupling.data (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN hr hDs hprivateFinalMass
      (PrivateChronologicalCoupling.terminalCursor (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN).old))
  (Jprivate : ∀ (k : ℕ) (hk : k<privateN),FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN hr hDs hprivateMass
      (PrivateChronologicalCoupling.stage (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN k hk.le).1
      (PrivateChronologicalCoupling.stage_positive (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN k hk)))

/-- Actual consumed-private augmentation, with the complete parent source
and unread mean body preserved. -/
def incomingKernel : Kernel (Point d) (MeanIncomingCompletedLaw.History d × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) :=
  MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN L (MeanIncomingPrivateReferenceLaw.privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate)
instance incomingKernel_markov : IsMarkovKernel
    (incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate) := by
  unfold incomingKernel
  infer_instance

local instance point_probability : IsProbabilityMeasure L.pointDraw := L.point_probability
local instance allTape_probability {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    IsProbabilityMeasure (tapeLaw L p) := tapeLaw_probability L p

/-- Forget only the appended private reference; keep the original center,
designated input and the entire parent tape. -/
def incomingOriginal (z : MeanIncomingCompletedLaw.History d × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) : (Point d × Point d) × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN) := (z.1.1,z.2)
theorem incomingOriginal_measurable : Measurable (incomingOriginal (d := d) M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN) :=
  measurable_fst.fst.prodMk measurable_snd

theorem incomingKernel_original : (incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate).map
    (incomingOriginal M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN)=MeanIncomingPrivateCoupling.prior M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN L := by
  unfold incomingKernel MeanIncomingCompletedLaw.kernel
  rw [← Kernel.map_comp_right _ PrivateCausalAdvance.regroupOriginal_measurable
    (incomingOriginal_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN)]
  change (MeanIncomingPrivateCoupling.kernel M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN L (MeanIncomingPrivateReferenceLaw.privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate )).map Prod.fst=_
  rw [← Kernel.fst_eq]
  exact MeanIncomingPrivateCoupling.kernel_original M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN L (MeanIncomingPrivateReferenceLaw.privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate)

def incomingSeed (z : MeanIncomingCompletedLaw.History d × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) : Point d × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN) := (z.1.1.2,z.2)
theorem incomingSeed_measurable : Measurable (incomingSeed (d := d) M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN) :=
  measurable_fst.fst.snd.prodMk measurable_snd

private theorem prior_source : (MeanIncomingPrivateCoupling.prior M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN L).map
    (fun z : (Point d × Point d) × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN) => (z.1.2,z.2)) =
      Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) := by
  ext base : 1
  rw [Kernel.map_apply _ (by fun_prop),Kernel.const_apply,MeanIncomingPrivateCoupling.prior,
    Kernel.prod_apply,Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Kernel.const_apply]
  exact ((measurePreserving_snd (μ := Measure.dirac base) (ν := L.pointDraw)).prod
    (MeasurePreserving.id (tapeLaw L (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)))).map_eq

/-- The exact complete standalone source seed is preserved. -/
theorem incomingKernel_source : (incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate).map
    (incomingSeed M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN) =
      Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) := by
  change (incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate).map
    ((fun z : (Point d × Point d) × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN) => (z.1.2,z.2)) ∘ incomingOriginal M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN)=_
  rw [Kernel.map_comp_right _ (incomingOriginal_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN) (by fun_prop),
    incomingKernel_original,prior_source]

private theorem prior_center : (MeanIncomingPrivateCoupling.prior M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN L).map
    (fun z : (Point d × Point d) × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN) => z.1.1) = Kernel.id := by
  ext base : 1
  rw [Kernel.map_apply _ (by fun_prop),Kernel.id_apply,MeanIncomingPrivateCoupling.prior,
    Kernel.prod_apply,Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Kernel.const_apply]
  exact ((measurePreserving_fst (μ := Measure.dirac base) (ν := L.pointDraw)).comp
    (measurePreserving_fst (μ := (Measure.dirac base).prod L.pointDraw)
      (ν := tapeLaw L (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)))).map_eq

theorem incomingKernel_center : (incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate).map
    (fun z : MeanIncomingCompletedLaw.History d × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN) => z.1.1.1) = Kernel.id := by
  change (incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate).map
    ((fun z : (Point d × Point d) × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN) => z.1.1) ∘ incomingOriginal M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN)=_
  rw [Kernel.map_comp_right _ (incomingOriginal_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN) (by fun_prop),
    incomingKernel_original,prior_center]

theorem incoming_center_ae (base : Point d) :
    ∀ᵐ z ∂incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base,MeanIncomingCompletedLaw.center z.1=base := by
  have hp : MeasurePreserving (fun z : MeanIncomingCompletedLaw.History d × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN) => z.1.1.1)
      (incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base) (Measure.dirac base) := by
    refine ⟨measurable_fst.fst.fst,?_⟩
    rw [← Kernel.map_apply _ (by fun_prop),incomingKernel_center,Kernel.id_apply]
  exact hp.quasiMeasurePreserving.ae (show ∀ᵐ u ∂Measure.dirac base,u=base by simp)

variable (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
  (δ t w : ℝ) (G : Point d → Point d) (hG : Measurable G)
  (Jmain : ∀ (k : ℕ) (hk : k<meanN),FreshChildBatchCoupling.Lower L
    (MeanChronologicalCoupling.data M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hmass
      (MeanChronologicalCoupling.stage M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN k hk.le).1
      (MeanChronologicalCoupling.stage_positive M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN k hk)))
  (Jfinal : DesignatedChildBatchCoupling.Lower L (MeanFinalBatchCoupling.data M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hfinalMass))

/-- The actual main/final mean extension uses the retained original center
jointly measurably; it is not a family supplied separately at fixed centers. -/
def extension := MeanCompletedJointCenter.kernel M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hmass L hL (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jmain Jfinal

instance extension_markov : IsMarkovKernel
    (extension M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN L hL hF hell hlo hup hsmall hmass hfinalMass δ t w G hG Jmain Jfinal) := by
  unfold extension
  infer_instance

/-- The full actual private/mean augmentation, before projecting any history. -/
def fullKernel := extension M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN L hL hF hell hlo hup hsmall hmass hfinalMass δ t w G hG Jmain Jfinal ∘ₖ
  incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate
instance fullKernel_markov : IsMarkovKernel
    (fullKernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal) := by
  unfold fullKernel
  infer_instance

/-- Retain the complete canonical standalone parent seed. -/
def seed (z : (MeanChronologicalCoupling.History (d := d) M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN (MeanIncomingCompletedLaw.History d) × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) × (Fin m → Point d)) : Point d × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN) :=
  let old := MeanCompletedCoupling.original M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN z
  (old.1.1.2,old.2)
theorem seed_measurable : Measurable (seed (d := d) M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN) :=
  ((MeanCompletedCoupling.original_measurable M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN).fst.fst.snd).prodMk
    (MeanCompletedCoupling.original_measurable M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN).snd

/-- Full canonical seed and actual physical reference readout together. -/
def kernel := (fullKernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal).map
  (fun z => (seed M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN z,
    MeanCompletedJointCenter.readout M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r hr (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) hF hell hlo hup σ hσ hsmall z))
instance kernel_markov : IsMarkovKernel
    (kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal) := by
  unfold kernel
  exact Kernel.IsMarkovKernel.map _ ((seed_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN).prodMk
    (MeanCompletedJointCenter.readout_measurable M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r hr (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall))

private theorem extension_seed : (extension M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN L hL hF hell hlo hup hsmall hmass hfinalMass δ t w G hG Jmain Jfinal).map (seed M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN)=
    Kernel.deterministic (incomingSeed M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN) (incomingSeed_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN) := by
  change (extension M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN L hL hF hell hlo hup hsmall hmass hfinalMass δ t w G hG Jmain Jfinal).map ((incomingSeed M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN) ∘ MeanCompletedCoupling.original M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)=_
  unfold extension
  rw [Kernel.map_comp_right _ (MeanCompletedCoupling.original_measurable M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)
    (incomingSeed_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN),MeanCompletedJointCenter.kernel_original,Kernel.id_map]

/-- Exact first marginal on every center: the original designated Gaussian
and every canonical source tape coordinate have their standalone source law. -/
theorem kernel_source : (kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal).fst=
    Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) := by
  rw [Kernel.fst_eq,kernel,← Kernel.map_comp_right _ ((seed_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN).prodMk (MeanCompletedJointCenter.readout_measurable M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r hr (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall)) measurable_fst]
  change (fullKernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal).map (seed M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN)=_
  rw [fullKernel,Kernel.map_comp,extension_seed,Kernel.deterministic_comp_eq_map,incomingKernel_source]

/-- Measurability is joint in the actual external center and the full
standalone seed/reference distribution. -/
theorem kernel_measurable : Measurable (fun base => kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base) :=
  (kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal).measurable

/-- Exact prescribed recursive reference pair at each original center. The
actual private producer and whole-body split discharge the incoming law;
only lower retained-reference identities and deterministic row guards remain. -/
theorem kernel_reference (base : Point d) (hm : 0<m) (ht : 0<t) (q : ℝ) (hq : (1/2:ℝ)<q)
    (hretained : ∀ i y,(Jfinal.joint i y).map (fun z => (z.1.1,z.2))=
      (stdGaussian (Point d)) ⊗ₘ
        ((Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-t)).kernel.comap
          (fun p => (Conditional.RecursiveReference.childParameters hell M (MeanCompletedReference.parentTheta r σ hr hσ hsmall base) y,p)) measurable_prodMk_left))
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w) :
    (kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base).map (fun z => (z.1.1,z.2))=
      (stdGaussian (Point d)) ⊗ₘ
        ((Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht q).kernel.comap
          (fun p => (MeanCompletedReference.parentTheta r σ hr hσ hsmall base,p)) measurable_prodMk_left) := by
  let ρ := incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base
  let μ := MeanIncomingCompletedLaw.bodyPrefixLaw M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN L (MeanIncomingPrivateReferenceLaw.privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate) base
  let _ : IsProbabilityMeasure ρ := by dsimp [ρ];infer_instance
  let _ : IsProbabilityMeasure μ := by dsimp [μ];infer_instance
  have hsplit := MeanIncomingCompletedLaw.kernel_body_split M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN L (MeanIncomingPrivateReferenceLaw.privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate) base
  have hi := MeanIncomingPrivateReferenceLaw.incoming_augmented_law M hm nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate base
  have hreference := MeanCompletedJointCenter.kernel_retained_reference_law M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hmass L hL (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jmain Jfinal
    base hm ht q hq hretained ha hA ρ μ (incoming_center_ae M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base) hsplit hi
  rw [kernel,Kernel.map_apply _ ((seed_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN).prodMk (MeanCompletedJointCenter.readout_measurable M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r hr (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall)),Measure.map_map (by fun_prop) ((seed_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN).prodMk (MeanCompletedJointCenter.readout_measurable M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r hr (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall))]
  change (fullKernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base).map
    (fun z : (MeanChronologicalCoupling.History (d := d) M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN (MeanIncomingCompletedLaw.History d) × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) × (Fin m → Point d) => (MeanIncomingCompletedLaw.momentum z.1.1.1.1,MeanCompletedJointCenter.readout M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r hr (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) hF hell hlo hup σ hσ hsmall z))=_
  rw [fullKernel,Kernel.comp_apply]
  exact hreference

end AcceleratedLogConcave.Oracle.MeanStandaloneRetainedCoupling
