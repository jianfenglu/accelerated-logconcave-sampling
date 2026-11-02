import AcceleratedLogConcave.Oracle.MeanStandaloneRetainedCoupling
import AcceleratedLogConcave.Oracle.MeanAllNodeMoments
import AcceleratedLogConcave.Oracle.MeanMainErrorTransport
import AcceleratedLogConcave.Oracle.PrivateCompletedRms

/-! Actual incoming-host scale payments for MAIN lower errors. All source
projections below are consequences of the concrete native PRIVATE producer. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanActualMainPayments
open Numerics Numerics.AffineGraph AffineLowering TapeLowering SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open MeanChronologicalFinalObservation
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


local notation "sampling" => SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN
local notation "Jp" => MeanIncomingPrivateReferenceLaw.privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate
local notation "I" => MeanStandaloneRetainedCoupling.incomingKernel (d := d) M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate
local notation "coarseLaw" => MeanIncomingCompletedLaw.bodyPrefixLaw M nodes anchors seeds main final sampling meanN L Jp
local notation "C" => MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling meanN (MeanIncomingCompletedLaw.History d)
local notation "x" => MeanIncomingCompletedLaw.center (d := d)
local notation "P" => MeanIncomingCompletedLaw.momentum (d := d)
local notation "Y" => MeanIncomingCompletedLaw.position (d := d) M
local notation "D" => MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall
local notation "seed" => benchmarkSeed M nodes anchors seeds main final sampling meanN r hr x P Y hF hell hlo hup σ hσ hsmall
local notation "aug" => MeanCompletedAugmentedLaws.incomingAugmented M nodes anchors seeds main final sampling meanN r hr x P Y hF hell hlo hup σ hσ hsmall
local notation "cut" => MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling meanN
local notation "host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling meanN

/-- The actual benchmark phase seed has its full original seed law. This is
a marginal of the proved GE/phase/Pi joint, not a new assumption. -/
theorem benchmarkSeed_preserving (hm : 0<m) (base : Point d) :
    MeasurePreserving (seed base) (coarseLaw base) (MeanFlowLp.seedMeasure (D base)) := by
  have hmseed := benchmarkSeed_measurable M nodes anchors seeds main final sampling meanN r hr x P Y
    measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R))
    hF hell hlo hup σ hσ hsmall base
  refine ⟨hmseed,?_⟩
  have ha := MeanIncomingPrivateReferenceLaw.incoming_augmented_law M hm nodes anchors seeds main final
    meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL
    hF hell hlo hup hsmall JprivateFinal Jprivate base
  have hi := MeanCompletedAugmentedLaws.incomingAugmented_measurable M nodes anchors seeds main final sampling meanN r hr
    x P Y measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R))
    hF hell hlo hup σ hσ hsmall base
  have h := congrArg (fun ν => ν.map (fun z => z.1.2)) ha
  rw [Measure.map_map measurable_fst.snd hi] at h
  have hp := (measurePreserving_snd (μ := stdGaussian (Point d))
    (ν := MeanFlowLp.seedMeasure (D base))).comp
      (measurePreserving_fst
        (μ := (stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure (D base)))
        (ν := Measure.pi fun _ : Fin m => stdGaussian (Point d)))
  exact h.trans hp.map_eq

/-- The actual incoming prefix law is the prefix marginal of the full
retained source kernel; its physical center is therefore the incoming base. -/
theorem coarse_center_ae (base : Point d) : ∀ᵐ c ∂coarseLaw base, x c.1=base := by
  let : IsProbabilityMeasure (tapeLaw L (body (a := a) (h := h) M nodes main final sampling meanN)) := tapeLaw_probability L _
  have hs := MeanIncomingCompletedLaw.kernel_body_split M nodes anchors seeds main final sampling meanN L Jp base
  have hu := (CausalTailHistory.measurable_unpack (d := d) (A := MeanIncomingCompletedLaw.History d) L cut).fst
  have hp : MeasurePreserving (fun z => (CausalTailHistory.unpack cut z).1) (I base) (coarseLaw base) := by
    refine ⟨hu,?_⟩
    rw [show (fun z => (CausalTailHistory.unpack cut z).1) = Prod.fst ∘ CausalTailHistory.unpack cut by rfl,
      ← Measure.map_map measurable_fst (CausalTailHistory.measurable_unpack L cut),
      MeanStandaloneRetainedCoupling.incomingKernel, hs]
    exact (measurePreserving_fst (μ := coarseLaw base)
      (ν := tapeLaw L (body (a := a) (h := h) M nodes main final sampling meanN))).map_eq
  have hc := MeanStandaloneRetainedCoupling.incoming_center_ae M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base
  have hm : MeasurableSet {c : C | x c.1=base} :=
    measurableSet_eq_fun (measurable_fst.fst.comp measurable_fst) measurable_const
  rw [← hp.map_eq]
  exact (ae_map_iff hu.aemeasurable hm).2 hc

local notation "center" => MeanChronologicalHost.center M nodes anchors seeds main final sampling meanN x P Y hF hell hlo hup r σ hr hσ hsmall

/-- Equality uses the actual support certificate, never an equality of
fixed-base and stored-center maps away from that support. -/
theorem center_eq_seed_ae (base : Point d) (i : Fin n) :
    ∀ᵐ c ∂coarseLaw base, center i c = MeanResidualBridge.rawReference (D base) (nodes i) (seed base c) := by
  filter_upwards [coarse_center_ae M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base] with c hc
  simp only [MeanChronologicalHost.center,MeanJointReference.reference,
    MeanChronologicalHost.phaseInput,benchmarkSeed,MeanJointReference.seed]
  rw [← hc]

/-- Paid primitive-scale square on the literal coarse host. The bound is
computed from the original direct/residual analysis, not a host-budget premise. -/
theorem coarse_scale_square (hm : 0<m) (base : Point d) (h₀ : ℝ)
    (hmesh : MeanCollocationLp.MeshConditions (D base) h₀)
    (hhalf : MeanCollocationLp.contraction (D base) h₀≤1/2) (i : Fin n) :
    Integrable (fun c : C => (Gibbs.primitiveScale F (center i c))^2) (coarseLaw base) ∧
      (∫ c : C,(Gibbs.primitiveScale F (center i c))^2 ∂coarseLaw base) ≤
        MeanAllNodeMoments.scaleSquareBudget (D base) h₀ := by
  have hp := benchmarkSeed_preserving M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hm base
  have hi := MeanBenchmarkMoments.node_scale_square_integrable (D base) (nodes i)
  have he : (fun c : C => (Gibbs.primitiveScale F (center i c))^2) =ᵐ[coarseLaw base]
      (fun c => (MeanBenchmarkMoments.nodeScale (D base) (nodes i) (seed base c))^2) := by
    filter_upwards [center_eq_seed_ae M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ
      smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate base i] with c hc
    rw [hc]
    rfl
  refine ⟨(hp.integrable_comp_of_integrable hi).congr he.symm,?_⟩
  rw [integral_congr_ae he]
  have hmap := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (fun ω => MeanBenchmarkMoments.nodeScale (D base) (nodes i) ω ^ 2)
      ((coarseLaw base).map (seed base)) from hp.map_eq.symm ▸ hi.aestronglyMeasurable)
  rw [hp.map_eq] at hmap
  rw [← hmap]
  exact MeanAllNodeMoments.node_scale_square_le (D base) h₀ hmesh hhalf (nodes i)

variable (δ t w : ℝ) (G : Point d → Point d) (hG : Measurable G)
local notation "hcenter" => MeanChronologicalHost.center_measurable M nodes anchors seeds main final sampling meanN x P Y
  measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup r σ hr hσ hsmall
local notation "width" => CovarianceSetup.sigma n (RecursiveMeanPublicTable.centerNoise r M.R Ds)
  (rowBound (m := m) r σ δ t w)
local notation "err" => MeanMainErrorTransport.lowerError M nodes anchors seeds main final sampling meanN r Ds hr
  x P Y hF hell hlo hup σ hσ hsmall δ t w G

section LowerAveraging
variable (i : Fin n)
  (lower : Kernel (Point d) ((Point d × Tape d (main i).program) × Point d)) [IsMarkovKernel lower]

include hG in
/-- Every lower C is averaged on the actual complete coarse host. The
random-center square is paid by the derived source budget, not assumed. -/
theorem coarse_lower_error_bound (hm : 0<m) (base : Point d) (h₀ : ℝ)
    (hmesh : MeanCollocationLp.MeshConditions (D base) h₀)
    (hhalf : MeanCollocationLp.contraction (D base) h₀≤1/2) (amplitude : ℝ)
    (hmem : ∀ y,MemLp (FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
      (Gibbs.primitiveMean F y (M.radius r (nodes i))) width) 2 (lower y))
    (hbound : ∀ y,(∫ z,‖FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
      (Gibbs.primitiveMean F y (M.radius r (nodes i))) width z‖^2 ∂lower y) ≤
        (amplitude*Gibbs.primitiveScale F y)^2) :
    ∃ _hi : MemLp (err i) 2 ((coarseLaw base) ⊗ₘ lower.comap (center i) (hcenter i)),
      (∫ z,‖err i z‖^2 ∂((coarseLaw base) ⊗ₘ lower.comap (center i) (hcenter i))) ≤
        amplitude^2*MeanAllNodeMoments.scaleSquareBudget (D base) h₀ := by
  have hs := (MeanMainErrorTransport.lowerError_measurable M nodes anchors seeds main final sampling meanN r Ds hr
    x P Y measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R))
    hF hell hlo hup σ hσ hsmall δ t w G hG i).stronglyMeasurable
  obtain ⟨hscale,hscaleBound⟩ := coarse_scale_square M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hm base h₀ hmesh hhalf i
  have hsq : StronglyMeasurable (fun z => ‖err i z‖^2) := hs.norm.pow 2
  have hinner : StronglyMeasurable (fun c : C => ∫ z,‖err i (c,z)‖^2 ∂lower (center i c)) := by
    simpa only [Kernel.comap_apply] using
      (StronglyMeasurable.integral_kernel_prod_right
        (κ := lower.comap (center i) (hcenter i))
        (f := fun c z => ‖err i (c,z)‖^2) hsq)
  have houter : Integrable (fun c : C => ∫ z,‖err i (c,z)‖^2 ∂lower (center i c)) (coarseLaw base) := by
    apply (hscale.const_mul (amplitude^2)).mono' hinner.aestronglyMeasurable
    filter_upwards with c
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    exact (hbound (center i c)).trans_eq (by ring)
  have hint : Integrable (fun z => ‖err i z‖^2) ((coarseLaw base) ⊗ₘ lower.comap (center i) (hcenter i)) := by
    apply (Measure.integrable_compProd_iff hsq.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun c =>
        (memLp_two_iff_integrable_sq_norm (hmem (center i c)).aestronglyMeasurable).mp (hmem (center i c))
    · simpa only [Kernel.comap_apply,Real.norm_eq_abs,abs_pow,abs_norm] using houter
  refine ⟨(memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).2 hint,?_⟩
  rw [Measure.integral_compProd hint]
  calc
    _ ≤ ∫ c : C,amplitude^2*(Gibbs.primitiveScale F (center i c))^2 ∂coarseLaw base := by
      apply integral_mono houter (hscale.const_mul _)
      intro c
      exact (hbound (center i c)).trans_eq (by ring)
    _ = amplitude^2*(∫ c : C,(Gibbs.primitiveScale F (center i c))^2 ∂coarseLaw base) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hscaleBound (sq_nonneg _)
end LowerAveraging

variable (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
  (Jmain : ∀ (k : ℕ) (hk : k<meanN),FreshChildBatchCoupling.Lower L
    (MeanChronologicalCoupling.data M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hmass
      (MeanChronologicalCoupling.stage M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN k hk.le).1
      (MeanChronologicalCoupling.stage_positive M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN k hk)))
  (Jfinal : DesignatedChildBatchCoupling.Lower L
    (MeanFinalBatchCoupling.data M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hfinalMass))
local notation "full" => MeanStandaloneRetainedCoupling.fullKernel (d := d) M nodes anchors seeds main final meanN mesh snodes
  r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall
  JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal
local notation "stageErr" => MeanMainErrorTransport.stageError (d := d) (A := MeanIncomingCompletedLaw.History d) M nodes anchors seeds main final sampling meanN r Ds hr
  x P Y hF hell hlo hup σ hσ hsmall δ t w G
local notation "Xmain" => MeanChronologicalCoupling.History (d := d) M nodes anchors seeds main final sampling meanN
  (MeanIncomingCompletedLaw.History d) × Tape d host
local notation "Ω" => Xmain × (Fin m → Point d)

/-- Explicit carrier annotation prevents repeated inference through the
large native dependent source tree. This is the unchanged native full law. -/
def completedLaw (base : Point d) : Measure Ω := full base

def fixedMeasure (base : Point d) : Measure Ω :=
  MeanCompletedCoupling.kernel (d := d) (A := MeanIncomingCompletedLaw.History d) M nodes anchors seeds main final sampling meanN r Ds hr hDs hmass L hL
    x P Y measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R))
    hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jmain Jfinal ∘ₘ I base

local notation "actualLaw" => completedLaw M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ
  smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate
  δ t w G hG hmass hfinalMass Jmain Jfinal
local notation "fixedLaw" => fixedMeasure M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ
  smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate
  δ t w G hG hmass hfinalMass Jmain Jfinal

/-- The native jointly measurable completed producer is compared to its
fixed-base analysis only under its proved actual incoming center support. -/
theorem full_law_eq_fixed (base : Point d) : actualLaw base = fixedLaw base := by
  unfold completedLaw fixedMeasure
  rw [MeanStandaloneRetainedCoupling.fullKernel,Kernel.comp_apply,MeanStandaloneRetainedCoupling.extension]
  exact MeanCompletedJointCenter.law_eq_fixed (d := d) (A := MeanIncomingCompletedLaw.History d) M nodes anchors seeds main final sampling meanN r Ds hr hDs hmass L hL
    x P Y measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R))
    hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jmain Jfinal base (I base)
    (MeanStandaloneRetainedCoupling.incoming_center_ae M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs
      smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base)

/-- Every literal past MAIN error has its lower error law on the SAME full
completed source/history joint, after the paid final batch. -/
theorem completed_error_law (base : Point d) (k : ℕ) (hk : k<meanN) (i : Fin n)
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (M.radius r (nodes i)) (main i).shiftVector) :
    (actualLaw base).map ((stageErr k hk i) ∘ Prod.fst) =
      ((coarseLaw base) ⊗ₘ ((Jmain k hk).joint i).comap (center i) (hcenter i)).map (err i) := by
  rw [full_law_eq_fixed M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate
    δ t w G hG hmass hfinalMass Jmain Jfinal base]
  unfold fixedMeasure
  exact MeanMainErrorTransport.completed_error_law M nodes anchors seeds main final sampling meanN r Ds hr hDs hmass L hL
    x P Y measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall
    δ t w Jmain G hG ha hA (I base) (coarseLaw base)
    (MeanIncomingCompletedLaw.kernel_body_split M nodes anchors seeds main final sampling meanN L Jp base)
    base hfinalMass Jfinal k hk i hshift

/-- All k<meanN lower C payments on the actual native completed producer.
Only LOWER full-source errors enter. The explicit original-data mesh and
half-contraction guards pay the actual random-center envelope. -/
theorem completed_error_bound (hm : 0<m) (base : Point d) (h₀ : ℝ)
    (hmesh : MeanCollocationLp.MeshConditions (D base) h₀)
    (hhalf : MeanCollocationLp.contraction (D base) h₀≤1/2)
    (k : ℕ) (hk : k<meanN) (i : Fin n) (amplitude : ℝ)
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (M.radius r (nodes i)) (main i).shiftVector)
    (hmem : ∀ y,MemLp (FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
      (Gibbs.primitiveMean F y (M.radius r (nodes i))) width) 2 ((Jmain k hk).joint i y))
    (hbound : ∀ y,(∫ z,‖FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
      (Gibbs.primitiveMean F y (M.radius r (nodes i))) width z‖^2 ∂(Jmain k hk).joint i y) ≤
        (amplitude*Gibbs.primitiveScale F y)^2) :
    ∃ _hi : MemLp ((stageErr k hk i) ∘ Prod.fst) 2 (actualLaw base),
      (∫ z : Ω,‖stageErr k hk i z.1‖^2 ∂actualLaw base) ≤
        amplitude^2*MeanAllNodeMoments.scaleSquareBudget (D base) h₀ := by
  let : IsMarkovKernel ((Jmain k hk).joint i) := (Jmain k hk).markov i
  obtain ⟨hi,hB⟩ := coarse_lower_error_bound M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate
    δ t w G hG i ((Jmain k hk).joint i) hm base h₀ hmesh hhalf amplitude hmem hbound
  have hlaw := completed_error_law M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate
    δ t w G hG hmass hfinalMass Jmain Jfinal base k hk i ha hA hshift
  have hf : Measurable (fun z : Ω => stageErr k hk i z.1) := (MeanMainErrorTransport.stageError_measurable M nodes anchors seeds main final sampling meanN r Ds hr hDs hmass L
    x P Y measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall
    δ t w G hG k hk i).comp measurable_fst
  have hg := MeanMainErrorTransport.lowerError_measurable M nodes anchors seeds main final sampling meanN r Ds hr
    x P Y measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall
    δ t w G hG i
  obtain ⟨hmemOut,he⟩ := PrivateCompletedRms.memLp_integral_of_law _ _ _ _ hf hg hlaw hi
  exact ⟨hmemOut,he.le.trans hB⟩

end AcceleratedLogConcave.Oracle.MeanActualMainPayments
