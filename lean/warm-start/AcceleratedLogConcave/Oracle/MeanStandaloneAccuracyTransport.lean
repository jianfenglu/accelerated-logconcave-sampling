import AcceleratedLogConcave.Oracle.MeanStandaloneRetainedCoupling
import AcceleratedLogConcave.Oracle.RecursiveRetainedAccuracy

/-! Transport from the actual completed mean history to the same standalone
retained kernel. The original designated input and every source coordinate
remain unchanged; only the already constructed reference is projected. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanStandaloneAccuracyTransport
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

variable (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
  (δ t w : ℝ) (G : Point d → Point d) (hG : Measurable G)
  (Jmain : ∀ (k : ℕ) (hk : k<meanN),FreshChildBatchCoupling.Lower L
    (MeanChronologicalCoupling.data M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hmass
      (MeanChronologicalCoupling.stage M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN k hk.le).1
      (MeanChronologicalCoupling.stage_positive M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN k hk)))
  (Jfinal : DesignatedChildBatchCoupling.Lower L (MeanFinalBatchCoupling.data M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hfinalMass))


variable (base : Point d) (hm : 0<m) (ht : 0<t) (q : ℝ)
local notation "Sample" => (MeanChronologicalCoupling.History (d := d) M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN (MeanIncomingCompletedLaw.History d) × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) × (Fin m → Point d)

/-- Fixed-center completed law with the literal incoming private augmentation. -/
def completedLaw : Measure Sample :=
  MeanCompletedCoupling.kernel M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hmass L hL (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jmain Jfinal ∘ₘ (MeanStandaloneRetainedCoupling.incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base)

/-- Full original seed and the fixed-center completed reference. -/
def projection (z : Sample) := (MeanStandaloneRetainedCoupling.seed M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN z,MeanCompletedReference.readout M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hm ht q z)

include L hG in
theorem projection_measurable : Measurable (projection M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q) :=
  (MeanStandaloneRetainedCoupling.seed_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN).prodMk (MeanCompletedReference.readout_measurable M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs L (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG hm ht q)

/-- The dynamic-center standalone source is exactly the fixed-center
completed law under this same full-seed/reference projection. -/
theorem kernel_eq_completed_map :
    MeanStandaloneRetainedCoupling.kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base =
      (completedLaw M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base).map
        (projection M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q) := by
  let ρ := MeanStandaloneRetainedCoupling.incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base
  have hρ := MeanStandaloneRetainedCoupling.incoming_center_ae M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base
  have he := MeanCompletedJointCenter.law_eq_fixed M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hmass L hL (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jmain Jfinal base ρ hρ
  have hc := MeanCompletedJointCenter.center_ae M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hmass L hL (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jmain Jfinal base ρ hρ
  rw [MeanStandaloneRetainedCoupling.kernel,Kernel.map_apply _ ((MeanStandaloneRetainedCoupling.seed_measurable M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN).prodMk (MeanCompletedJointCenter.readout_measurable M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r hr (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall))]
  change (MeanCompletedJointCenter.kernel M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs hmass L hL (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) measurable_fst.fst measurable_fst.snd (measurable_snd.const_smul (backwardEnd M.R)) hF hell hlo hup σ hσ hsmall δ t w hfinalMass G hG Jmain Jfinal ∘ₘ ρ).map (fun z : Sample => (MeanStandaloneRetainedCoupling.seed M nodes anchors seeds main final meanN mesh snodes r Ds smain sfinal privateN z,MeanCompletedJointCenter.readout M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r hr (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) hF hell hlo hup σ hσ hsmall z)) = _
  rw [he]
  apply Measure.map_congr
  rw [he] at hc
  filter_upwards [hc] with z hz
  exact Prod.ext rfl (MeanCompletedJointCenter.readout_eq_fixed M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) hF hell hlo hup σ hσ hsmall δ t w hfinalMass G base hm ht q z hz)

/-- Exact measure-preserving projection of the literal completed augmentation. -/
theorem projection_preserving : MeasurePreserving (projection M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q) (completedLaw M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base) (MeanStandaloneRetainedCoupling.kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base) := by
  refine ⟨projection_measurable M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN L hF hell hlo hup hsmall hfinalMass δ t w G hG base hm ht q,?_⟩
  exact (kernel_eq_completed_map M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q).symm

/-- Literal full-source error, at any fixed physical target mean u. -/
def sourceError (u : Point d)
    (z : (Point d × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) × Point d) : Point d :=
  FreshChildRunShift.lowerError (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)
    G (SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN)) base u σ z

include hG in
theorem sourceError_measurable (u : Point d) : Measurable
    (sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base u) := by
  have hp := CanonicalTapeMeasurability.program_point_of_measurable
    (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN) G hG
    (fun _ => SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN))
    (fun _ => base)
    (fun z : (Point d × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) × Point d => z.1.1)
    (fun z => z.1.2) measurable_const measurable_const measurable_fst.fst measurable_fst.snd
  exact hp.sub (measurable_const.add (measurable_snd.const_smul σ))

/-- L2 membership transfers from the actual completed source error to the
same standalone retained kernel, with physical normalization unchanged. -/
theorem sourceError_memLp (u : Point d)
    (herr : MemLp ((sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base u) ∘ (projection M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q)) 2 (completedLaw M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base)) :
    MemLp (sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base u) 2 (MeanStandaloneRetainedCoupling.kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base) := by
  have hp := projection_preserving M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q
  have hf := sourceError_measurable M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G hG base u
  rw [kernel_eq_completed_map M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q]
  exact (memLp_map_measure_iff hf.aestronglyMeasurable hp.aemeasurable).2 herr

/-- Exact squared error transport, before any numerical relaxation. -/
theorem sourceError_square_integral (u : Point d) :
    (∫ z,‖sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base u z‖^2 ∂MeanStandaloneRetainedCoupling.kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base) =
      ∫ z,‖sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base u (projection M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q z)‖^2 ∂completedLaw M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base := by
  have hp := projection_preserving M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q
  have hf := sourceError_measurable M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G hG base u
  rw [kernel_eq_completed_map M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q]
  exact integral_map hp.aemeasurable (hf.norm.pow_const 2).aestronglyMeasurable

/-- Exact L2 norm transport for the same physical error. -/
theorem sourceError_norm (u : Point d)
    (herr : MemLp ((sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base u) ∘ (projection M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q)) 2 (completedLaw M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base)) :
    ‖(sourceError_memLp M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q u herr).toLp (sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base u)‖ =
      ‖herr.toLp ((sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base u) ∘ (projection M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q))‖ := by
  have hp := projection_preserving M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q
  have hf := sourceError_measurable M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G hG base u
  simp only [Lp.norm_toLp]
  exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hp).symm

end AcceleratedLogConcave.Oracle.MeanStandaloneAccuracyTransport
