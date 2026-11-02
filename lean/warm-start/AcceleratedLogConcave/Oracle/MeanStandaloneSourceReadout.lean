import AcceleratedLogConcave.Oracle.MeanStandaloneAccuracyTransport
import AcceleratedLogConcave.Oracle.MeanSourceBuildRms

/-! Exact physical source readout under the already constructed standalone
projection. The original momentum and entire parent tape are the literal
ones supplied to the interpreter; no output-law replacement is used. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanStandaloneSourceReadout
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
  (privateShift : GaussianSlot (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN).program → ℝ)
local notation "Sample" => (MeanChronologicalCoupling.History (d := d) M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN (MeanIncomingCompletedLaw.History d) × Tape d (SourceMeanExecutable.program M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN)) × (Fin m → Point d)

/-- The literal full-build physical error on the completed source history. -/
def completedError (z : Sample) : Point d :=
  MeanSourceBuildRms.output (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN Ds δ t w privateShift G
    (fun z : Sample => z.1.2) (fun z : Sample => MeanIncomingCompletedLaw.momentum z.1.1.1.1) z -
      (Gibbs.primitiveMean F base r+σ • MeanCompletedReference.readout M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN r Ds hr hDs (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) (MeanIncomingCompletedLaw.position M) hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hm ht q z)

/-- Pointwise execution identity, including the primitive-mean centering and
the actual width multiplying the normalized retained reference. -/
theorem sourceError_projection (z : Sample) :
    MeanStandaloneAccuracyTransport.sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base (Gibbs.primitiveMean F base r) (MeanStandaloneAccuracyTransport.projection M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q z) =
      completedError M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q privateShift z := by
  unfold MeanStandaloneAccuracyTransport.sourceError MeanStandaloneAccuracyTransport.projection completedError
  dsimp only [FreshChildRunShift.lowerError,MeanSourceBuildRms.output,
    MeanStandaloneRetainedCoupling.seed,MeanCompletedCoupling.original,
    RetainedMeanFinalBatch.childPoint,SourceMeanExecutable.build,
    MeanJointReference.data,MeanIncomingCompletedLaw.momentum]
  rfl

/-- The completed full-build L2 payment is an L2 payment on the actual
standalone joint, retaining exactly the original full canonical source seed. -/
theorem error_memLp
    (herr : MemLp (completedError M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q privateShift) 2 (MeanStandaloneAccuracyTransport.completedLaw M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base)) :
    MemLp (MeanStandaloneAccuracyTransport.sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base (Gibbs.primitiveMean F base r)) 2 (MeanStandaloneRetainedCoupling.kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base) := by
  exact MeanStandaloneAccuracyTransport.sourceError_memLp M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q (Gibbs.primitiveMean F base r) herr


/-- Exact norm equality for the physical error used in the numerical payment. -/
theorem error_norm (herr : MemLp (completedError M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q privateShift) 2 (MeanStandaloneAccuracyTransport.completedLaw M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base)) :
    ‖(error_memLp M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q privateShift herr).toLp (MeanStandaloneAccuracyTransport.sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base (Gibbs.primitiveMean F base r))‖ =
      ‖herr.toLp (completedError M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q privateShift)‖ := by
  exact MeanStandaloneAccuracyTransport.sourceError_norm M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q (Gibbs.primitiveMean F base r) herr

/-- Exact squared physical error, expressed directly using the full-build
readout consumed by the completed RMS theorem. -/
theorem square_integral :
    (∫ z,‖MeanStandaloneAccuracyTransport.sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base (Gibbs.primitiveMean F base r) z‖^2 ∂MeanStandaloneRetainedCoupling.kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base) =
      ∫ z,‖completedError M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hF hell hlo hup hsmall hfinalMass δ t w G base hm ht q privateShift z‖^2 ∂MeanStandaloneAccuracyTransport.completedLaw M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base := by
  exact MeanStandaloneAccuracyTransport.sourceError_square_integral M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q (Gibbs.primitiveMean F base r)

end AcceleratedLogConcave.Oracle.MeanStandaloneSourceReadout
