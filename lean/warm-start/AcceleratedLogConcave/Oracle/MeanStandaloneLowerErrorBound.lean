import AcceleratedLogConcave.Oracle.MeanStandaloneSourceReadout
import AcceleratedLogConcave.Oracle.MeanCompletedSourceRms
import AcceleratedLogConcave.Oracle.MeanActualMainPayments
import AcceleratedLogConcave.Oracle.MeanPrivateBudgetNonnegative
import AcceleratedLogConcave.Oracle.MeanStandaloneAnchorAccuracy

/-! Concrete complete-source RMS composition for the already constructed
standalone joint. All incoming laws are the actual private producer; the
remaining errors belong only to strictly lower child joints. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.MeanStandaloneLowerErrorBound
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


/-- A physical LOWER-fibre second-moment bound on an exact supplied joint. -/
def Fiber (E : ExecutableData)
    (J : Kernel (Point d) ((Point d × Tape d E.program) × Point d))
    (radius width amplitude : ℝ) : Prop :=
  ∀ y : Point d,MemLp (FreshChildRunShift.lowerError E.program G E.coefficient y
    (Gibbs.primitiveMean F y radius) width) 2 (J y) ∧
    (∫ z,‖FreshChildRunShift.lowerError E.program G E.coefficient y
      (Gibbs.primitiveMean F y radius) width z‖^2 ∂J y)≤(amplitude*Gibbs.primitiveScale F y)^2

variable (base : Point d) (hm : 0<m) (ht : 0<t) (q : ℝ)
  (privateShift : GaussianSlot (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN).program → ℝ)

include hm ht q in
/-- Once the genuinely lower private anchor is paid on the actual incoming
law, complete-source RMS and exact readout transport give this same joint's
physical error. This internal composition introduces no alternate history law. -/
private theorem output_of_anchor (h₀ : ℝ)
    (hmesh : Numerics.MeanCollocationLp.MeshConditions (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) h₀)
    (hhalf : Numerics.MeanCollocationLp.contraction (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) h₀≤1/2)
    (ha : 0<SourceMeanExecutable.rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤SourceMeanExecutable.rowBound (m := m) r σ δ t w)
    (hpsi : M.psi≤M.R^4) (κ κf : ℝ≥0) (Eprivate : ℝ)
    (hanchor : MemLp (MeanCompletedSourceRms.incomingAnchorError (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN Ds δ t w
      (MeanIncomingCompletedLaw.momentum (d := d)) Prod.snd G privateShift) 2 (MeanStandaloneRetainedCoupling.incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base))
    (hanchorBound : ‖hanchor.toLp _‖≤Eprivate)
    (amplitude : ℕ → Fin n → ℝ) (amplitudeFinal : Fin m → ℝ)
    (hstable : ∀ i,FixedTapeStability.ChildStable (main i).program (main i).coefficient G κ)
    (hfinalStable : ∀ i,FixedTapeStability.ChildStable (final i).program (final i).coefficient G κf)
    (hshift : ∀ i,ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (M.radius r (nodes i)) (main i).shiftVector)
    (hfinalShift : ∀ i,ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (r*M.R) (final i).shiftVector)
    (hmain : ∀ k (hk : k<meanN) i,Fiber (F := F) G (main i) ((Jmain k hk).joint i)
      (M.radius r (nodes i)) (CovarianceSetup.sigma n (RecursiveMeanPublicTable.centerNoise r M.R Ds) (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) (amplitude k i))
    (hfinal : ∀ i,Fiber (F := F) G (final i) (Jfinal.joint i) (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (amplitudeFinal i)) :
    ∃ hout : MemLp (MeanStandaloneAccuracyTransport.sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base (Gibbs.primitiveMean F base r)) 2 (MeanStandaloneRetainedCoupling.kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base),‖hout.toLp _‖≤MeanCompletedSourceRms.outputBudget (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) nodes meanN h₀ κ κf (SourceMeanExecutable.rowBound (m := m) r σ δ t w) Eprivate amplitude amplitudeFinal := by
  let ρ := MeanStandaloneRetainedCoupling.incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base
  let μ := MeanIncomingCompletedLaw.bodyPrefixLaw M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN L (MeanIncomingPrivateReferenceLaw.privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate) base
  let _ : IsProbabilityMeasure ρ := by dsimp [ρ];infer_instance
  let _ : IsProbabilityMeasure μ := by dsimp [μ];infer_instance
  have hbaseρ := MeanStandaloneRetainedCoupling.incoming_center_ae M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base
  have hbaseμ := MeanActualMainPayments.coarse_center_ae M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate base
  have hsplit := MeanIncomingCompletedLaw.kernel_body_split M nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN L (MeanIncomingPrivateReferenceLaw.privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup JprivateFinal Jprivate) base
  have hincoming := MeanIncomingPrivateReferenceLaw.incoming_augmented_law M hm nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate base
  obtain ⟨hi,hbound⟩ := MeanCompletedSourceRms.output_error_bound (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) nodes anchors seeds main final (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN) meanN Ds δ t w hDs hmass
    (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d)) Prod.snd
    measurable_fst.fst measurable_fst.snd measurable_snd L hL Jmain hfinalMass G hG Jfinal ρ hbaseρ privateShift μ hbaseμ
    ha hA hsplit hincoming hm ht q h₀ hmesh hhalf hpsi κ κf Eprivate hanchor hanchorBound amplitude amplitudeFinal
    hstable hfinalStable hshift hfinalShift
    (fun k hk i y => (hmain k hk i y).1) (fun k hk i y => (hmain k hk i y).2)
    (fun i y => (hfinal i y).1) (fun i y => (hfinal i y).2)
  let hout := MeanStandaloneSourceReadout.error_memLp M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q privateShift hi
  refine ⟨hout,?_⟩
  rw [MeanStandaloneSourceReadout.error_norm M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q privateShift hi]
  exact hbound

include hm ht q in
/-- Complete physical error of the SAME actual standalone joint, paid from
all four LOWER child families and the explicit finite private budget. Source
and coarse laws, original-center support and every readout transport are
derived internally from the actual private/mean construction. -/
theorem output_error_bound (h₀ : ℝ)
    (hmesh : Numerics.MeanCollocationLp.MeshConditions (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) h₀)
    (hhalf : Numerics.MeanCollocationLp.contraction (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) h₀≤1/2)
    (ha : 0<SourceMeanExecutable.rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤SourceMeanExecutable.rowBound (m := m) r σ δ t w)
    (hpsi : M.psi≤M.R^4) (κ κf : ℝ≥0) (Eprivate : ℝ)
    (amplitude : ℕ → Fin n → ℝ) (amplitudeFinal : Fin m → ℝ)
    (hstable : ∀ i,FixedTapeStability.ChildStable (main i).program (main i).coefficient G κ)
    (hfinalStable : ∀ i,FixedTapeStability.ChildStable (final i).program (final i).coefficient G κf)
    (hshift : ∀ i,ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (M.radius r (nodes i)) (main i).shiftVector)
    (hfinalShift : ∀ i,ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (r*M.R) (final i).shiftVector)
    (hmain : ∀ k (hk : k<meanN) i,Fiber (F := F) G (main i) ((Jmain k hk).joint i)
      (M.radius r (nodes i)) (CovarianceSetup.sigma n (RecursiveMeanPublicTable.centerNoise r M.R Ds) (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) (amplitude k i))
    (hfinal : ∀ i,Fiber (F := F) G (final i) (Jfinal.joint i) (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (amplitudeFinal i))
    (amplitudePrivate : ℕ → Fin sn → ℝ) (amplitudePrivateFinal : Fin sn → ℝ)
    (hprivatePayment : (backwardEnd M.R*MeanIncomingPrivateAccuracy.privateBudget M mesh snodes r hr privateN hF hell hlo hup base κ κf amplitudePrivate amplitudePrivateFinal)≤Eprivate)
    (hprivateShift : ∀ i,ChildAbsorption.QueryShift (smain i).program (smain i).enumeration (smain i).coefficient
      ((RecursiveExecutable.privateGeometry M mesh).radius r (snodes i)) (smain i).shiftVector)
    (hprivateFinalShift : ∀ i,ChildAbsorption.QueryShift (sfinal i).program (sfinal i).enumeration (sfinal i).coefficient
      ((RecursiveExecutable.privateGeometry M mesh).radius r (snodes i)) (sfinal i).shiftVector)
    (hprivateStable : ∀ i,FixedTapeStability.ChildStable (smain i).program (smain i).coefficient G κ)
    (hprivateFinalStable : ∀ i,FixedTapeStability.ChildStable (sfinal i).program (sfinal i).coefficient G κf)
    (hprivateMain : ∀ k (hk : k<privateN) i,Fiber (F := F) G (smain i) ((Jprivate k hk).joint i)
      ((RecursiveExecutable.privateGeometry M mesh).radius r (snodes i)) (RecursiveMeanPublicTable.mainWidth sn r (RecursiveExecutable.privateGeometry M mesh).R Ds (r^2)) (amplitudePrivate k i))
    (hprivateFinal : ∀ i,Fiber (F := F) G (sfinal i) (JprivateFinal.joint i)
      ((RecursiveExecutable.privateGeometry M mesh).radius r (snodes i)) (SourceExecutableTables.samplingFinalWidth (RecursiveExecutable.privateGeometry M mesh) r) (amplitudePrivateFinal i)) :
    ∃ hout : MemLp (MeanStandaloneAccuracyTransport.sourceError M nodes anchors seeds main final meanN mesh snodes r Ds σ smain sfinal privateN δ t w G base (Gibbs.primitiveMean F base r)) 2 (MeanStandaloneRetainedCoupling.kernel M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base),‖hout.toLp _‖≤MeanCompletedSourceRms.outputBudget (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) nodes meanN h₀ κ κf (SourceMeanExecutable.rowBound (m := m) r σ δ t w) Eprivate amplitude amplitudeFinal := by
  let privateShift := (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN).shift
  obtain ⟨hanchor,hanchorSq⟩ := MeanStandaloneAnchorAccuracy.anchor_square_bound M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ
    smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate δ t w G hG privateShift
    (by omega : 1≤m) base κ κf amplitudePrivate amplitudePrivateFinal
    hprivateShift hprivateFinalShift hprivateStable hprivateFinalStable
    (fun k hk i y => (hprivateMain k hk i y).1) (fun k hk i y => (hprivateMain k hk i y).2)
    (fun i y => (hprivateFinal i y).1) (fun i y => (hprivateFinal i y).2)
  have hB := MeanPrivateBudgetNonnegative.scaled_privateBudget_nonneg M mesh snodes r hr privateN hF hell hlo hup
    base κ κf amplitudePrivate amplitudePrivateFinal
  have hnorm := FreshChildBatchErrorTransfer.norm_toLp_le_of_square_integral _ _ hanchor (backwardEnd M.R*MeanIncomingPrivateAccuracy.privateBudget M mesh snodes r hr privateN hF hell hlo hup base κ κf amplitudePrivate amplitudePrivateFinal) hB hanchorSq
  exact output_of_anchor M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs hσ smain sfinal privateN hprivateMass hprivateFinalMass L hL hF hell hlo hup hsmall JprivateFinal Jprivate hmass hfinalMass δ t w G hG Jmain Jfinal base hm ht q privateShift h₀ hmesh hhalf ha hA hpsi κ κf Eprivate hanchor (hnorm.trans hprivatePayment)
    amplitude amplitudeFinal hstable hfinalStable hshift hfinalShift hmain hfinal

end AcceleratedLogConcave.Oracle.MeanStandaloneLowerErrorBound
