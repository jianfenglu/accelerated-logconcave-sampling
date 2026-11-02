import AcceleratedLogConcave.Oracle.MeanIncomingCompletedLaw

/-! The actual private completed producer supplies the incoming mean law.
Its geometry is the literal same-R private helper, and the original full source
and every unread body coordinate are retained by the incoming kernel. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanIncomingPrivateReferenceLaw
open Numerics Numerics.AffineGraph TapeLowering CanonicalTapeLaw CanonicalTapeMeasurability
open TailOccurrenceCut TailCut
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (path : TailCut q p) :
    MeasurableSpace (Prefix d path) := prefixSpace d path
variable {m n a h sn d : ℕ} (M : MeanGeometry m) (hm : 0<m)
  (nodes : Fin n ≃ M.MeanNode) (anchors : Fin a ≃ M.Anchor)
  (seeds : Fin h ≃ Fin m × M.Kernel) (main : Fin n → ExecutableData)
  (final : Fin m → ExecutableData) (meanN : ℕ)
  (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
  (snodes : Fin sn ≃ (RecursiveExecutable.privateGeometry M mesh).Node)
  (r Ds σ : ℝ) (hr : 0<r) (hDs : 0<Ds) (hσ : 0<σ)
  (smain sfinal : Fin sn → ExecutableData) (privateN : ℕ)
  (hmass : ∀ i,CovarianceSetup.shiftSq (smain i).shiftVector≤Ds^2)
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (sfinal i).shiftVector≤Ds^2)
  (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (hsmall : r^2*ell≤1/2)
local notation "S" => RecursiveExecutable.privateGeometry M mesh
local notation "sampling" => SamplingExecutable.build S snodes r Ds smain sfinal privateN
variable
  (Jf : FreshChildBatchCoupling.Lower L
    (PrivateFinalCoupling.data (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN hr hDs hfinalMass
      (PrivateChronologicalCoupling.terminalCursor (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN).old))
  (J : ∀ (k : ℕ) (hk : k<privateN),FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN hr hDs hmass
      (PrivateChronologicalCoupling.stage (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN k hk.le).1
      (PrivateChronologicalCoupling.stage_positive (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN k hk)))

/-- Actual complete private retained kernel, at the source's prescribed geometry. -/
def privateKernel := PrivateCompletedReference.retainedKernel S snodes r Ds smain sfinal privateN
  hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J

instance privateKernel_markov : IsMarkovKernel
    (privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hmass hfinalMass L hL
      hF hell hlo hup Jf J) := inferInstanceAs (IsMarkovKernel
        (PrivateCompletedReference.retainedKernel S snodes r Ds smain sfinal privateN
          hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J))

include hm in
/-- The incoming chronology premise is discharged by actual lower private
execution and literal Gaussian assembly. No independent reference is substituted. -/
theorem incoming_augmented_law (base : Point d) :
    (MeanIncomingCompletedLaw.bodyPrefixLaw M nodes anchors seeds main final sampling meanN L
      (privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hmass hfinalMass L hL
        hF hell hlo hup Jf J) base).map
      (MeanCompletedAugmentedLaws.incomingAugmented M nodes anchors seeds main final sampling meanN r hr
        (MeanIncomingCompletedLaw.center (d := d)) (MeanIncomingCompletedLaw.momentum (d := d))
        (MeanIncomingCompletedLaw.position M) hF hell hlo hup σ hσ hsmall base) =
      ((stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure
        (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base))).prod
          (Measure.pi fun _ : Fin m => stdGaussian (Point d)) := by
  exact MeanIncomingCompletedLaw.incoming_augmented_law M nodes anchors seeds main final sampling meanN L
    (privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hmass hfinalMass L hL
      hF hell hlo hup Jf J) hL hF hell hlo hup r σ hr hσ hsmall
    (PrivateCompletedReference.retainedKernel_fst S snodes r Ds smain sfinal privateN
      hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J) base
    (PrivateCompletedReference.retainedKernel_reference S snodes r Ds smain sfinal privateN
      hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J hm base)

end AcceleratedLogConcave.Oracle.MeanIncomingPrivateReferenceLaw
