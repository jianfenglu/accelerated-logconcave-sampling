import AcceleratedLogConcave.Oracle.MeanIncomingPrivateError

/-! Quantitative actual private-to-mean anchor transport. The private
completed accuracy producer is used at the literal same-R private geometry,
on the same complete seed read by the embedded incoming source call. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.MeanIncomingPrivateAccuracy
open Numerics Numerics.AffineGraph TapeLowering CanonicalTapeLaw CanonicalTapeMeasurability
open TailOccurrenceCut TailCut
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (path : TailCut q p) :
    MeasurableSpace (Prefix d path) := prefixSpace d path
variable {m n a h sn d : ℕ} (M : MeanGeometry m)
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


open MeanIncomingPrivateReferenceLaw
local notation "privateJ" => privateKernel M mesh snodes r Ds hr hDs smain sfinal privateN hmass hfinalMass
  L hL hF hell hlo hup Jf J
local notation "rho" => MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling meanN L privateJ
variable (δ t w : ℝ) (privateShift : GaussianSlot (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN).program → ℝ)
  {G : Point d → Point d} (hG : Measurable G)

/-- Exact finite private budget, before its manuscript scalar absorption. -/
def privateBudget (base : Point d) (κ κf : ℝ≥0)
    (amplitude : ℕ → Fin sn → ℝ) (amplitudeF : Fin sn → ℝ) : ℝ :=
  (r*((κf:ℝ)*PrivateCompletedRms.mainBudget S snodes r privateN hr hF hell hlo hup base κ amplitude) +
    ∑ i, |SourceExecutableTables.samplingFinalWeight S snodes r i| *
      PrivateCompletedRms.childPayment S snodes r hr hF hell hlo hup base i (amplitudeF i)) +
        PrivateCompletedRms.quadratureBudget S r hr hF hell hlo hup

include hG hsmall in
/-- The actual private retained execution pays the incoming stored-anchor
error from only LOWER main/final errors. For the recursive source the literal
smain/sfinal are PrivateRecursiveBatchBudget.main/final, both at q-1/4. -/
theorem anchor_square_bound (hm : 1≤m) (base : Point d) (κ κf : ℝ≥0)
    (amplitude : ℕ → Fin sn → ℝ) (amplitudeF : Fin sn → ℝ)
    (hshift : ∀ i, ChildAbsorption.QueryShift (smain i).program (smain i).enumeration (smain i).coefficient
      ((S).radius r (snodes i)) (smain i).shiftVector)
    (hshiftF : ∀ i, ChildAbsorption.QueryShift (sfinal i).program (sfinal i).enumeration (sfinal i).coefficient
      ((S).radius r (snodes i)) (sfinal i).shiftVector)
    (hstable : ∀ i, FixedTapeStability.ChildStable (smain i).program (smain i).coefficient G κ)
    (hstableF : ∀ i, FixedTapeStability.ChildStable (sfinal i).program (sfinal i).coefficient G κf)
    (hmem : ∀ k (hk : k<privateN) i y, MemLp
      (FreshChildRunShift.lowerError (smain i).program G (smain i).coefficient y
        (Gibbs.primitiveMean F y ((S).radius r (snodes i)))
        (RecursiveMeanPublicTable.mainWidth sn r (S).R Ds (r^2))) 2 ((J k hk).joint i y))
    (hbound : ∀ k (hk : k<privateN) i y, (∫ z,
      ‖FreshChildRunShift.lowerError (smain i).program G (smain i).coefficient y
        (Gibbs.primitiveMean F y ((S).radius r (snodes i)))
        (RecursiveMeanPublicTable.mainWidth sn r (S).R Ds (r^2)) z‖^2 ∂(J k hk).joint i y) ≤
          (amplitude k i*Gibbs.primitiveScale F y)^2)
    (hmemF : ∀ i y, MemLp
      (FreshChildRunShift.lowerError (sfinal i).program G (sfinal i).coefficient y
        (Gibbs.primitiveMean F y ((S).radius r (snodes i))) (SourceExecutableTables.samplingFinalWidth S r)) 2
          (Jf.joint i y))
    (hboundF : ∀ i y, (∫ z,
      ‖FreshChildRunShift.lowerError (sfinal i).program G (sfinal i).coefficient y
        (Gibbs.primitiveMean F y ((S).radius r (snodes i))) (SourceExecutableTables.samplingFinalWidth S r) z‖^2
          ∂Jf.joint i y) ≤ (amplitudeF i*Gibbs.primitiveScale F y)^2) :
    ∃ _hi : MemLp (MeanIncomingPrivateError.anchorError M nodes anchors seeds main final sampling meanN
      r σ Ds δ t w privateShift G base) 2 (rho base),
      (∫ z,‖MeanIncomingPrivateError.anchorError M nodes anchors seeds main final sampling meanN
        r σ Ds δ t w privateShift G base z‖^2 ∂rho base) ≤
          (backwardEnd M.R*privateBudget M mesh snodes r hr privateN hF hell hlo hup
            base κ κf amplitude amplitudeF)^2 := by
  obtain ⟨hmemory,hpayment⟩ := PrivateRetainedAccuracy.square_error_bound (G := G) (hG := hG)
    S snodes r Ds smain sfinal privateN hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J
    hm hsmall base κ κf amplitude amplitudeF hshift hshiftF hstable hstableF hmem hbound hmemF hboundF
  exact MeanIncomingPrivateError.anchorError_square_bound M nodes anchors seeds main final sampling meanN
    L privateJ r σ Ds δ t w privateShift G hG
    (PrivateCompletedReference.retainedKernel_fst S snodes r Ds smain sfinal privateN
      hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J) base
    (privateBudget M mesh snodes r hr privateN hF hell hlo hup base κ κf amplitude amplitudeF)
    hmemory hpayment

end AcceleratedLogConcave.Oracle.MeanIncomingPrivateAccuracy
