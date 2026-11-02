import AcceleratedLogConcave.Oracle.MeanCompletedSourceRms
import AcceleratedLogConcave.Oracle.MeanStandaloneRetainedCoupling
import AcceleratedLogConcave.Oracle.MeanIncomingSourcePayments

/-! Actual lower-private accuracy supplies the incoming anchor of the SAME
standalone mean coupling. The source specialization fixes tau=R/backwardEnd R,
all private lower precisions q-1/4 and their constant-four widths; it assumes
only lower full-seed errors, never current private or parent accuracy. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.MeanStandaloneAnchorAccuracy
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open CanonicalTapeLaw CanonicalTapeMeasurability
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
section General
variable {m n a h sn D : ℕ} (M : MeanGeometry m)
  (nodes : Fin n ≃ M.MeanNode) (anchors : Fin a ≃ M.Anchor)
  (seeds : Fin h ≃ Fin m × M.Kernel) (main : Fin n → ExecutableData)
  (final : Fin m → ExecutableData) (meanN : ℕ)
  (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
  (snodes : Fin sn ≃ (RecursiveExecutable.privateGeometry M mesh).Node)
  (r Ds σ : ℝ) (hr : 0<r) (hDs : 0<Ds) (hσ : 0<σ)
  (smain sfinal : Fin sn → ExecutableData) (privateN : ℕ)
  (hmass : ∀ i,CovarianceSetup.shiftSq (smain i).shiftVector≤Ds^2)
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (sfinal i).shiftVector≤Ds^2)
  (L : PrimitiveLaws D) (hL : L.pointDraw=stdGaussian (Point D))
  {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (hsmall : r^2*ell≤1/2)
  (Jf : FreshChildBatchCoupling.Lower L
    (PrivateFinalCoupling.data (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN hr hDs hfinalMass
      (PrivateChronologicalCoupling.terminalCursor (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN).old))
  (J : ∀ (k : ℕ) (hk : k<privateN),FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN hr hDs hmass
      (PrivateChronologicalCoupling.stage (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN k hk.le).1
      (PrivateChronologicalCoupling.stage_positive (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN k hk)))
  (δ t w : ℝ) (G : Point D → Point D) (hG : Measurable G)
  (privateShift : GaussianSlot (SamplingExecutable.build (RecursiveExecutable.privateGeometry M mesh) snodes r Ds smain sfinal privateN).program → ℝ)
local notation "S" => RecursiveExecutable.privateGeometry M mesh
local notation "sampling" => SamplingExecutable.build S snodes r Ds smain sfinal privateN
local notation "Host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling meanN
local notation "Sample" => MeanIncomingCompletedLaw.History D × Tape D Host

/-- Exactly the actual standalone incoming law, constructed from the lower
private full-source joints and retaining every parent tape coordinate. -/
def incomingLaw (base : Point D) : Measure Sample :=
  MeanStandaloneRetainedCoupling.incomingKernel M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN
    hmass hfinalMass L hL hF hell hlo hup Jf J base

/-- The RMS consumer's literal anchor error with raw private reference V. -/
def error (base : Point D) : Sample → Point D :=
  MeanCompletedSourceRms.incomingAnchorError (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)
    nodes anchors seeds main final sampling meanN Ds δ t w (MeanIncomingCompletedLaw.momentum (d := D)) Prod.snd G privateShift

/-- The two existing readouts differ only by distributing the same scalar. -/
theorem error_eq (base : Point D) : error M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hσ smain sfinal privateN
    hF hell hlo hup hsmall δ t w G privateShift base =
    MeanIncomingPrivateError.anchorError M nodes anchors seeds main final sampling meanN r σ Ds δ t w privateShift G base := by
  funext z
  change backwardEnd M.R • (SourceMeanBuildRms.privateResult M nodes anchors seeds r σ Ds δ t w main final sampling meanN
      privateShift G base z.1.1.2 z.2-z.1.2)=_
  exact smul_sub _ _ _

include hG hsmall in
/-- Actual standalone incoming private-anchor square payment from genuinely
LOWER private main/final errors on the exact supplied lower joints. -/
theorem anchor_square_bound (hm : 1≤m) (base : Point D) (κ κf : ℝ≥0)
    (amplitude : ℕ → Fin sn → ℝ) (amplitudeF : Fin sn → ℝ)
    (hshift : ∀ i,ChildAbsorption.QueryShift (smain i).program (smain i).enumeration (smain i).coefficient
      ((S).radius r (snodes i)) (smain i).shiftVector)
    (hshiftF : ∀ i,ChildAbsorption.QueryShift (sfinal i).program (sfinal i).enumeration (sfinal i).coefficient
      ((S).radius r (snodes i)) (sfinal i).shiftVector)
    (hstable : ∀ i,FixedTapeStability.ChildStable (smain i).program (smain i).coefficient G κ)
    (hstableF : ∀ i,FixedTapeStability.ChildStable (sfinal i).program (sfinal i).coefficient G κf)
    (hmem : ∀ k (hk : k<privateN) i y,MemLp (FreshChildRunShift.lowerError (smain i).program G (smain i).coefficient y
      (Gibbs.primitiveMean F y ((S).radius r (snodes i)))
      (RecursiveMeanPublicTable.mainWidth sn r (S).R Ds (r^2))) 2 ((J k hk).joint i y))
    (hbound : ∀ k (hk : k<privateN) i y,(∫ z,‖FreshChildRunShift.lowerError (smain i).program G (smain i).coefficient y
      (Gibbs.primitiveMean F y ((S).radius r (snodes i)))
      (RecursiveMeanPublicTable.mainWidth sn r (S).R Ds (r^2)) z‖^2 ∂(J k hk).joint i y)≤(amplitude k i*Gibbs.primitiveScale F y)^2)
    (hmemF : ∀ i y,MemLp (FreshChildRunShift.lowerError (sfinal i).program G (sfinal i).coefficient y
      (Gibbs.primitiveMean F y ((S).radius r (snodes i))) (SourceExecutableTables.samplingFinalWidth S r)) 2 (Jf.joint i y))
    (hboundF : ∀ i y,(∫ z,‖FreshChildRunShift.lowerError (sfinal i).program G (sfinal i).coefficient y
      (Gibbs.primitiveMean F y ((S).radius r (snodes i))) (SourceExecutableTables.samplingFinalWidth S r) z‖^2 ∂Jf.joint i y)≤
        (amplitudeF i*Gibbs.primitiveScale F y)^2) :
    ∃ _hi : MemLp (error M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hσ smain sfinal privateN hF hell hlo hup hsmall δ t w G privateShift base) 2
      (incomingLaw M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hmass hfinalMass L hL hF hell hlo hup Jf J base),
      (∫ z,‖error M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hσ smain sfinal privateN hF hell hlo hup hsmall δ t w G privateShift base z‖^2
        ∂incomingLaw M nodes anchors seeds main final meanN mesh snodes r Ds hr hDs smain sfinal privateN hmass hfinalMass L hL hF hell hlo hup Jf J base)≤
        (backwardEnd M.R*MeanIncomingPrivateAccuracy.privateBudget M mesh snodes r hr privateN hF hell hlo hup base κ κf amplitude amplitudeF)^2 := by
  obtain ⟨hi,hb⟩ := MeanIncomingPrivateAccuracy.anchor_square_bound M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hDs
    smain sfinal privateN hmass hfinalMass L hL hF hell hlo hup hsmall Jf J δ t w privateShift hG hm base κ κf amplitude amplitudeF
    hshift hshiftF hstable hstableF hmem hbound hmemF hboundF
  rw [error_eq M nodes anchors seeds main final meanN mesh snodes r Ds σ hr hσ smain sfinal privateN hF hell hlo hup hsmall δ t w G privateShift base]
  exact ⟨hi,hb⟩

end General

section Prescribed
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hcsmall hC baseHy
local notation "M" => PrescribedSourceGeometry.meanGeometry P.m P.R P.h0 P.R_pos hR P.h0_pos
local notation "mesh" => PrescribedSourceGeometry.privateMesh P.R P.h0 P.R_pos hR P.h0_pos
local notation "S" => PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos hR P.h0_pos

include hK hc hcsmall hC hy in
/-- The original source curvature domain and radius cap imply the actual
private curvature guard; no call accuracy enters this implication. -/
theorem source_curvature {ell r : ℝ} (hell : 0≤ell) (hr : 0<r) (hr1 : r≤1) (hellδ : ell≤P.delta) :
    r^2*ell≤1/2 := by
  have hd := PrivateSourceScalarAbsorption.delta_le_hundredth P hK hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
  have hr2 : r^2≤1 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hr2 hell
  nlinarith

variable {n a h sn D : ℕ}
  (nodes : Fin n ≃ (PrescribedSourceGeometry.meanGeometry P.m P.R P.h0 P.R_pos (CubicSchedulePayments.radius_guard P hK hc hcsmall hC (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos).MeanNode)
  (anchors : Fin a ≃ (PrescribedSourceGeometry.meanGeometry P.m P.R P.h0 P.R_pos (CubicSchedulePayments.radius_guard P hK hc hcsmall hC (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos).Anchor)
  (seeds : Fin h ≃ Fin P.m × (PrescribedSourceGeometry.meanGeometry P.m P.R P.h0 P.R_pos (CubicSchedulePayments.radius_guard P hK hc hcsmall hC (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos).Kernel)
  (snodes : Fin sn ≃ (PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos (CubicSchedulePayments.radius_guard P hK hc hcsmall hC (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos).Node)
  (main : Fin n → ExecutableData) (final : Fin P.m → ExecutableData)
  (smain sfinal : Fin sn → ExecutableData)
  (r σ : ℝ) (hr : 0<r) (hσ : 0<σ) (hr1 : r≤1)
  {F : Point D → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (hellδ : ell≤P.delta)
  (hmass : ∀ i,CovarianceSetup.shiftSq (smain i).shiftVector≤P.Ds^2)
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (sfinal i).shiftVector≤P.Ds^2)
  (L : PrimitiveLaws D) (hL : L.pointDraw=stdGaussian (Point D))
  (Jf : FreshChildBatchCoupling.Lower L
    (PrivateFinalCoupling.data (PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos (CubicSchedulePayments.radius_guard P hK hc hcsmall hC (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos) snodes r P.Ds smain sfinal P.NP hr P.Ds_pos hfinalMass
      (PrivateChronologicalCoupling.terminalCursor (PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos (CubicSchedulePayments.radius_guard P hK hc hcsmall hC (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos) snodes r P.Ds smain sfinal P.NP).old))
  (J : ∀ (k : ℕ) (hk : k<P.NP),FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data (PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos (CubicSchedulePayments.radius_guard P hK hc hcsmall hC (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos) snodes r P.Ds smain sfinal P.NP hr P.Ds_pos hmass
      (PrivateChronologicalCoupling.stage (PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos (CubicSchedulePayments.radius_guard P hK hc hcsmall hC (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos) snodes r P.Ds smain sfinal P.NP k hk.le).1
      (PrivateChronologicalCoupling.stage_positive (PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos (CubicSchedulePayments.radius_guard P hK hc hcsmall hC (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos) snodes r P.Ds smain sfinal P.NP k hk)))
  (G : Point D → Point D) (hG : Measurable G)
  (privateShift : GaussianSlot (SamplingExecutable.build (PrescribedSourceGeometry.samplingGeometry P.m P.R P.h0 P.R_pos (CubicSchedulePayments.radius_guard P hK hc hcsmall hC (PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy)) P.h0_pos) snodes r P.Ds smain sfinal P.NP).program → ℝ)
local notation "κ" => PrivateSourceScalarAbsorption.twiceNonneg ell hell
local notation "sigmaM" => RecursiveMeanPublicTable.mainWidth sn r (S).R P.Ds (r^2)
local notation "sigmaF" => SourceExecutableTables.samplingFinalWidth S r
local notation "sampling" => SamplingExecutable.build S snodes r P.Ds smain sfinal P.NP
local notation "hcurv" => source_curvature P hK hc hcsmall hC hy hell hr hr1 hellδ
local notation "anchor" => error M nodes anchors seeds main final P.NP mesh snodes r P.Ds σ hr hσ smain sfinal P.NP hF hell hlo hup hcurv P.delta P.t P.w G privateShift
local notation "rho" => incomingLaw M nodes anchors seeds main final P.NP mesh snodes r P.Ds hr P.Ds_pos smain sfinal P.NP hmass hfinalMass L hL hF hell hlo hup Jf J

include hG hr1 hellδ in
/-- Prescribed actual private LOWER errors pay the literal incoming anchor
by 3R delta^(q-1/4) D_F(base), on exactly Standalone.incomingKernel. Both
private batches use their true widths and precision q-1/4, with all final
children retained; no current private accuracy is supplied. -/
theorem source_anchor_bound (base : Point D) (q : ℝ) (hq : q≤(P.K:ℝ))
    (hshift : ∀ i,ChildAbsorption.QueryShift (smain i).program (smain i).enumeration (smain i).coefficient
      ((S).radius r (snodes i)) (smain i).shiftVector)
    (hshiftF : ∀ i,ChildAbsorption.QueryShift (sfinal i).program (sfinal i).enumeration (sfinal i).coefficient
      ((S).radius r (snodes i)) (sfinal i).shiftVector)
    (hstable : ∀ i,FixedTapeStability.ChildStable (smain i).program (smain i).coefficient G κ)
    (hstableF : ∀ i,FixedTapeStability.ChildStable (sfinal i).program (sfinal i).coefficient G κ)
    (hmem : ∀ k (hk : k<P.NP) i y,MemLp (FreshChildRunShift.lowerError (smain i).program G (smain i).coefficient y
      (Gibbs.primitiveMean F y ((S).radius r (snodes i))) sigmaM) 2 ((J k hk).joint i y))
    (hbound : ∀ k (hk : k<P.NP) i y,(∫ z,‖FreshChildRunShift.lowerError (smain i).program G (smain i).coefficient y
      (Gibbs.primitiveMean F y ((S).radius r (snodes i))) sigmaM z‖^2 ∂(J k hk).joint i y)≤
        (4*sigmaM*P.delta^(q-1/4)*Gibbs.primitiveScale F y)^2)
    (hmemF : ∀ i y,MemLp (FreshChildRunShift.lowerError (sfinal i).program G (sfinal i).coefficient y
      (Gibbs.primitiveMean F y ((S).radius r (snodes i))) sigmaF) 2 (Jf.joint i y))
    (hboundF : ∀ i y,(∫ z,‖FreshChildRunShift.lowerError (sfinal i).program G (sfinal i).coefficient y
      (Gibbs.primitiveMean F y ((S).radius r (snodes i))) sigmaF z‖^2 ∂Jf.joint i y)≤
        (4*sigmaF*P.delta^(q-1/4)*Gibbs.primitiveScale F y)^2) :
    ∃ hi : MemLp (anchor base) 2 (rho base),
      (∫ z,‖anchor base z‖^2 ∂rho base)≤(3*P.R*P.delta^(q-1/4)*Gibbs.primitiveScale F base)^2 ∧
      ‖hi.toLp _‖≤3*P.R*P.delta^(q-1/4)*Gibbs.primitiveScale F base := by
  have hm : 1≤P.m := by have := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega
  obtain ⟨hi,hI⟩ := anchor_square_bound M nodes anchors seeds main final P.NP mesh snodes r P.Ds σ hr P.Ds_pos hσ
    smain sfinal P.NP hmass hfinalMass L hL hF hell hlo hup hcurv Jf J P.delta P.t P.w G hG privateShift hm base κ κ
    (fun _ _ => 4*sigmaM*P.delta^(q-1/4)) (fun _ => 4*sigmaF*P.delta^(q-1/4))
    hshift hshiftF hstable hstableF hmem hbound hmemF hboundF
  have hpay := MeanIncomingSourcePayments.recursive_anchor_payment_sq P hK hc hcsmall hC hy snodes hF hell hlo hup r hr hr1 hellδ base q hq
  have hI' : (∫ z,‖anchor base z‖^2 ∂rho base)≤(3*P.R*P.delta^(q-1/4)*Gibbs.primitiveScale F base)^2 := hI.trans hpay
  refine ⟨hi,hI',?_⟩
  exact FreshChildBatchErrorTransfer.norm_toLp_le_of_square_integral _ _ hi _
    (by positivity [P.R_pos,P.delta_pos,Gibbs.primitiveScale_nonneg F base]) hI'
end Prescribed

end AcceleratedLogConcave.Oracle.MeanStandaloneAnchorAccuracy
