import AcceleratedLogConcave.Oracle.PrescribedRetainedCoreEquation
import AcceleratedLogConcave.Oracle.PrescribedRetainedStepAccuracy
import AcceleratedLogConcave.Oracle.MeanStandaloneLowerErrorBound
import AcceleratedLogConcave.Oracle.MeanCompletedSourcePayments
import AcceleratedLogConcave.Oracle.PrescribedFourChildGuards

/-! Source quantitative closure for the exact active retained core, using
only the four actual strictly lower accuracy hypotheses. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.PrescribedRetainedNonterminalAccuracy
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall
open RecursiveRetainedAccuracy PrescribedRetainedChildPaths
open PrescribedRetainedQuantitativeInduction PrescribedRetainedCoreEquation
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
local instance canonicalTapeSpace {D c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape D p) := CanonicalTapeMeasurability.tapeSpace D p
set_option maxHeartbeats 200000
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
  {d : ℕ} (ell r0 σ0 : ℝ) (hell : 0≤ell) (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hrootRadius : ell*r0^2≤P.delta)
  {V : Point d → ℝ} (scale : ℝ) (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v≤ell*‖v‖^2)

local notation "hR" => PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy
local notation "C" => source P hR
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "hF" => (show ContDiff ℝ 2 (scaledPotential V scale) from by unfold scaledPotential; fun_prop)
local notation "hG" => ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp (hV.continuous_fderiv (by norm_num))).measurable
local notation "hm2" => P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch)
local notation "hm" => (show 0<P.m from by have := hm2; omega)
local notation "hs" => CubicSchedulePayments.actual_scalar_payments P hK hc hcsmall hC baseHy
local notation "hy0" => (CubicSchedulePayments.prerequisites P hK hc hcsmall hC baseHy).1
local notation "hpsieq" => (show (C).M.psi=P.delta^(4*P.t) from P.psi_eq_R_pow.symm)
variable {p : State} {depth cost : ℕ}
  (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
    (PrescribedRecursiveStability.root P r0 σ0) p depth cost)
  (hq : 1/2<p.precision)
local notation "theta" => PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp

def mainLower :=
  RecursiveRetainedCoupling.meanMainLower (C).M hm hF hell hlo hup P.t (P.t_pos hc)
    (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.w P.NP
    (step_quarter P hc hcsmall) scale (P.K:ℝ) P.Ds_pos P.delta_pos le_rfl (ScalarSchedulePayment.I P hR) P.Hs (by rfl)
    (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC)
    hs.2.2.2.1 theta p.precision
    (PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp)
    (mainLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq)

def finalLower :=
  RecursiveRetainedCoupling.finalLower (C).M hm hF hell hlo hup P.t (P.t_pos hc)
    (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.w P.NP
    (step_quarter P hc hcsmall) scale (P.K:ℝ) P.Ds_pos le_rfl (ScalarSchedulePayment.I P hR) P.Hs (by rfl)
    (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC)
    hs.2.2.2.1 theta p.precision
    (PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp)
    (finalLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq)

def privateLower :=
  RecursiveRetainedCoupling.privateMainLower (C).M hm hF hell hlo hup P.t (P.t_pos hc)
    (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.w P.NP
    (step_quarter P hc hcsmall) scale (P.K:ℝ) P.Ds_pos le_rfl (ScalarSchedulePayment.I P hR) P.Hs (by rfl)
    (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC)
    hs.2.2.2.1 theta p.precision
    (PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp)
    (privateMainLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq)

def privateFinalLower :=
  RecursiveRetainedCoupling.privateFinalLower (C).M hm hF hell hlo hup P.t (P.t_pos hc)
    (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.w P.NP
    (step_quarter P hc hcsmall) scale (P.K:ℝ) P.Ds_pos le_rfl (ScalarSchedulePayment.I P hR) P.Hs (by rfl)
    (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC)
    hs.2.2.2.1 theta p.precision
    (PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp)
    (privateFinalLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq)

local notation "main" => MeanMainBatchCoupling.recursiveMain (C).M (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.width p.precision
local notation "final" => MeanMainBatchCoupling.recursiveFinal (C).M (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.width p.precision
local notation "smain" => PrivateRecursiveBatchBudget.main (C).M (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.precision
local notation "sfinal" => PrivateRecursiveBatchBudget.final (C).M (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.precision
local notation "Jm" => mainLower P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq
local notation "Jf" => finalLower P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq
local notation "Jp" => privateLower P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq
local notation "Jpf" => privateFinalLower P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq
local notation "aRow" => SourceMeanExecutable.rowBound (m := P.m) p.radius p.width P.delta P.t P.w
local notation "sigmaM" => RecursiveMeanPublicTable.mainWidth (ScalarSchedulePayment.n P hR) p.radius (C).M.R P.Ds aRow
local notation "sigmaPM" => RecursiveMeanPublicTable.mainWidth (ScalarSchedulePayment.ns P hR) p.radius (C).S.R P.Ds (p.radius^2)
local notation "sigmaF" => RecursiveMeanPublicTable.finalWidth (C).M.R p.width
local notation "sigmaPF" => SourceExecutableTables.samplingFinalWidth (C).S p.radius
local notation "kap" => PrivateSourceScalarAbsorption.twiceNonneg ell hell
local notation "amain" => (fun (_ : ℕ) (_ : Fin (ScalarSchedulePayment.n P hR)) => 4*sigmaM*P.delta^(p.precision-1/4))
local notation "afinal" => (fun (_ : Fin P.m) => 4*sigmaF*P.delta^(p.precision-P.t))
local notation "aprivate" => (fun (_ : ℕ) (_ : Fin (ScalarSchedulePayment.ns P hR)) => 4*sigmaPM*P.delta^(p.precision-1/4))
local notation "aprivateFinal" => (fun (_ : Fin (ScalarSchedulePayment.ns P hR)) => 4*sigmaPF*P.delta^(p.precision-1/4))

local notation "massM" => MeanRecursiveChronologicalCoupling.mainMass (C).M (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.width p.precision (P.K:ℝ) P.Ds_pos le_rfl (ScalarSchedulePayment.I P hR) P.Hs (by rfl) (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC) hs.2.2.2.1 (theta).radius_pos (PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp)
local notation "massP" => PrivateRecursiveChronologicalCoupling.mainMass (C).M (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.precision (P.K:ℝ) P.Ds_pos le_rfl (ScalarSchedulePayment.I P hR) P.Hs (by rfl) (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC) hs.2.2.2.1 (theta).radius_pos (PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp)
local notation "massPF" => PrivateRecursiveChronologicalCoupling.finalMass (C).M (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.precision (P.K:ℝ) P.Ds_pos le_rfl (ScalarSchedulePayment.I P hR) P.Hs (by rfl) (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC) hs.2.2.2.1 (theta).radius_pos (PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp)
local notation "massF" => (fun i => (MeanMainBatchCoupling.recursive_final_shift (C).M (C).nodes (anchors P hR) (seeds P hR) (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.width p.precision (P.K:ℝ) P.Ds_pos le_rfl (ScalarSchedulePayment.I P hR) P.Hs (by rfl) (CubicSchedulePayments.shift_precision P hK) (CubicSchedulePayments.support_height P hC) hs.2.2.2.1 (theta).radius_pos (PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp) i).2)

variable (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
  (hr1 : r0≤1) (hellδ : ell≤P.delta) (hrootRatio : ell*(r0/σ0)≤P.delta)

include hp hq hyMean hr1 hellδ hrootRatio in
private theorem nonterminal_of_fibers
    (hmain : ∀ k (hk : k<P.NP) i,MeanStandaloneLowerErrorBound.Fiber (F := scaledPotential V scale)
      (gradient V) (main i) ((Jm k hk).joint i) ((C).M.radius p.radius ((C).nodes i)) sigmaM (amain k i))
    (hfinal : ∀ i,MeanStandaloneLowerErrorBound.Fiber (F := scaledPotential V scale)
      (gradient V) (final i) ((Jf).joint i) (p.radius*(C).M.R) sigmaF (afinal i))
    (hprivate : ∀ k (hk : k<P.NP) i,MeanStandaloneLowerErrorBound.Fiber (F := scaledPotential V scale)
      (gradient V) (smain i) ((Jp k hk).joint i) ((C).S.radius p.radius ((C).snodes i)) sigmaPM (aprivate k i))
    (hprivateFinal : ∀ i,MeanStandaloneLowerErrorBound.Fiber (F := scaledPotential V scale)
      (gradient V) (sfinal i) ((Jpf).joint i) ((C).S.radius p.radius ((C).snodes i)) sigmaPF (aprivateFinal i)) :
    AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp := by
  dsimp only [AccurateCall]
  rw [active_eq_step P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq]
  unfold activeStep RecursiveRetainedCoupling.step
  apply (accurateWith_castLaw (C).M hm hF hell hlo hup P.t (P.t_pos hc) 4 _ _ (gradient V) P.delta).2
  intro base
  have hpos := hp.positive hm P.Ds_pos P.delta_pos hr0 hσ0
  have hrp := PrescribedTerminalAccuracy.radius_le_root hp hm P.Ds_pos P.delta_pos hr0 hσ0
  change p.radius≤r0 at hrp
  have hqueryM := PrescribedFourChildGuards.meanMain P hK hc hcsmall hC hy scale hV ⟨ell,hell⟩ hlo hup r0 σ0 hr0 hσ0 hrootRadius hrootRatio hp hq
  have hqueryF := PrescribedFourChildGuards.activeFinal P hK hc hcsmall hC hy scale hV ⟨ell,hell⟩ hlo hup r0 σ0 hr0 hσ0 hrootRadius hrootRatio hp hq
  have hqueryP := PrescribedFourChildGuards.privateMain P hK hc hcsmall hC hy scale hV ⟨ell,hell⟩ hlo hup r0 σ0 hr0 hσ0 hrootRadius hrootRatio hp hq
  have hqueryPF := PrescribedFourChildGuards.privateFinal P hK hc hcsmall hC hy scale hV ⟨ell,hell⟩ hlo hup r0 σ0 hr0 hσ0 hrootRadius hrootRatio hp hq
  have hpay := MeanIncomingSourcePayments.anchor_payment_le P hK hc hcsmall hC hy (C).snodes hF hell hlo hup
    p.radius hpos.1 (hrp.trans hr1) hellδ base (p.precision-1/4)
    (by have := PrescribedRetainedAccuracy.precision_le P hK hc hcsmall hC hy r0 σ0 hp; linarith)
  have hmesh := PrescribedMeanNumericalData.reachable_mesh P hF hell hlo hup base hK hc hcsmall hC hy hr0 hσ0 hrootRadius hp
  have hhalf := PrescribedMeanNumericalData.reachable_contraction P hF hell hlo hup base hK hc hcsmall hC hy hr0 hσ0 hrootRadius hrootRatio hp
  have ha := MeanRecursiveChronologicalCoupling.row_pos (m := P.m) P.delta P.t P.w p.radius p.width hpos.1 hpos.2 P.delta_pos
  have hA := MeanRecursiveChronologicalCoupling.actual_rows (C).M (C).nodes (C).mesh (C).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc)
    p.radius p.width hpos.1 hpos.2 P.delta_pos hm2 (P.delta_le_one hy0) hpsieq hs.2.2.2.2.2.1.2.2.2 rfl
  obtain ⟨hout,hbound⟩ := MeanStandaloneLowerErrorBound.output_error_bound
    (C).M (C).nodes (anchors P hR) (seeds P hR) main final P.NP (C).mesh (C).snodes
    p.radius P.Ds p.width hpos.1 P.Ds_pos hpos.2 smain sfinal P.NP massP massPF
    (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl hF hell hlo hup (theta).small
    Jpf Jp massM massF P.delta P.t P.w (gradient V) hG Jm Jf base hm (P.t_pos hc) p.precision
    P.h0 hmesh hhalf ha hA le_rfl kap kap (3*P.R*P.delta^(p.precision-1/4)*Gibbs.primitiveScale (scaledPotential V scale) base)
    amain afinal (fun i => (hqueryM i).2.2) (fun i => (hqueryF i).2.2)
    (fun i => (hqueryM i).1) (fun i => (hqueryF i).1) hmain hfinal
    aprivate aprivateFinal hpay (fun i => (hqueryP i).1) (fun i => (hqueryPF i).1)
    (fun i => (hqueryP i).2.2) (fun i => (hqueryPF i).2.2) hprivate hprivateFinal
  have hbudget := MeanCompletedSourcePayments.source_output_budget_le P hK hc hcsmall hC hyMean
    hF hell hlo hup base hr0 hr1 hσ0 hellδ hrootRatio hp
  have hnorm := hbound.trans hbudget
  refine ⟨hout,?_⟩
  have hn : 0≤4*p.width*P.delta^p.precision*Gibbs.primitiveScale (scaledPotential V scale) base := by
    positivity [hpos.2,P.delta_pos,Gibbs.primitiveScale_nonneg (scaledPotential V scale) base]
  have hsq := FreshChildBatchErrorTransfer.norm_toLp_sq_eq _ _ hout
  have hsqbound := (sq_le_sq₀ (norm_nonneg (hout.toLp _)) hn).2 hnorm
  have hintegral := hsq.symm.le.trans hsqbound
  have hright : (4*p.width*P.delta^p.precision*Gibbs.primitiveScale (scaledPotential V scale) base)^2 =
      (4*(p.width*P.delta^p.precision*Gibbs.primitiveScale (scaledPotential V scale) base))^2 := by ring
  have hfinalBound := hintegral.trans_eq hright
  simpa only [RecursiveRetainedAccuracy.error,SourceMeanExecutable.build,
    MeanMainBatchCoupling.recursivePrivate,MeanStandaloneAccuracyTransport.sourceError,
    PrescribedRetainedAccuracy.parameters,MeanCompletedReference.parentTheta,
    Conditional.SourceParameters.radius,Conditional.SourceParameters.width,
    mainLower,finalLower,privateLower,privateFinalLower] using hfinalBound

include hyMean hr1 hellδ hrootRatio in
/-- Actual nonterminal source accuracy, obtained solely from the four strictly
lower reachable calls of the same retained core. -/
theorem nonterminal_case
    (ihmain : ∀ i : Fin (ScalarSchedulePayment.n P hR),AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup
      (main_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i))
    (ihfinal : ∀ i : Fin P.m,AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup
      (final_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i))
    (ihprivate : ∀ i : Fin (ScalarSchedulePayment.ns P hR),AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup
      (privateMain_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i))
    (ihprivateFinal : ∀ i : Fin (ScalarSchedulePayment.ns P hR),AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup
      (privateFinal_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i))
    : AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp := by
  apply nonterminal_of_fibers P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq hyMean hr1 hellδ hrootRatio
  · intro k hk i
    exact PrescribedRetainedStepAccuracy.main_fiber P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq i (ihmain i)
  · intro i
    exact PrescribedRetainedStepAccuracy.final_fiber P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq i (ihfinal i)
  · intro k hk i
    exact PrescribedRetainedStepAccuracy.privateMain_fiber P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq i (ihprivate i)
  · intro i
    exact PrescribedRetainedStepAccuracy.privateFinal_fiber P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq i (ihprivateFinal i)

end AcceleratedLogConcave.Oracle.PrescribedRetainedNonterminalAccuracy
