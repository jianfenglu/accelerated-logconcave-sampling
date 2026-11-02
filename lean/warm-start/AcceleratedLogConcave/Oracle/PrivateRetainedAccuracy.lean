import AcceleratedLogConcave.Oracle.PrivateCompletedRms
import AcceleratedLogConcave.Oracle.PrivateSamplingRmsMeasurability

/-! Exact quantitative error transport onto the constructed retained private
coupling. The complete original seed and parent momentum stay in its source. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.PrivateRetainedAccuracy
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceExecutableTables CovarianceSetup
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateChronologicalCoupling PrivateCompletedRms
attribute [local instance] PrivateCompletedRms.canonicalTapeSpace PrivateCompletedRms.canonicalPrefixSpace

variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
local notation "Ω" => Sample (d := d) S e r Ds main final N

variable (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, shiftSq (main i).shiftVector ≤ Ds^2)
  (hfinalMass : ∀ i, shiftSq (final i).shiftVector ≤ Ds^2)
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v, 0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  {G : Point d → Point d} (hG : Measurable G)
  (Jf : FreshChildBatchCoupling.Lower L (PrivateFinalCoupling.data S e r Ds main final N hr hDs hfinalMass
    (terminalCursor S e r Ds main final N).old))
  (J : ∀ (k : ℕ) (hk : k<N), FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk)))

local notation "actualLaw" => law S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J
local notation "prior" => PrivateChronologicalCoupling.kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J

local notation "A" => samplingMatrix S e r
local notation "rho" => samplingNoise S r Ds
local notation "Cmat" => residualRoot A rho (r^2)
local notation "sigma" => RecursiveMeanPublicTable.mainWidth n r (S.R) Ds (r^2)

local notation "flowData" => PrivateSamplingOriginalBounds.data S r hF hell hlo hup hr


local notation "κactual" => PrivateCompletedReference.retainedKernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J
local notation "Seed" => (Point d × Tape d (Host S e r Ds main final N)) × Point d

/-- Literal standalone private output minus the reference returned by its
constructed retained coupling, on the full original designated input and tape. -/
def error (x : Point d) (z : Seed) : Point d :=
  (show Point d from (run (Host S e r Ds main final N) G
    ⟨(SamplingExecutable.build S e r Ds main final N).coefficient,x,z.1.1⟩ Env.empty z.1.2).value) - z.2

include hG in
theorem error_measurable (x : Point d) : Measurable (error (G := G) S e r Ds main final N x) := by
  have hgrad := hG
  have hprogram := CanonicalTapeMeasurability.program_point_of_measurable (Host S e r Ds main final N) G hgrad
    (fun _ => (SamplingExecutable.build S e r Ds main final N).coefficient) (fun _ => x)
    (fun z : Seed => z.1.1) (fun z => z.1.2) measurable_const measurable_const measurable_fst.fst measurable_fst.snd
  exact hprogram.sub measurable_snd

include L hG in
theorem completed_error_measurable (x : Point d) :
    Measurable (retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x) := by
  have hgrad := hG
  have hprogram := CanonicalTapeMeasurability.program_point_of_measurable (Host S e r Ds main final N) G hgrad
    (fun _ => (SamplingExecutable.build S e r Ds main final N).coefficient) (fun _ => x)
    (fun z : Ω => z.1.1.1.2) (fun z => z.1.2) measurable_const measurable_const
    measurable_fst.fst.fst.snd measurable_fst.snd
  have hout := (PrivateCompletedReference.output_joint_measurable S e r Ds main final N hr L hF hell hlo hup).comp
    (show Measurable (fun z : Ω => (x,z)) from measurable_const.prodMk measurable_id)
  exact hprogram.sub hout

include hG in
/-- Pushforward of the actual completed error is the error on the actual
retained kernel. The stored center is identified AE by original-source retention. -/
theorem error_law (x : Point d) :
    (κactual x).map (error (G := G) S e r Ds main final N x) =
      (actualLaw x).map (retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x) := by
  rw [PrivateCompletedReference.retainedKernel,Kernel.map_apply _
    (PrivateCompletedReference.retained_readout_measurable S e r Ds main final N hr L hF hell hlo hup),
    Measure.map_map (error_measurable (G := G) (hG := hG) S e r Ds main final N x)
      (PrivateCompletedReference.retained_readout_measurable S e r Ds main final N hr L hF hell hlo hup)]
  apply Measure.map_congr
  filter_upwards [source_support S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x] with z hz
  change error (G := G) S e r Ds main final N x
    ((z.1.1.1.2,z.1.2),PrivateCompletedReference.output S e r Ds main final N hr hF hell hlo hup z.1.1.1.1.1 z) = _
  rw [hz.1]
  rfl

include hG in
/-- L2 membership and the exact second moment survive the actual retained
kernel pushforward, without a new marginal or independence hypothesis. -/
theorem error_moment_transport (x : Point d)
    (hmem : MemLp (retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x) 2 (actualLaw x)) :
    ∃ _hi : MemLp (error (G := G) S e r Ds main final N x) 2 (κactual x),
      (∫ z : Seed, ‖error (G := G) S e r Ds main final N x z‖^2 ∂κactual x) =
        ∫ z : Ω, ‖retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x z‖^2 ∂actualLaw x := by
  exact memLp_integral_of_law _ _ _ _ (error_measurable (G := G) (hG := hG) S e r Ds main final N x)
    (completed_error_measurable (G := G) (hG := hG) S e r Ds main final N hr L hF hell hlo hup x)
    (error_law (G := G) (hG := hG) S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x) hmem

include hG in
/-- Convert the proved completed RMS norm payment into the standalone
retained coupling's literal square-error payment. -/
theorem square_error_of_completed_norm (x : Point d) (B : ℝ)
    (hmem : MemLp (retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x) 2 (actualLaw x))
    (hbound : ‖hmem.toLp (retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x)‖ ≤ B) :
    ∃ _hi : MemLp (error (G := G) S e r Ds main final N x) 2 (κactual x),
      (∫ z : Seed, ‖error (G := G) S e r Ds main final N x z‖^2 ∂κactual x) ≤ B^2 := by
  obtain ⟨hi,he⟩ := error_moment_transport (G := G) (hG := hG) S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x hmem
  refine ⟨hi,he.le.trans ?_⟩
  rw [← FreshChildBatchErrorTransfer.norm_toLp_sq_eq _ _ hmem]
  have hB : 0≤B := (norm_nonneg _).trans hbound
  nlinarith [norm_nonneg (hmem.toLp (retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x))]

include hDs hmass L hG in
/-- The actual main fixed-tape difference is measurable on the full completed
sample; no numerical regularity premise is supplied. -/
theorem main_difference_measurable (x : Point d) (k : ℕ) (hk : k<N) (i : Fin n) :
    Measurable (mainDifference (G := G) S e r Ds main final N hr hF hell hlo hup x k i) := by
  have hY : Measurable (fun z : Ω => stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i z.1) :=
    (stageBenchmark_measurable S e r Ds main final N hr hDs hmass L hF hell hlo hup x k hk.le i).comp measurable_fst
  have hm := PrivateSamplingRmsMeasurability.main_difference_measurable S e r Ds main final N hr hDs hmass L G hG
    (tape S e r Ds main final N) (tape_measurable S e r Ds main final N) x
    (PrivateSamplingRetainedRms.reply S e r Ds main final N hF hell hlo hup x hr) k hk i _ hY
  convert hm using 1
  rfl

include hDs hmass L hG in
/-- The actual final fixed-tape difference uses the reached interpreter state
and the same literal final seed in both callbacks, measurably. -/
theorem final_difference_measurable (x P : Point d) (i : Fin n) :
    Measurable (finalDifference (G := G) S e r Ds main final N hr hF hell hlo hup x P i) := by
  have hY : Measurable (fun z : Ω => stageBenchmark S e r Ds main final N hr hF hell hlo hup x N i z.1) :=
    (stageBenchmark_measurable S e r Ds main final N hr hDs hmass L hF hell hlo hup x N le_rfl i).comp measurable_fst
  have hm := PrivateSamplingRmsMeasurability.final_difference_measurable S e r Ds main final N L G hG
    (tape S e r Ds main final N) (tape_measurable S e r Ds main final N) x P i _ hY
  convert hm using 1
  rfl

include hG in
/-- Actual retained-kernel quantitative accuracy from only LOWER child errors
and the original source analytic budgets. This is a statement about the
constructed joint kernel, with its entire original source seed. -/
theorem square_error_bound (hm : 1≤m) (hphysical : r^2*ell≤1/2)
    (x : Point d) (κ κf : ℝ≥0) (amplitude : ℕ → Fin n → ℝ) (amplitudeF : Fin n → ℝ)
    (hshift : ∀ i, ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (S.radius r (e i)) (main i).shiftVector)
    (hshiftF : ∀ i, ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (S.radius r (e i)) (final i).shiftVector)
    (hstable : ∀ i, FixedTapeStability.ChildStable (main i).program (main i).coefficient G κ)
    (hstableF : ∀ i, FixedTapeStability.ChildStable (final i).program (final i).coefficient G κf)
    (hmem : ∀ k (hk : k<N) i y, MemLp (FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
      (Gibbs.primitiveMean F y (S.radius r (e i))) sigma) 2 ((J k hk).joint i y))
    (hbound : ∀ k (hk : k<N) i y, (∫ z : (Point d × Tape d (main i).program) × Point d,
      ‖FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
        (Gibbs.primitiveMean F y (S.radius r (e i))) sigma z‖^2 ∂(J k hk).joint i y) ≤
      (amplitude k i*Gibbs.primitiveScale F y)^2)
    (hmemF : ∀ i y, MemLp (FreshChildRunShift.lowerError (final i).program G (final i).coefficient y
      (Gibbs.primitiveMean F y (S.radius r (e i))) (samplingFinalWidth S r)) 2 (Jf.joint i y))
    (hboundF : ∀ i y, (∫ z : (Point d × Tape d (final i).program) × Point d,
      ‖FreshChildRunShift.lowerError (final i).program G (final i).coefficient y
        (Gibbs.primitiveMean F y (S.radius r (e i))) (samplingFinalWidth S r) z‖^2 ∂Jf.joint i y) ≤
      (amplitudeF i*Gibbs.primitiveScale F y)^2) :
    ∃ _hi : MemLp (error (G := G) S e r Ds main final N x) 2 (κactual x),
      (∫ z : Seed, ‖error (G := G) S e r Ds main final N x z‖^2 ∂κactual x) ≤
        ((r*((κf:ℝ)*mainBudget S e r N hr hF hell hlo hup x κ amplitude) +
          ∑ i, |samplingFinalWeight S e r i| * childPayment S e r hr hF hell hlo hup x i (amplitudeF i)) +
            quadratureBudget S r hr hF hell hlo hup)^2 := by
  let P : Point d := 0
  have hmeas (k : ℕ) (hk : k<N) (i : Fin n) :=
    (main_difference_measurable (G := G) (hG := hG) S e r Ds main final N hr hDs hmass L hF hell hlo hup x k hk i).aestronglyMeasurable (μ := actualLaw x)
  have hmeasF (i : Fin n) :=
    (final_difference_measurable (G := G) (hG := hG) S e r Ds main final N hr hDs hmass L hF hell hlo hup x P i).aestronglyMeasurable (μ := actualLaw x)
  obtain ⟨hn,hnB⟩ := PrivateCompletedRms.retained_error_bound (G := G) (hG := hG) S e r Ds main final N hr hDs hmass hfinalMass L hL
    hF hell hlo hup Jf J hm hphysical x P κ κf amplitude amplitudeF hshift hshiftF hstable hstableF hmeas hmeasF
    hmem hbound hmemF hboundF
  exact square_error_of_completed_norm (G := G) (hG := hG) S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x _ hn hnB

end AcceleratedLogConcave.Oracle.PrivateRetainedAccuracy
