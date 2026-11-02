import AcceleratedLogConcave.Oracle.PrivateCompletedReference
import AcceleratedLogConcave.Oracle.SamplingCenterRegularity
import AcceleratedLogConcave.Oracle.PrivateCompletedSupport
import AcceleratedLogConcave.Oracle.PrivateFinalEvaluatorReadout
import AcceleratedLogConcave.Oracle.PrivateCompletedMainReadout
import AcceleratedLogConcave.Oracle.PrivateChronologicalLaws
import AcceleratedLogConcave.Oracle.PrivateCompletedLaws
import AcceleratedLogConcave.Oracle.PrivateSamplingMeshPayments
import AcceleratedLogConcave.Oracle.PrivateBenchmarkMoments
import AcceleratedLogConcave.Oracle.FreshChildBatchErrorTransfer

/-! Quantitative RMS estimates at the actual completed private sample.
Original-data norm budgets and standalone lower error estimates are used.
The actual measurable oracle G is independent of the scaled analysis potential F. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.PrivateCompletedRms
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceExecutableTables CovarianceSetup
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateChronologicalCoupling

attribute [local instance] canonicalTapeSpace canonicalPrefixSpace

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

def initializerBudget (x : Point d) : ℝ :=
  r^2*(samplingEnd S.τ)^2*PrivateSamplingOriginalBounds.replyBudget flowData x

def residualBudget : ℝ := r^2*(samplingEnd S.τ)*
  AffineResidual.cellBudget S.mesh m (SamplingGaussianJetLp.cellDerivativeBudget flowData S.mesh m)

def quadratureBudget : ℝ := (r/samplingEnd S.τ)*
  AffineResidual.cellBudget S.mesh m (SamplingGaussianJetLp.cellDerivativeBudget flowData S.mesh m)

local notation "ref" => PrivateSamplingRetainedRms.reference S e r Ds main final N hF hell hlo hup
local notation "rep" => PrivateSamplingRetainedRms.reply S e r Ds main final N hF hell hlo hup

def initializerError (x : Point d) (i : Fin n) (z : Ω) : Point d :=
  PrivateSamplingExecutionSchedule.initial S e r Ds main final N x (tape S e r Ds main final N z) i -
    (ref x hr i (tape S e r Ds main final N z) +
      PrivateSamplingRetainedRms.initialNoise S e r Ds main final N i (tape S e r Ds main final N z))

def rowError (x : Point d) (i : Fin n) (z : Ω) : Point d :=
  SharedLayerRms.residual
    (fun j z => x+(r*S.mesh.location m (e j)) •
      (show Point d from (tape S e r Ds main final N z).2.1)) A
    (fun j z => rep x hr j (tape S e r Ds main final N z))
    (fun j z => ref x hr j (tape S e r Ds main final N z)) i z

/-- The final source-row defect against the exact Gaussian-start endpoint.
Only this error, not the absolute endpoint position, needs an L2 estimate. -/
def quadratureError (x : Point d) (z : Ω) : Point d :=
  let seed : Point d := (tape S e r Ds main final N z).2.1
  (samplingEnd S.τ)⁻¹ • seed +
    (∑ i, samplingFinalWeight S e r i • rep x hr i (tape S e r Ds main final N z)) -
    (samplingEnd S.τ)⁻¹ • (SamplingFlowLp.sourcePath hF hell hlo hup x hr
      S.samplingEnd_pos.le S.samplingEnd_lt_one (samplingEnd S.τ) seed)

/-- Original-data initializer bound on the actual completed coupling. -/
theorem initializer_bound (hphysical : r^2*ell≤1/2) (x : Point d) :
    ∃ hi : ∀ i, MemLp (initializerError S e r Ds main final N hr hF hell hlo hup x i) 2 (actualLaw x),
      Collocation.rawNodeErrorNorm (actualLaw x) (initializerError S e r Ds main final N hr hF hell hlo hup x) hi ≤
        initializerBudget S r hr hF hell hlo hup x := by
  exact PrivateSamplingOriginalBounds.initial_node_norm_bound S e r Ds main final N
    hF hell hlo hup hr x (actualLaw x) (tape S e r Ds main final N) hphysical L hL
    (tape_preserving S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x)

/-- The actual collocation residual's quantitative budget is supplied by
original smooth convex data and the exact unchanged source projection. -/
theorem row_bound (hphysical : r^2*ell≤1/2) (hm : 1≤m) (x : Point d) :
    ∃ hi : ∀ i, MemLp (rowError S e r Ds main final N hr hF hell hlo hup x i) 2 (actualLaw x),
      ∀ i, ‖(hi i).toLp (rowError S e r Ds main final N hr hF hell hlo hup x i)‖ ≤
        residualBudget S r hr hF hell hlo hup := by
  exact PrivateSamplingOriginalBounds.residual_bounds S e r Ds main final N
    hF hell hlo hup hr x (actualLaw x) (tape S e r Ds main final N) hphysical hm L hL
    (tape_preserving S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x)

/-- The final endpoint quadrature defect on the actual completed kernel,
including the physical output factor r/rhoEnd. -/
theorem quadrature_bound (hphysical : r^2*ell≤1/2) (hm : 1≤m) (x : Point d) :
    ∃ hi : MemLp (quadratureError S e r Ds main final N hr hF hell hlo hup x) 2 (actualLaw x),
      ‖hi.toLp (quadratureError S e r Ds main final N hr hF hell hlo hup x)‖ ≤
        quadratureBudget S r hr hF hell hlo hup := by
  exact PrivateSamplingOriginalBounds.final_norm_bound S e r Ds main final N
    hF hell hlo hup hr x (actualLaw x) (tape S e r Ds main final N) hphysical hm L hL
    (tape_preserving S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x)

section MainPast
local notation "X" => History d N n × Tape d (Host S e r Ds main final N)

abbrev PastSample (k : ℕ) :=
  ((((Point d × Point d) × Point d) × Tape d (Host S e r Ds main final N)) ×
    (Fin k → Fin n → Point d))

/-- Restore just the fields read by a completed main child error. Future
reference slots and the no-longer-needed current comparison are set to zero. -/
def restorePast (k : ℕ) (_hk : k≤N) (a : PastSample (d := d) S e r Ds main final N k) : X :=
  ((a.1.1,((fun j => if hj : (j:ℕ)<k then a.2 ⟨j,hj⟩ else 0),fun _ => 0)),a.1.2)

theorem restorePast_measurable (k : ℕ) (hk : k≤N) :
    Measurable (restorePast (d := d) S e r Ds main final N k hk) := by
  have href : Measurable (fun a : PastSample (d := d) S e r Ds main final N k =>
      fun j : Fin N => if hj : (j:ℕ)<k then a.2 ⟨j,hj⟩ else (0 : Fin n → Point d)) := by
    apply Measurable.of_eval
    intro j
    by_cases hj : (j:ℕ)<k
    · simp only [dite_eq_left hj]
      exact (measurable_pi_apply (⟨j,hj⟩ : Fin k)).comp measurable_snd
    · simp only [dite_eq_right hj]
      exact measurable_const
  exact (measurable_fst.fst.prodMk (href.prodMk measurable_const)).prodMk measurable_fst.snd

theorem restorePast_reference (k : ℕ) (hk : k≤N) (j : ℕ) (hj : j<k) (i : Fin n) (z : X) :
    PrivateChronologicalExecution.returnedReference S e r Ds main final N j i
      (restorePast S e r Ds main final N k hk
        (PrivateChronologicalExecution.past S e r Ds main final N k hk z)) =
    PrivateChronologicalExecution.returnedReference S e r Ds main final N j i z := by
  simp only [PrivateChronologicalExecution.returnedReference,
    dite_eq_left (lt_of_lt_of_le hj hk),restorePast,PrivateChronologicalExecution.past,dite_eq_left hj]

theorem restorePast_comparison (k : ℕ) (hk : k≤N) (j : ℕ) (hj : j≤k) (z : X) :
    PrivateChronologicalExecution.comparisonNoise S e r Ds main final N j (hj.trans hk)
      (restorePast S e r Ds main final N k hk
        (PrivateChronologicalExecution.past S e r Ds main final N k hk z)) =
    PrivateChronologicalExecution.comparisonNoise S e r Ds main final N j (hj.trans hk) z := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [PrivateChronologicalExecution.comparisonNoise,restorePast,
      PrivateChronologicalExecution.past,dite_eq_left (show j<k by omega)]

def stageBenchmark (x : Point d) (k : ℕ) (i : Fin n) (z : X) : Point d :=
  SharedLayerRms.benchmark (fun j z => ref x hr j z.2) A Cmat sigma
    (SourceMeanRetainedRms.finiteReference N
      (PrivateChronologicalExecution.returnedReference S e r Ds main final N))
    (fun k i z => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i z.2)
    (fun i z => PrivateSamplingRetainedRms.initialNoise S e r Ds main final N i z.2) k i z

include hDs in
theorem stageBenchmark_eq (x : Point d) (k : ℕ) (hk : k≤N) (i : Fin n) (z : X) :
    stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i z =
      ref x hr i z.2 + rho • PrivateChronologicalExecution.comparisonNoise S e r Ds main final N k hk z i := by
  unfold stageBenchmark
  rw [PrivateChronologicalExecution.finiteReference_returnedReference]
  exact PrivateChronologicalExecution.benchmark_eq_comparisonNoise S e r Ds main final N hr hDs k hk
    (fun j z => ref x hr j z.2) z i

include hDs in
theorem restorePast_benchmark (x : Point d) (k : ℕ) (hk : k≤N) (j : ℕ) (hj : j≤k) (i : Fin n) (z : X) :
    stageBenchmark S e r Ds main final N hr hF hell hlo hup x j i
      (restorePast S e r Ds main final N k hk
        (PrivateChronologicalExecution.past S e r Ds main final N k hk z)) =
    stageBenchmark S e r Ds main final N hr hF hell hlo hup x j i z := by
  rw [stageBenchmark_eq S e r Ds main final N hr hDs hF hell hlo hup x j (hj.trans hk),
    stageBenchmark_eq S e r Ds main final N hr hDs hF hell hlo hup x j (hj.trans hk),
    restorePast_comparison S e r Ds main final N k hk j hj]
  rfl

def stageMainError (x : Point d) (k : ℕ) (i : Fin n) (z : X) : Point d :=
  PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G (rep x hr) k i z.2
    (stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i z) -
      rep x hr i z.2 - sigma • PrivateChronologicalExecution.returnedReference S e r Ds main final N k i z

include hDs in
theorem restorePast_mainError (x : Point d) (k : ℕ) (hk : k≤N) (j : ℕ) (hj : j<k) (i : Fin n) (z : X) :
    stageMainError (G := G) S e r Ds main final N hr hF hell hlo hup x j i
      (restorePast S e r Ds main final N k hk
        (PrivateChronologicalExecution.past S e r Ds main final N k hk z)) =
    stageMainError (G := G) S e r Ds main final N hr hF hell hlo hup x j i z := by
  unfold stageMainError
  rw [restorePast_benchmark S e r Ds main final N hr hDs hF hell hlo hup x k hk j hj.le,
    restorePast_reference S e r Ds main final N k hk j hj]
  rfl
/-- The exact actual k-layer augmented source law. -/
def stageLaw (x : Point d) (k : ℕ) (hk : k≤N) : Measure X :=
  iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk ∘ₘ
    initial S e r Ds main final N L x

instance stageLaw_probability (x : Point d) (k : ℕ) (hk : k≤N) :
    IsProbabilityMeasure (stageLaw S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x k hk) := by
  unfold stageLaw
  infer_instance

include hfinalMass Jf in
/-- Actual stored coarse coordinates remain tied to their original source
at every finite stage, before adjoining the next batch. -/
theorem stage_source_support (x : Point d) (k : ℕ) (hk : k≤N) :
    ∀ᵐ z ∂stageLaw S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x k hk,
      z.1.1.1.1=x ∧ z.1.1.1.2=(show Point d from z.2.2.1) := by
  let Q : PastSample (d := d) S e r Ds main final N k → Prop :=
    fun a => a.1.1.1.1=x ∧ a.1.1.1.2=(show Point d from a.1.2.2.1)
  have hQ : MeasurableSet {a | Q a} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))
  have hp : Measurable (fun z : Ω => PrivateChronologicalExecution.past S e r Ds main final N k hk z.1) :=
    (PrivateChronologicalExecution.past_measurable (d := d) S e r Ds main final N k hk).comp measurable_fst
  have ha : ∀ᵐ z ∂actualLaw x, Q (PrivateChronologicalExecution.past S e r Ds main final N k hk z.1) :=
    source_support S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x
  have hb := (ae_map_iff hp.aemeasurable hQ).2 ha
  rw [past_law S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x k hk] at hb
  exact ae_of_ae_map (PrivateChronologicalExecution.past_measurable S e r Ds main final N k hk).aemeasurable hb

include hfinalMass Jf in
/-- The exact current benchmark center is the lower coupling's physical flow
center plus the recorded comparison draw on this same actual sample. -/
theorem stage_benchmark_center (x : Point d) (k : ℕ) (hk : k≤N) :
    ∀ᵐ z ∂stageLaw S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x k hk,
      ∀ i, stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i z =
        jointPhi S e hF hell hlo hup hr i z.1.1.1 + rho • z.1.2.2 i := by
  filter_upwards [stage_source_support S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x k hk,
    PrivateChronologicalExecution.iteration_comparisonNoise_ae S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk x]
    with z hz hn
  intro i
  rw [stageBenchmark_eq S e r Ds main final N hr hDs hF hell hlo hup x k hk,← hn]
  congr 1
  rw [jointPhi_eq_nodePhi S e hF hell hlo hup hr i, hz.1,hz.2]
  rfl

include hDs hmass L in
theorem stageBenchmark_measurable (x : Point d) (k : ℕ) (hk : k≤N) (i : Fin n) :
    Measurable (stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i) := by
  have hphi : Measurable (fun z : X => ref x hr i z.2) :=
    (PrivateConditionalFlowConsumer.nodePhi_measurable S e hF hell hlo hup x hr i).comp measurable_snd.snd.fst
  have hn := ((measurable_pi_apply i).comp
    (PrivateChronologicalExecution.comparisonNoise_measurable S e r Ds main final N hr hDs hmass L k hk)).const_smul rho
  have he : stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i =
      (fun z : X => ref x hr i z.2 + rho • PrivateChronologicalExecution.comparisonNoise S e r Ds main final N k hk z i) := by
    funext z
    exact stageBenchmark_eq S e r Ds main final N hr hDs hF hell hlo hup x k hk i z
  rw [he]
  exact hphi.add hn

include hDs hmass L hG in
theorem stageMainError_measurable (x : Point d) (k : ℕ) (hk : k<N) (i : Fin n) :
    Measurable (stageMainError (G := G) S e r Ds main final N hr hF hell hlo hup x k i) := by
  let seed := PrivateCompletedMainReadout.cursorSeed (d := d) S e r Ds main final N hr hDs hmass
    (stage S e r Ds main final N k hk.le).1 (stage_positive S e r Ds main final N k hk) i
  have hs : Measurable (fun z : X => seed z.2) :=
    (PrivateCompletedMainReadout.cursorSeed_measurable S e r Ds main final N hr hDs hmass L _ _ i).comp measurable_snd
  have hgrad := hG
  have hp := CanonicalTapeMeasurability.program_point_of_measurable (main i).program G hgrad
    (fun _ => (main i).coefficient) (stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i)
    (fun z : X => (seed z.2).1) (fun z => (seed z.2).2) measurable_const
    (stageBenchmark_measurable S e r Ds main final N hr hDs hmass L hF hell hlo hup x k hk.le i) hs.fst hs.snd
  have hu : Measurable (fun z : X => rep x hr i z.2) :=
    (PrivateConditionalFlowConsumer.nodeReply_measurable S e hF hell hlo hup x hr i).comp measurable_snd.snd.fst
  have href := (PrivateChronologicalExecution.returnedReference_measurable (d := d) S e r Ds main final N k i).const_smul sigma
  have he : stageMainError (G := G) S e r Ds main final N hr hF hell hlo hup x k i =
      (fun z : X => (show Point d from (run (main i).program G
        ⟨(main i).coefficient,stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i z,(seed z.2).1⟩
        Env.empty (seed z.2).2).value) - rep x hr i z.2 -
          sigma • PrivateChronologicalExecution.returnedReference S e r Ds main final N k i z) := by
    funext z
    unfold stageMainError
    rw [PrivateCompletedMainReadout.evaluator_eq_run S e r Ds main final N hr hDs hmass k hk]
  rw [he]
  exact (hp.sub hu).sub href

/-- The literal main child error readout on the final completed sample. -/
def mainCompletedError (x : Point d) (k : ℕ) (i : Fin n) (z : Ω) : Point d :=
  stageMainError (G := G) S e r Ds main final N hr hF hell hlo hup x k i z.1

include hG in
/-- Its full distribution is already determined immediately after the actual
kth returned reference was recorded. Later main/final extensions change none
of the source coordinates or recorded references this error reads. -/
theorem main_completed_error_law (x : Point d) (k : ℕ) (hk : k<N) (i : Fin n) :
    (actualLaw x).map (mainCompletedError (G := G) S e r Ds main final N hr hF hell hlo hup x k i) =
    (stageLaw S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x (k+1) (by omega)).map
      (stageMainError (G := G) S e r Ds main final N hr hF hell hlo hup x k i) := by
  let read := stageMainError (G := G) S e r Ds main final N hr hF hell hlo hup x k i ∘
    restorePast S e r Ds main final N (k+1) (by omega)
  have hrm : Measurable read :=
    (stageMainError_measurable (G := G) (hG := hG) S e r Ds main final N hr hDs hmass L hF hell hlo hup x k hk i).comp
      (restorePast_measurable S e r Ds main final N (k+1) (by omega))
  have h := congrArg (fun ν => ν.map read)
    (past_law S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x (k+1) (by omega))
  change ((actualLaw x).map (PrivateChronologicalExecution.past S e r Ds main final N (k+1) (by omega) ∘ Prod.fst)).map read = _ at h
  rw [Measure.map_map hrm
    ((PrivateChronologicalExecution.past_measurable S e r Ds main final N (k+1) (by omega)).comp
      (show Measurable (Prod.fst : Ω → X) from measurable_fst)),
    Measure.map_map hrm (PrivateChronologicalExecution.past_measurable S e r Ds main final N (k+1) (by omega))] at h
  have he1 : read ∘ PrivateChronologicalExecution.past S e r Ds main final N (k+1) (by omega) ∘ (Prod.fst : Ω → X) =
      mainCompletedError (G := G) S e r Ds main final N hr hF hell hlo hup x k i := by
    funext z
    exact restorePast_mainError (G := G) S e r Ds main final N hr hDs hF hell hlo hup x (k+1) (by omega) k (by omega) i z.1
  have he2 : read ∘ PrivateChronologicalExecution.past S e r Ds main final N (k+1) (by omega) =
      stageMainError (G := G) S e r Ds main final N hr hF hell hlo hup x k i := by
    funext z
    exact restorePast_mainError (G := G) S e r Ds main final N hr hDs hF hell hlo hup x (k+1) (by omega) k (by omega) i z
  rw [he1,he2] at h
  exact h

end MainPast

/-- The actual center scale has an integrable square on the augmented coarse
host, including original P. The host is the source law, not an averaging input. -/
theorem coarse_scale_square (hphysical : r^2*ell≤1/2) (x : Point d) (i : Fin n) :
    Integrable (fun c : (Point d × Point d) × Point d =>
      (Gibbs.primitiveScale F (jointPhi S e hF hell hlo hup hr i c.1))^2)
      (PrivateChronologicalLaws.coarseLaw x) ∧
    (∫ c : (Point d × Point d) × Point d,
      (Gibbs.primitiveScale F (jointPhi S e hF hell hlo hup hr i c.1))^2
      ∂PrivateChronologicalLaws.coarseLaw x) ≤
      PrivateBenchmarkMoments.squareBudget flowData x (S.mesh.location m (e i)) := by
  let γ := stdGaussian (Point d)
  let f : ((Point d × Point d) × Point d) → ℝ :=
    fun c => (Gibbs.primitiveScale F (jointPhi S e hF hell hlo hup hr i c.1))^2
  let g : Point d → ℝ := fun seed =>
    (Gibbs.primitiveScale F (PrivateConditionalFlowConsumer.nodePhi S e hF hell hlo hup x hr i seed))^2
  have hgcont := (Gibbs.gradient_lipschitz_of_hessian_bounds hF hell hlo hup).continuous
  have hf : Continuous f := by
    exact (continuous_const.add (hgcont.comp
      ((jointPhi_continuous S e hF hell hlo hup hr i).comp continuous_fst)).norm).pow 2
  have hg : Continuous g := by
    have hp := ConditionalSamplingFlowFields.Phi_continuous hF hell hlo hup x hr
      S.samplingEnd_pos.le S.samplingEnd_lt_one (S.mesh.location m (e i))
    exact (continuous_const.add (hgcont.comp hp).norm).pow 2
  have hemb : MeasurePreserving (fun z : Point d => (x,z)) γ ((Measure.dirac x).prod γ) :=
    ⟨measurable_const.prodMk measurable_id,(Measure.dirac_prod _).symm⟩
  have hp := hemb.prod (MeasurePreserving.id γ)
  have hp0 : MeasurePreserving (Prod.fst : Point d × Point d → Point d) (γ.prod γ) γ :=
    measurePreserving_fst
  have hnode : Integrable g γ := PrivateBenchmarkMoments.node_scale_square_integrable x S e hF hell hlo hup hr i
  have hs : Integrable (g ∘ Prod.fst) (γ.prod γ) :=
    (integrable_map_measure hg.aestronglyMeasurable hp0.measurable.aemeasurable).1 (hp0.map_eq.symm ▸ hnode)
  have he : f ∘ (Prod.map (fun z : Point d => (x,z)) id) = g ∘ Prod.fst := by
    funext z
    dsimp only [f,g,Function.comp_def,Prod.map,id_eq]
    rw [jointPhi_eq_nodePhi S e hF hell hlo hup hr i x z.1]
  have hi : Integrable f (PrivateChronologicalLaws.coarseLaw x) := by
    change Integrable f (((Measure.dirac x).prod γ).prod γ)
    rw [← hp.map_eq]
    apply (integrable_map_measure hf.aestronglyMeasurable hp.measurable.aemeasurable).2
    rw [he]
    exact hs
  refine ⟨hi,?_⟩
  change (∫ c, f c ∂((Measure.dirac x).prod γ).prod γ) ≤ _
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable]
  change (∫ z, (f ∘ Prod.map (fun z : Point d => (x,z)) id) z ∂γ.prod γ) ≤ _
  rw [he]
  have hmap := integral_map (μ := γ.prod γ) hp0.measurable.aemeasurable hg.aestronglyMeasurable
  rw [hp0.map_eq] at hmap
  change (∫ z : Point d × Point d, g z.1 ∂γ.prod γ) ≤ _
  rw [← hmap]
  exact PrivateBenchmarkMoments.node_scale_square_integral_le x S e hF hell hlo hup hr hphysical i

section LowerAveraging
variable (child : ExecutableData) (width amplitude : ℝ) (x : Point d) (i : Fin n)
local notation "Phi" => PrivateConditionalFlowConsumer.nodePhi S e hF hell hlo hup x hr i
local notation "rad" => S.radius r (e i)

def nodeLowerError (z : Point d × ((Point d × Tape d child.program) × Point d)) : Point d :=
  FreshChildRunShift.lowerError child.program G child.coefficient (Phi z.1)
    (Gibbs.primitiveMean F (Phi z.1) rad) width z.2

include hG in
theorem nodeLowerError_stronglyMeasurable :
    StronglyMeasurable (nodeLowerError (G := G) S e r hr hF hell hlo hup child width x i) := by
  apply Measurable.stronglyMeasurable
  have hphi := PrivateConditionalFlowConsumer.nodePhi_measurable S e hF hell hlo hup x hr i
  have hgrad := hG
  have hu := (Gibbs.primitive_mean_lipschitz hF hell hlo hup (S.radius_pos r hr (e i))).continuous.measurable.comp hphi
  have hp := CanonicalTapeMeasurability.program_point_of_measurable child.program G hgrad
    (fun _ => child.coefficient) (fun z : Point d × ((Point d × Tape d child.program) × Point d) => Phi z.1)
    (fun z => z.2.1.1) (fun z => z.2.1.2)
    measurable_const (hphi.comp measurable_fst) measurable_snd.fst.fst measurable_snd.fst.snd
  exact hp.sub ((hu.comp measurable_fst).add (measurable_snd.snd.const_smul width))

variable (lower : Kernel (Point d) ((Point d × Tape d child.program) × Point d)) [IsMarkovKernel lower]
local notation "lowerMix" => (stdGaussian (Point d)) ⊗ₘ lower.comap Phi
  (PrivateConditionalFlowConsumer.nodePhi_measurable S e hF hell hlo hup x hr i)

include hG in
/-- Pointwise LOWER error estimates are averaged over the actual Gaussian-start
benchmark center. Original-data scale moments discharge the averaging demand. -/
theorem node_lower_error_bound (hphysical : r^2*ell≤1/2)
    (hmem : ∀ y : Point d, MemLp (FreshChildRunShift.lowerError child.program G child.coefficient y
      (Gibbs.primitiveMean F y rad) width) 2 (lower y))
    (hbound : ∀ y : Point d, (∫ z : ((Point d × Tape d child.program) × Point d), ‖FreshChildRunShift.lowerError child.program G child.coefficient y
      (Gibbs.primitiveMean F y rad) width z‖^2 ∂lower y) ≤ (amplitude*Gibbs.primitiveScale F y)^2) :
    ∃ _hi : MemLp (nodeLowerError (G := G) S e r hr hF hell hlo hup child width x i) 2 lowerMix,
      (∫ z : Point d × ((Point d × Tape d child.program) × Point d), ‖nodeLowerError (G := G) S e r hr hF hell hlo hup child width x i z‖^2 ∂lowerMix) ≤
        amplitude^2 * PrivateBenchmarkMoments.squareBudget flowData x (S.mesh.location m (e i)) := by
  let err := nodeLowerError (G := G) S e r hr hF hell hlo hup child width x i
  have hs : StronglyMeasurable err := nodeLowerError_stronglyMeasurable (G := G) (hG := hG) S e r hr hF hell hlo hup child width x i
  have hb := PrivateBenchmarkMoments.node_scale_square_integrable x S e hF hell hlo hup hr i
  have hsq : StronglyMeasurable (fun z => ‖err z‖^2) := hs.norm.pow 2
  have hinner : StronglyMeasurable (fun seed : Point d =>
      ∫ z, ‖err (seed,z)‖^2 ∂lower (Phi seed)) :=
    by
      simpa only [Kernel.comap_apply] using
        (StronglyMeasurable.integral_kernel_prod_right
          (κ := lower.comap Phi (PrivateConditionalFlowConsumer.nodePhi_measurable S e hF hell hlo hup x hr i))
          (f := fun (seed : Point d) (z : (Point d × Tape d child.program) × Point d) => ‖err (seed,z)‖^2) hsq)
  have houter : Integrable (fun seed : Point d =>
      ∫ z, ‖err (seed,z)‖^2 ∂lower (Phi seed)) (stdGaussian (Point d)) := by
    apply (hb.const_mul (amplitude^2)).mono' hinner.aestronglyMeasurable
    filter_upwards with seed
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    exact (hbound (Phi seed)).trans_eq (by ring)
  have hint : Integrable (fun z => ‖err z‖^2) lowerMix := by
    apply (Measure.integrable_compProd_iff hsq.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun seed => (memLp_two_iff_integrable_sq_norm (hmem (Phi seed)).aestronglyMeasurable).mp (hmem (Phi seed))
    · simpa only [Kernel.comap_apply,Real.norm_eq_abs,abs_pow,abs_norm] using houter
  have hm : MemLp err 2 lowerMix := (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).2 hint
  refine ⟨hm,?_⟩
  rw [Measure.integral_compProd hint]
  calc
    _ ≤ ∫ seed : Point d, amplitude^2*(Gibbs.primitiveScale F (Phi seed))^2 ∂stdGaussian (Point d) := by
      apply integral_mono houter (hb.const_mul _)
      intro seed
      exact (hbound (Phi seed)).trans_eq (by ring)
    _ = amplitude^2 * (∫ seed : Point d, (Gibbs.primitiveScale F (Phi seed))^2 ∂stdGaussian (Point d)) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (PrivateBenchmarkMoments.node_scale_square_integral_le x S e hF hell hlo hup hr hphysical i) (sq_nonneg _)
end LowerAveraging

section CoarseLowerAveraging
variable (child : ExecutableData) (width amplitude : ℝ) (x : Point d) (i : Fin n)
local notation "H" => (Point d × Point d) × Point d
local notation "center" => (fun c : H => jointPhi S e hF hell hlo hup hr i c.1)

def coarseLowerError (z : H × ((Point d × Tape d child.program) × Point d)) : Point d :=
  FreshChildRunShift.lowerError child.program G child.coefficient (center z.1)
    (Gibbs.primitiveMean F (center z.1) (S.radius r (e i))) width z.2

include hG in
theorem coarseLowerError_stronglyMeasurable :
    StronglyMeasurable (coarseLowerError (G := G) S e r hr hF hell hlo hup child width i) := by
  apply Measurable.stronglyMeasurable
  have hc : Measurable center := (jointPhi_continuous S e hF hell hlo hup hr i).measurable.comp measurable_fst
  have hgrad := hG
  have hu := (Gibbs.primitive_mean_lipschitz hF hell hlo hup (S.radius_pos r hr (e i))).continuous.measurable.comp hc
  have hp := CanonicalTapeMeasurability.program_point_of_measurable child.program G hgrad
    (fun _ => child.coefficient) (fun z : H × ((Point d × Tape d child.program) × Point d) => center z.1)
    (fun z => z.2.1.1) (fun z => z.2.1.2)
    measurable_const (hc.comp measurable_fst) measurable_snd.fst.fst measurable_snd.fst.snd
  exact hp.sub ((hu.comp measurable_fst).add (measurable_snd.snd.const_smul width))

variable (lower : Kernel (Point d) ((Point d × Tape d child.program) × Point d)) [IsMarkovKernel lower]
local notation "mix" => (PrivateChronologicalLaws.coarseLaw x) ⊗ₘ lower.comap center
  ((jointPhi_continuous S e hF hell hlo hup hr i).measurable.comp measurable_fst)

include hG in
/-- LOWER quantitative errors averaged over the exact augmented source host
of each concrete main/final disintegration, retaining original P throughout. -/
theorem coarse_lower_error_bound (hphysical : r^2*ell≤1/2)
    (hmem : ∀ y : Point d, MemLp (FreshChildRunShift.lowerError child.program G child.coefficient y
      (Gibbs.primitiveMean F y (S.radius r (e i))) width) 2 (lower y))
    (hbound : ∀ y : Point d, (∫ z : (Point d × Tape d child.program) × Point d,
      ‖FreshChildRunShift.lowerError child.program G child.coefficient y
        (Gibbs.primitiveMean F y (S.radius r (e i))) width z‖^2 ∂lower y) ≤
      (amplitude*Gibbs.primitiveScale F y)^2) :
    ∃ _hi : MemLp (coarseLowerError (G := G) S e r hr hF hell hlo hup child width i) 2 mix,
      (∫ z : H × ((Point d × Tape d child.program) × Point d),
        ‖coarseLowerError (G := G) S e r hr hF hell hlo hup child width i z‖^2 ∂mix) ≤
      amplitude^2 * PrivateBenchmarkMoments.squareBudget flowData x (S.mesh.location m (e i)) := by
  let err := coarseLowerError (G := G) S e r hr hF hell hlo hup child width i
  have hs := coarseLowerError_stronglyMeasurable (G := G) (hG := hG) S e r hr hF hell hlo hup child width i
  obtain ⟨hscale,hscaleBound⟩ := coarse_scale_square S e r hr hF hell hlo hup hphysical x i
  have hsq : StronglyMeasurable (fun z => ‖err z‖^2) := hs.norm.pow 2
  have hinner : StronglyMeasurable (fun c : H => ∫ z, ‖err (c,z)‖^2 ∂lower (center c)) := by
    simpa only [Kernel.comap_apply] using
      (StronglyMeasurable.integral_kernel_prod_right
        (κ := lower.comap center ((jointPhi_continuous S e hF hell hlo hup hr i).measurable.comp measurable_fst))
        (f := fun (c : H) (z : (Point d × Tape d child.program) × Point d) => ‖err (c,z)‖^2) hsq)
  have houter : Integrable (fun c : H => ∫ z, ‖err (c,z)‖^2 ∂lower (center c))
      (PrivateChronologicalLaws.coarseLaw x) := by
    apply (hscale.const_mul (amplitude^2)).mono' hinner.aestronglyMeasurable
    filter_upwards with c
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    exact (hbound (center c)).trans_eq (by ring)
  have hint : Integrable (fun z => ‖err z‖^2) mix := by
    apply (Measure.integrable_compProd_iff hsq.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun c =>
        (memLp_two_iff_integrable_sq_norm (hmem (center c)).aestronglyMeasurable).mp (hmem (center c))
    · simpa only [Kernel.comap_apply,Real.norm_eq_abs,abs_pow,abs_norm] using houter
  refine ⟨(memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).2 hint,?_⟩
  rw [Measure.integral_compProd hint]
  calc
    _ ≤ ∫ c : H, amplitude^2*(Gibbs.primitiveScale F (center c))^2 ∂PrivateChronologicalLaws.coarseLaw x := by
      apply integral_mono houter (hscale.const_mul _)
      intro c
      exact (hbound (center c)).trans_eq (by ring)
    _ = amplitude^2 * (∫ c : H, (Gibbs.primitiveScale F (center c))^2 ∂PrivateChronologicalLaws.coarseLaw x) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hscaleBound (sq_nonneg _)
end CoarseLowerAveraging

section MainTransport
local notation "Xmain" => History d N n × Tape d (Host S e r Ds main final N)
local notation "centersM" => (fun i (c : (Point d × Point d) × Point d) => jointPhi S e hF hell hlo hup hr i c.1)
local notation "hcentersM" => (fun i => (jointPhi_continuous S e hF hell hlo hup hr i).measurable.comp measurable_fst)

/-- Reaching a positive cursor exposes exactly its current child-batch cut.
This changes only the dependent presentation of the reached source syntax. -/
theorem cursor_batch_split (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (ρ : Measure Xmain) [IsProbabilityMeasure ρ]
    (hw : let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
      ∃ μ : Measure (History d N n × Prefix d s.cut), SFinite μ ∧
        ρ.map (CausalTailHistory.unpack s.cut) =
          μ.prod (tapeLaw L (Loop main final N s.remaining s.old s.direct s.saved))) :
    let cut := batchCut S e r Ds main final N hr hDs hmass s hs
    ∃ μ : Measure (History d N n × Prefix d cut), IsProbabilityMeasure μ ∧
      ρ.map (CausalTailHistory.unpack cut) = μ.prod (tapeLaw L _) ∧
      μ.map (fun z => (z.1.1,z.1.2.2)) =
        ρ.map (PrivateChronologicalLaws.comparison S e r Ds main final N) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => exact False.elim (Nat.not_lt_zero _ hs)
    | succ remaining =>
      obtain ⟨μ,hμ,he⟩ := hw
      let _ := hμ
      let s : Cursor S e r Ds main final N := ⟨remaining+1,ctx,old,direct,saved,cut⟩
      have hp := PrivateChronologicalLaws.prefix_probability_of_split S e r Ds main final N L s.cut ρ μ he
      exact ⟨μ,hp,he,
        PrivateChronologicalLaws.prefix_comparison_of_split S e r Ds main final N L s.cut ρ μ he⟩

/-- Actual main occurrence lower projection, before the chronological record
update. It retains the complete current lower seed and its returned reference. -/
def mainLowerProjection (k : ℕ) (hk : k<N) (i : Fin n) (z : Xmain × (Fin n → Point d)) :
    ((Point d × Point d) × Point d) × ((Point d × Tape d (main i).program) × Point d) :=
  let s := (stage S e r Ds main final N k hk.le).1
  let hs := stage_positive S e r Ds main final N k hk
  let B := data S e r Ds main final N hr hDs hmass s hs
  (z.1.1.1,FreshChildBatchErrorTransfer.completedMap B i
    ((z.1.1.2.2 i,(split (batchCut S e r Ds main final N hr hDs hmass s hs) z.1.2).2.1 i),z.2 i))

/-- The constructed main conditional supplies its exact standalone LOWER
joint law on the actual pre-record sample, with the original P retained. -/
theorem mainLowerProjection_preserving (hm : 0<m) (x : Point d) (k : ℕ) (hk : k<N) (i : Fin n) :
    MeasurePreserving (mainLowerProjection S e r Ds main final N hr hDs hmass k hk i)
      (adjoin S e r Ds main final N hr hDs hmass L hL hF hell hlo hup
        (stage S e r Ds main final N k hk.le).1 (stage_positive S e r Ds main final N k hk) (J k hk) ∘ₘ
          stageLaw S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x k hk.le)
      ((PrivateChronologicalLaws.coarseLaw x) ⊗ₘ ((J k hk).joint i).comap (centersM i) (hcentersM i)) := by
  let s := (stage S e r Ds main final N k hk.le).1
  let hs := stage_positive S e r Ds main final N k hk
  let cut := batchCut S e r Ds main final N hr hDs hmass s hs
  let B := data S e r Ds main final N hr hDs hmass s hs
  let oldLaw := stageLaw S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x k hk.le
  obtain ⟨ν,hν,hsplit,hcmp⟩ := cursor_batch_split S e r Ds main final N hr hDs hmass L s hs oldLaw
    (iteration_whole_suffix S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk.le x)
  let _ := hν
  have hcomparison := hcmp.trans (PrivateChronologicalLaws.iteration_comparison_law
    S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J hm k hk.le x)
  let W := History d N n × Prefix d (PrivateCausalLayer.afterBatch cut)
  let obs : W → ((Point d × Point d) × Point d) × (∀ i, FreshChildBatchCoupling.Raw d B i) :=
    PrivateChronologicalLaws.observed S e r Ds main final N hr hDs hmass s hs
  have hobs : Measurable obs := PrivateChronologicalLaws.observed_measurable S e r Ds main final N hr hDs hmass s hs
  let κ := FreshChildBatchCoupling.referenceBatch L hL B (J k hk) centersM hcentersM
  have he : conditional S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs (J k hk) = κ.comap obs hobs :=
    PrivateChronologicalLaws.conditional_augmented_coarse S e r Ds main final N hr hDs hmass s hs L hL hF hell hlo hup (J k hk)
  let ρ := PrivateCausalLayer.advancedLaw L cut ν
  let _ : IsProbabilityMeasure ρ := PrivateChronologicalLaws.advanced_probability L cut ν
  let η := FreshChildBatchErrorTransfer.observedLaw L hL B (J k hk) centersM hcentersM ρ obs hobs
  let _ : IsProbabilityMeasure η := inferInstance
  have hproject : ρ.map obs = (PrivateChronologicalLaws.coarseLaw x).prod
      (Measure.pi (FreshChildBatchCoupling.rawLaw L B)) :=
    PrivateChronologicalLaws.observation_law S e r Ds main final N hr hDs hmass s hs L ν
      (PrivateChronologicalLaws.coarseLaw x) hcomparison
  have hfull : (adjoin S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs (J k hk) ∘ₘ oldLaw).map
      (CausalTailHistory.unpackExtended (PrivateCausalLayer.afterBatch cut)) = η.prod (tapeLaw L _) := by
    have h := CausalTailHistory.whole_suffix_fresh_of_split L (PrivateCausalLayer.afterBatch cut)
      oldLaw ρ (PrivateCausalLayer.advanced_split_of_split L cut oldLaw ν hsplit) (κ.comap obs hobs)
    change _ = (ρ ⊗ₘ κ.comap obs hobs).prod _
    rw [← he] at h ⊢
    exact h
  have hp := FreshChildBatchErrorTransfer.full_sample_projection_preserving L
    (PrivateCausalLayer.afterBatch cut) _ η hfull
  have hl := FreshChildBatchErrorTransfer.observed_completed_preserving L hL B (J k hk) centersM hcentersM
    ρ (PrivateChronologicalLaws.coarseLaw x) obs hobs hproject i
  convert hl.comp hp using 1 <;> try rfl
  funext z
  simp only [s,cut,B,mainLowerProjection,FreshChildBatchErrorTransfer.lowerProjection,obs,
    PrivateChronologicalLaws.observed,observation,Function.comp_def,PrivateCausalLayer.split_afterBatch,
    PrivateCausalLayer.batchParts_append]

/-- Updating the recorded current reference leaves the earlier benchmark
center unchanged: it reads only already completed layers and the same tape. -/
theorem stageBenchmark_record (x : Point d) (k : ℕ) (hk : k<N) (i : Fin n)
    (z : Xmain × (Fin n → Point d)) :
    stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i
      (record S e r Ds main final N hr hDs hmass
        (stage S e r Ds main final N k hk.le).1
        (stage_positive S e r Ds main final N k hk) ⟨k,hk⟩ z) =
    stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i z.1 := by
  rw [← restorePast_benchmark S e r Ds main final N hr hDs hF hell hlo hup x k hk.le k le_rfl i,
    PrivateChronologicalExecution.past_record S e r Ds main final N hr hDs hmass _ _ k hk.le ⟨k,hk⟩ le_rfl,
    restorePast_benchmark S e r Ds main final N hr hDs hF hell hlo hup x k hk.le k le_rfl i]

/-- Query absorption identifies the lower completed-seed error with the
literal kth evaluator error after the actual returned vector is recorded. -/
theorem main_record_error_eq (x : Point d) (k : ℕ) (hk : k<N) (i : Fin n)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (S.radius r (e i)) (main i).shiftVector)
    (z : Xmain × (Fin n → Point d))
    (hcenter : stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i z.1 =
      jointPhi S e hF hell hlo hup hr i z.1.1.1.1 + rho • z.1.1.2.2 i)
    (hreply : rep x hr i z.1.2 = Gibbs.primitiveMean F
      (jointPhi S e hF hell hlo hup hr i z.1.1.1.1) (S.radius r (e i))) :
    stageMainError (G := G) S e r Ds main final N hr hF hell hlo hup x k i
      (record S e r Ds main final N hr hDs hmass
        (stage S e r Ds main final N k hk.le).1
        (stage_positive S e r Ds main final N k hk) ⟨k,hk⟩ z) =
      coarseLowerError (G := G) S e r hr hF hell hlo hup (main i) sigma i
        (mainLowerProjection S e r Ds main final N hr hDs hmass k hk i z) := by
  let s := (stage S e r Ds main final N k hk.le).1
  let hs := stage_positive S e r Ds main final N k hk
  let B := data S e r Ds main final N hr hDs hmass s hs
  let raw := (z.1.1.2.2 i,(split (batchCut S e r Ds main final N hr hDs hmass s hs) z.1.2).2.1 i)
  have hrun := FreshChildRunShift.run_completedSource (main i).program (main i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i) rho (S.radius r (e i)) Ds
    (main i).shiftVector (main i).coefficient (B.rho_nonneg i) (B.radius_pos i)
    B.Ds_pos (B.shift_budget i) (B.small i) hshift G
    (jointPhi S e hF hell hlo hup hr i z.1.1.1.1) raw
  have hv := congrArg (fun out => (show Point d from out.value)) hrun
  unfold stageMainError
  rw [stageBenchmark_record S e r Ds main final N hr hDs hmass hF hell hlo hup x k hk i z]
  change PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G (rep x hr) k i z.1.2
      (stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i z.1) - rep x hr i z.1.2 -
        sigma • PrivateChronologicalExecution.returnedReference S e r Ds main final N k i
          (record S e r Ds main final N hr hDs hmass s hs ⟨k,hk⟩ z) = _
  rw [PrivateCompletedMainReadout.evaluator_eq_run S e r Ds main final N hr hDs hmass k hk,
    hcenter,hreply]
  have href : PrivateChronologicalExecution.returnedReference S e r Ds main final N k i
      (record S e r Ds main final N hr hDs hmass s hs ⟨k,hk⟩ z) = z.2 i := by
    simp only [PrivateChronologicalExecution.returnedReference,dite_eq_left hk,record,Function.update_self]
  rw [href]
  unfold coarseLowerError FreshChildRunShift.lowerError
  rw [sub_add_eq_sub_sub]
  change _ = (show Point d from (run (main i).program G
    ⟨(main i).coefficient,jointPhi S e hF hell hlo hup hr i z.1.1.1.1,
      (FreshChildAbsorbedLaw.completedSource (main i).program (main i).enumeration
        (B.slot i) (B.old i) (B.designated i) (B.auxiliary i) rho (S.radius r (e i)) (main i).shiftVector raw).1⟩
      Env.empty (FreshChildAbsorbedLaw.completedSource (main i).program (main i).enumeration
        (B.slot i) (B.old i) (B.designated i) (B.auxiliary i) rho (S.radius r (e i)) (main i).shiftVector raw).2).value) -
      (Gibbs.primitiveMean F (jointPhi S e hF hell hlo hup hr i z.1.1.1.1) (S.radius r (e i))) - sigma • z.2 i
  rw [hv]
  rfl


include hG in
/-- Exact law of the literal completed main error, expressed through its
standalone lower joint law at the actual random source center. -/
theorem main_completed_error_lower_law (hm : 0<m) (x : Point d) (k : ℕ) (hk : k<N) (i : Fin n)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (S.radius r (e i)) (main i).shiftVector) :
    (actualLaw x).map (mainCompletedError (G := G) S e r Ds main final N hr hF hell hlo hup x k i) =
      ((PrivateChronologicalLaws.coarseLaw x) ⊗ₘ ((J k hk).joint i).comap (centersM i) (hcentersM i)).map
        (coarseLowerError (G := G) S e r hr hF hell hlo hup (main i) sigma i) := by
  let s := (stage S e r Ds main final N k hk.le).1
  let hs := stage_positive S e r Ds main final N k hk
  let oldLaw := stageLaw S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x k hk.le
  let adjoined := adjoin S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs (J k hk) ∘ₘ oldLaw
  let recordFn := record (d := d) S e r Ds main final N hr hDs hmass s hs ⟨k,hk⟩
  let err := stageMainError (G := G) S e r Ds main final N hr hF hell hlo hup x k i
  let lowerErr := coarseLowerError (G := G) S e r hr hF hell hlo hup (main i) sigma i
  let proj := mainLowerProjection (d := d) S e r Ds main final N hr hDs hmass k hk i
  have hrm : Measurable recordFn := record_measurable S e r Ds main final N hr hDs hmass L s hs ⟨k,hk⟩
  have hem : Measurable err := stageMainError_measurable (G := G) (hG := hG) S e r Ds main final N hr hDs hmass L hF hell hlo hup x k hk i
  have hlem : Measurable lowerErr :=
    (coarseLowerError_stronglyMeasurable (G := G) (hG := hG) S e r hr hF hell hlo hup (main i) sigma i).measurable
  have hp := mainLowerProjection_preserving S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J hm x k hk i
  have hfst : MeasurePreserving (Prod.fst : Xmain × (Fin n → Point d) → Xmain) adjoined oldLaw := by
    refine ⟨measurable_fst,?_⟩
    rw [Measure.map_comp _ _ measurable_fst,← Kernel.fst_eq,adjoin_original,Measure.id_comp]
  have hc := hfst.quasiMeasurePreserving.ae
    (stage_benchmark_center S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x k hk.le)
  have hsupp := hfst.quasiMeasurePreserving.ae
    (stage_source_support S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x k hk.le)
  have hae : err ∘ recordFn =ᵐ[adjoined] lowerErr ∘ proj := by
    filter_upwards [hc,hsupp] with z hz hsource
    apply main_record_error_eq (G := G) S e r Ds main final N hr hDs hmass hF hell hlo hup x k hk i hshift z (hz i)
    rw [PrivateSamplingRetainedRms.reply_eq S e r Ds main final N hF hell hlo hup x hr i z.1.2]
    change Gibbs.primitiveMean F
      (PrivateSamplingFlowResidual.reference S e r Ds main final N hF hell hlo hup x hr i z.1.2)
      (S.radius r (e i)) = _
    congr 1
    rw [jointPhi_eq_nodePhi S e hF hell hlo hup hr i,hsource.1,hsource.2,
      PrivateConditionalFlowConsumer.nodePhi_eq_reference S e hF hell hlo hup x hr Ds main final N i z.1.2]
  have hstage : stageLaw S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x (k+1) (by omega) =
      adjoined.map recordFn := by
    unfold stageLaw
    rw [iteration,← Measure.comp_assoc]
    exact (Measure.map_comp oldLaw _ hrm).symm
  rw [main_completed_error_law (G := G) (hG := hG) S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x k hk i,hstage,
    Measure.map_map hem hrm,Measure.map_congr hae,← Measure.map_map hlem hp.measurable,hp.map_eq]

end MainTransport

/-- Error moments depend only on the exact readout law. -/
theorem memLp_integral_of_law {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (μ : Measure U) (ν : Measure V) (f : U → Point d) (g : V → Point d)
    (hf : Measurable f) (hg : Measurable g) (hlaw : μ.map f = ν.map g)
    (hmem : MemLp g 2 ν) :
    ∃ _hi : MemLp f 2 μ, (∫ z, ‖f z‖^2 ∂μ) = ∫ z, ‖g z‖^2 ∂ν := by
  have hid : MemLp (id : Point d → Point d) 2 (ν.map g) :=
    (memLp_map_measure_iff (measurable_id.aestronglyMeasurable) hg.aemeasurable).2 hmem
  rw [← hlaw] at hid
  refine ⟨(memLp_map_measure_iff measurable_id.aestronglyMeasurable hf.aemeasurable).1 hid,?_⟩
  have h1 := integral_map (μ := μ) hf.aemeasurable
    ((continuous_norm.pow 2).measurable.aestronglyMeasurable :
      AEStronglyMeasurable (fun z : Point d => ‖z‖^2) (μ.map f))
  have h2 := integral_map (μ := ν) hg.aemeasurable
    ((continuous_norm.pow 2).measurable.aestronglyMeasurable :
      AEStronglyMeasurable (fun z : Point d => ‖z‖^2) (ν.map g))
  rw [hlaw] at h1
  exact h1.symm.trans h2

include hG in
/-- Each actual completed main-child error is paid by its standalone LOWER
quantitative IH and the original-data moment of its source flow center. -/
theorem main_completed_error_bound (hm : 0<m) (hphysical : r^2*ell≤1/2)
    (x : Point d) (k : ℕ) (hk : k<N) (i : Fin n) (amplitude : ℝ)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (S.radius r (e i)) (main i).shiftVector)
    (hmem : ∀ y : Point d, MemLp (FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
      (Gibbs.primitiveMean F y (S.radius r (e i))) sigma) 2 ((J k hk).joint i y))
    (hbound : ∀ y : Point d, (∫ z : (Point d × Tape d (main i).program) × Point d,
      ‖FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
        (Gibbs.primitiveMean F y (S.radius r (e i))) sigma z‖^2 ∂(J k hk).joint i y) ≤
      (amplitude*Gibbs.primitiveScale F y)^2) :
    ∃ _hi : MemLp (mainCompletedError (G := G) S e r Ds main final N hr hF hell hlo hup x k i) 2 (actualLaw x),
      (∫ z : Ω, ‖mainCompletedError (G := G) S e r Ds main final N hr hF hell hlo hup x k i z‖^2 ∂actualLaw x) ≤
        amplitude^2*PrivateBenchmarkMoments.squareBudget flowData x (S.mesh.location m (e i)) := by
  let _ : IsMarkovKernel ((J k hk).joint i) := (J k hk).markov i
  obtain ⟨hi,hB⟩ := coarse_lower_error_bound (G := G) (hG := hG) S e r hr hF hell hlo hup
    (main i) sigma amplitude x i ((J k hk).joint i) hphysical hmem hbound
  have hlaw := main_completed_error_lower_law (G := G) (hG := hG) S e r Ds main final N hr hDs hmass hfinalMass
    L hL hF hell hlo hup Jf J hm x k hk i hshift
  have hf : Measurable (mainCompletedError (G := G) S e r Ds main final N hr hF hell hlo hup x k i) :=
    (stageMainError_measurable (G := G) (hG := hG) S e r Ds main final N hr hDs hmass L hF hell hlo hup x k hk i).comp measurable_fst
  obtain ⟨hm,he⟩ := memLp_integral_of_law _ _ _ _ hf
    (coarseLowerError_stronglyMeasurable (G := G) (hG := hG) S e r hr hF hell hlo hup (main i) sigma i).measurable hlaw hi
  exact ⟨hm,he.le.trans hB⟩

section FinalTransport
local notation "cut" => terminalCut S e r Ds main final N
local notation "Bf" => PrivateFinalCoupling.data S e r Ds main final N hr hDs hfinalMass
  (terminalCursor S e r Ds main final N).old
local notation "centers" => (fun i (c : (Point d × Point d) × Point d) => jointPhi S e hF hell hlo hup hr i c.1)
local notation "hcenters" => (fun i => (jointPhi_continuous S e hF hell hlo hup hr i).measurable.comp measurable_fst)

/-- Complete actual final occurrence lower seed, with its returned reference.
The observed child tape and current comparison are literal retained fields. -/
def finalLowerProjection (i : Fin n) (z : Ω) :
    ((Point d × Point d) × Point d) × ((Point d × Tape d (final i).program) × Point d) :=
  (z.1.1.1,FreshChildBatchErrorTransfer.completedMap Bf i
    ((z.1.1.2.2 i,(split cut z.1.2).2.1 i),z.2 i))

/-- The actual final batch disintegration transports the LOWER joint law
onto the original full completed sample, including its correlated old history. -/
theorem finalLowerProjection_preserving (hm : 0<m) (x : Point d) (i : Fin n) :
    MeasurePreserving (finalLowerProjection S e r Ds main final N hr hDs hfinalMass i) (actualLaw x)
      ((PrivateChronologicalLaws.coarseLaw x) ⊗ₘ (Jf.joint i).comap
        (centers i) (hcenters i)) := by
  obtain ⟨ν,hν,hsplit,hcomparison⟩ := PrivateChronologicalFinish.kernel_terminalCut_laws
    S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J hm x
  let _ := hν
  let oldLaw := PrivateChronologicalCoupling.kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x
  let W := History d N n × Prefix d (PrivateCausalLayer.afterBatch cut)
  let obs : W → ((Point d × Point d) × Point d) × (∀ i, FreshChildBatchCoupling.Raw d Bf i) :=
    PrivateCompletedLaws.observed S e r Ds main final N hr hDs hfinalMass
  have hobs : Measurable obs := PrivateCompletedLaws.observed_measurable S e r Ds main final N hr hDs hfinalMass
  let κ := FreshChildBatchCoupling.referenceBatch L hL Bf Jf centers hcenters
  have he : PrivateCompletedCoupling.finalConditional S e r Ds main final N hr hDs hfinalMass
      L hL hF hell hlo hup Jf = κ.comap obs hobs :=
    PrivateCompletedLaws.conditional_augmented_coarse S e r Ds main final N hr hDs hfinalMass L hL hF hell hlo hup Jf
  let ρ := PrivateCausalLayer.advancedLaw L cut ν
  let _ : IsProbabilityMeasure ρ := PrivateChronologicalLaws.advanced_probability L cut ν
  let η := FreshChildBatchErrorTransfer.observedLaw L hL Bf Jf centers hcenters ρ obs hobs
  let _ : IsProbabilityMeasure η := inferInstance
  have hproject : ρ.map obs = (PrivateChronologicalLaws.coarseLaw x).prod
      (Measure.pi (FreshChildBatchCoupling.rawLaw L Bf)) :=
    PrivateCompletedLaws.observation_law S e r Ds main final N hr hDs hfinalMass L ν
      (PrivateChronologicalLaws.coarseLaw x) hcomparison
  have hfull : (actualLaw x).map
      (CausalTailHistory.unpackExtended (PrivateCausalLayer.afterBatch cut)) =
      η.prod (tapeLaw L (PrivateFinalCoupling.suffix main final N
        ((terminalCursor S e r Ds main final N).saved (RefMap.shiftMany n .here)))) := by
    have h := CausalTailHistory.whole_suffix_fresh_of_split L (PrivateCausalLayer.afterBatch cut)
      oldLaw ρ (PrivateCausalLayer.advanced_split_of_split L cut oldLaw ν hsplit) (κ.comap obs hobs)
    change _ = (ρ ⊗ₘ κ.comap obs hobs).prod _
    rw [← he] at h ⊢
    simpa only [law,PrivateCompletedCoupling.kernel,Kernel.comp_apply,
      PrivateCompletedCoupling.finalKernel,oldLaw,PrivateFinalCoupling.suffix] using h
  have hp := FreshChildBatchErrorTransfer.full_sample_projection_preserving L
    (PrivateCausalLayer.afterBatch cut) (actualLaw x) η hfull
  have hl := FreshChildBatchErrorTransfer.observed_completed_preserving L hL Bf Jf centers hcenters
    ρ (PrivateChronologicalLaws.coarseLaw x) obs hobs hproject i
  convert hl.comp hp using 1 <;> try rfl
  funext z
  simp only [finalLowerProjection,FreshChildBatchErrorTransfer.lowerProjection,obs,
    PrivateCompletedLaws.observed,Function.comp_def,PrivateCausalLayer.split_afterBatch,
    PrivateCausalLayer.batchParts_append]
/-- The transported error on the same completed final occurrence, retaining
its original lower source seed and returned reference. -/
def finalCompletedError (i : Fin n) (z : Ω) : Point d :=
  coarseLowerError (G := G) S e r hr hF hell hlo hup (final i) (samplingFinalWidth S r) i
    (finalLowerProjection S e r Ds main final N hr hDs hfinalMass i z)

include hG in
/-- Original-data moment averaging and the actual final disintegration supply
the complete final child error estimate from only its standalone LOWER IH. -/
theorem final_completed_error_bound (hm : 0<m) (hphysical : r^2*ell≤1/2)
    (x : Point d) (i : Fin n) (amplitude : ℝ)
    (hmem : ∀ y : Point d, MemLp (FreshChildRunShift.lowerError (final i).program G (final i).coefficient y
      (Gibbs.primitiveMean F y (S.radius r (e i))) (samplingFinalWidth S r)) 2 (Jf.joint i y))
    (hbound : ∀ y : Point d, (∫ z : (Point d × Tape d (final i).program) × Point d,
      ‖FreshChildRunShift.lowerError (final i).program G (final i).coefficient y
        (Gibbs.primitiveMean F y (S.radius r (e i))) (samplingFinalWidth S r) z‖^2 ∂Jf.joint i y) ≤
      (amplitude*Gibbs.primitiveScale F y)^2) :
    ∃ _hi : MemLp (finalCompletedError (G := G) S e r Ds main final N hr hDs hfinalMass hF hell hlo hup i) 2 (actualLaw x),
      (∫ z : Ω, ‖finalCompletedError (G := G) S e r Ds main final N hr hDs hfinalMass hF hell hlo hup i z‖^2 ∂actualLaw x) ≤
        amplitude^2*PrivateBenchmarkMoments.squareBudget flowData x (S.mesh.location m (e i)) := by
  let _ : IsMarkovKernel (Jf.joint i) := Jf.markov i
  obtain ⟨hi,hB⟩ := coarse_lower_error_bound (G := G) (hG := hG) S e r hr hF hell hlo hup
    (final i) (samplingFinalWidth S r) amplitude x i (Jf.joint i) hphysical hmem hbound
  have hp := finalLowerProjection_preserving S e r Ds main final N hr hDs hmass hfinalMass
    L hL hF hell hlo hup Jf J hm x i
  refine ⟨hi.comp_measurePreserving hp,?_⟩
  have hmap := integral_map hp.measurable.aemeasurable
    (hp.map_eq.symm ▸ hi.aestronglyMeasurable.norm.pow 2)
  rw [hp.map_eq] at hmap
  exact hmap.ge.trans hB

/-- Literal final callback error at the actual completed benchmark, in the
order used by the existing paid-final RMS propagation theorem. -/
def finalLiteralError (x P : Point d) (i : Fin n) (z : Ω) : Point d :=
  PrivateSamplingRetainedRms.finalEvaluator S e r Ds main final N x G P z.1.2 i
    (stageBenchmark S e r Ds main final N hr hF hell hlo hup x N i z.1) -
      samplingFinalWidth S r • z.2 i - rep x hr i z.1.2

/-- The literal final callback uses the same complete transformed seed as
the constructed terminal conditional; query absorption pays its lower error. -/
theorem final_literal_error_eq (x P : Point d) (i : Fin n)
    (hshift : ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (S.radius r (e i)) (final i).shiftVector) :
    finalLiteralError (G := G) S e r Ds main final N hr hF hell hlo hup x P i =ᵐ[actualLaw x]
      finalCompletedError (G := G) S e r Ds main final N hr hDs hfinalMass hF hell hlo hup i := by
  have hb := (prior_preserving S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x).quasiMeasurePreserving.ae
    (stage_benchmark_center S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x N le_rfl)
  filter_upwards [hb,source_support S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x] with z hz hsource
  change z.1.1.1.1.1=x ∧ z.1.1.1.1.2=(show Point d from z.1.2.2.1) at hsource
  let B := Bf
  let raw := (z.1.1.2.2 i,(split cut z.1.2).2.1 i)
  have hrun := FreshChildRunShift.run_completedSource (final i).program (final i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i) rho (S.radius r (e i)) Ds
    (final i).shiftVector (final i).coefficient (B.rho_nonneg i) (B.radius_pos i)
    B.Ds_pos (B.shift_budget i) (B.small i) hshift G
    (jointPhi S e hF hell hlo hup hr i z.1.1.1.1) raw
  have hv := congrArg (fun out => (show Point d from out.value)) hrun
  have hreply : rep x hr i z.1.2 = Gibbs.primitiveMean F
      (jointPhi S e hF hell hlo hup hr i z.1.1.1.1) (S.radius r (e i)) := by
    rw [PrivateSamplingRetainedRms.reply_eq S e r Ds main final N hF hell hlo hup x hr i z.1.2]
    change Gibbs.primitiveMean F
      (PrivateSamplingFlowResidual.reference S e r Ds main final N hF hell hlo hup x hr i z.1.2)
      (S.radius r (e i)) = _
    congr 1
    rw [jointPhi_eq_nodePhi S e hF hell hlo hup hr i,hsource.1,hsource.2,
      PrivateConditionalFlowConsumer.nodePhi_eq_reference S e hF hell hlo hup x hr Ds main final N i z.1.2]
  unfold finalLiteralError
  rw [PrivateFinalEvaluatorReadout.finalEvaluator_eq_terminalSeed,hz i,hreply]
  unfold finalCompletedError coarseLowerError FreshChildRunShift.lowerError
  rw [sub_add_eq_sub_sub]
  change _ = (show Point d from (run (final i).program G
    ⟨(final i).coefficient,jointPhi S e hF hell hlo hup hr i z.1.1.1.1,
      (FreshChildAbsorbedLaw.completedSource (final i).program (final i).enumeration
        (B.slot i) (B.old i) (B.designated i) (B.auxiliary i) rho (S.radius r (e i)) (final i).shiftVector raw).1⟩
      Env.empty (FreshChildAbsorbedLaw.completedSource (final i).program (final i).enumeration
        (B.slot i) (B.old i) (B.designated i) (B.auxiliary i) rho (S.radius r (e i)) (final i).shiftVector raw).2).value) -
      (Gibbs.primitiveMean F (jointPhi S e hF hell hlo hup hr i z.1.1.1.1) (S.radius r (e i))) - samplingFinalWidth S r • z.2 i
  rw [hv]
  dsimp only [PrivateFinalEvaluatorReadout.terminalSeed,ReplaySeedMeasurability.transformedSeed,B,raw,PrivateFinalCoupling.data]
  exact sub_right_comm (show Point d from _) _ _

include hG in
/-- Actual final evaluator membership and payment follow from only the LOWER
standalone quantitative bound, including the original flow-center moment. -/
theorem final_literal_error_bound (hm : 0<m) (hphysical : r^2*ell≤1/2)
    (x P : Point d) (i : Fin n) (amplitude : ℝ)
    (hshift : ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (S.radius r (e i)) (final i).shiftVector)
    (hmem : ∀ y : Point d, MemLp (FreshChildRunShift.lowerError (final i).program G (final i).coefficient y
      (Gibbs.primitiveMean F y (S.radius r (e i))) (samplingFinalWidth S r)) 2 (Jf.joint i y))
    (hbound : ∀ y : Point d, (∫ z : (Point d × Tape d (final i).program) × Point d,
      ‖FreshChildRunShift.lowerError (final i).program G (final i).coefficient y
        (Gibbs.primitiveMean F y (S.radius r (e i))) (samplingFinalWidth S r) z‖^2 ∂Jf.joint i y) ≤
      (amplitude*Gibbs.primitiveScale F y)^2) :
    ∃ _hi : MemLp (finalLiteralError (G := G) S e r Ds main final N hr hF hell hlo hup x P i) 2 (actualLaw x),
      (∫ z : Ω, ‖finalLiteralError (G := G) S e r Ds main final N hr hF hell hlo hup x P i z‖^2 ∂actualLaw x) ≤
        amplitude^2*PrivateBenchmarkMoments.squareBudget flowData x (S.mesh.location m (e i)) := by
  obtain ⟨hi,hB⟩ := final_completed_error_bound (G := G) (hG := hG) S e r Ds main final N hr hDs hmass hfinalMass
    L hL hF hell hlo hup Jf J hm hphysical x i amplitude hmem hbound
  have he := final_literal_error_eq (G := G) S e r Ds main final N hr hDs hmass hfinalMass
    L hL hF hell hlo hup Jf J x P i hshift
  refine ⟨(memLp_congr_ae he).2 hi,?_⟩
  have hiEq : (∫ z : Ω, ‖finalLiteralError (G := G) S e r Ds main final N hr hF hell hlo hup x P i z‖^2 ∂actualLaw x) =
      (∫ z : Ω, ‖finalCompletedError (G := G) S e r Ds main final N hr hDs hfinalMass hF hell hlo hup i z‖^2 ∂actualLaw x) := by
    apply integral_congr_ae
    filter_upwards [he] with z hz
    rw [hz]
  exact hiEq.le.trans hB
end FinalTransport


section NumericalJoin

/-- The literal SharedLayer benchmark commutes with reading the unchanged
prior sample from the completed augmentation. -/
theorem completed_benchmark_eq (x : Point d) (k : ℕ) (i : Fin n) (z : Ω) :
    SharedLayerRms.benchmark
      (fun j z => ref x hr j z.1.2) A Cmat sigma
      (SourceMeanRetainedRms.finiteReference N (mainReference S e r Ds main final N))
      (fun k i z => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i z.1.2)
      (fun i z => PrivateSamplingRetainedRms.initialNoise S e r Ds main final N i z.1.2) k i z =
    stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i z.1 := by
  cases k <;> rfl

/-- Explicit original-data RMS payment for one lower child at its actual
random center; the source center's square moment is retained. -/
def childPayment (x : Point d) (i : Fin n) (amplitude : ℝ) : ℝ :=
  Real.sqrt (amplitude^2*PrivateBenchmarkMoments.squareBudget flowData x (S.mesh.location m (e i)))

theorem childPayment_sq (x : Point d) (i : Fin n) (amplitude : ℝ) :
    (childPayment S e r hr hF hell hlo hup x i amplitude)^2 =
      amplitude^2*PrivateBenchmarkMoments.squareBudget flowData x (S.mesh.location m (e i)) := by
  apply Real.sq_sqrt
  apply mul_nonneg (sq_nonneg _)
  unfold PrivateBenchmarkMoments.squareBudget
  positivity

theorem residualBudget_nonneg : 0≤residualBudget S r hr hF hell hlo hup := by
  unfold residualBudget
  apply mul_nonneg (mul_nonneg (sq_nonneg _) S.samplingEnd_pos.le)
  unfold AffineResidual.cellBudget
  apply Finset.sum_nonneg
  intro c _
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (S.mesh.length_pos c).le _))
    (SamplingGaussianJetLp.cellDerivativeBudget_nonneg flowData S.mesh m c)) (Nat.cast_nonneg _)

/-- Actual synchronous iterate on the completed source sample. -/
def completedIterate (x : Point d) : ℕ → Fin n → Ω → Point d :=
  SharedLayerRms.iterate
    (fun j z => x+(r*S.mesh.location m (e j)) • (show Point d from (tape S e r Ds main final N z).2.1)) A Cmat
    (fun k i z => PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G (rep x hr) k i (tape S e r Ds main final N z))
    (fun k i z => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i (tape S e r Ds main final N z))
    (fun i z => PrivateSamplingExecutionSchedule.initial S e r Ds main final N x (tape S e r Ds main final N z) i)

def mainDifference (x : Point d) (k : ℕ) (i : Fin n) (z : Ω) : Point d :=
  PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G (rep x hr) k i z.1.2
    (completedIterate (G := G) S e r Ds main final N hr hF hell hlo hup x k i z) -
  PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G (rep x hr) k i z.1.2
    (stageBenchmark S e r Ds main final N hr hF hell hlo hup x k i z.1)

def finalDifference (x P : Point d) (i : Fin n) (z : Ω) : Point d :=
  let st := PrivateSamplingTapeProjections.state (samplingConfig main final N) G
    (PrivateSamplingExecutionSchedule.inp S e r Ds main final x P) z.1.2
  PrivateSamplingRetainedRms.finalEvaluator S e r Ds main final N x G P z.1.2 i (storedPoint st.env (st.old i)) -
    PrivateSamplingRetainedRms.finalEvaluator S e r Ds main final N x G P z.1.2 i
      (stageBenchmark S e r Ds main final N hr hF hell hlo hup x N i z.1)

def executed (x P : Point d) (z : Ω) : Point d :=
  (run (SamplingExecutable.build S e r Ds main final N).program G
    (PrivateSamplingExecutionSchedule.inp S e r Ds main final x P) Env.empty z.1.2).value

/-- Numerical target with the actual final returned references and the literal
source initial, residual, and reserve coordinates. -/
def numericalTarget (x : Point d) (z : Ω) : Point d :=
  let noise := PrivateSamplingTapeProjections.coordinates (samplingConfig main final N) z.1.2
  (samplingEnd S.τ)⁻¹ • noise (.inl ()) +
    (samplingBeta S e r • noise (.inr (.inr (.inl ()))) +
      (S.τ/2) • noise (.inr (.inr (.inr ())))) +
    ∑ i, samplingFinalWeight S e r i • (rep x hr i z.1.2 + samplingFinalWidth S r • z.2 i)

def numericalError (x P : Point d) (z : Ω) : Point d :=
  executed (G := G) S e r Ds main final N x P z - numericalTarget S e r Ds main final N hr hF hell hlo hup x z

/-- The exact finite numerical main-layer payment, with every executed lower
child and the original initializer/residual budgets displayed. -/
def mainBudget (x : Point d) (κ : ℝ≥0) (amplitude : ℕ → Fin n → ℝ) : ℝ :=
  ((κ:ℝ)*r^2)^N*initializerBudget S r hr hF hell hlo hup x +
    Collocation.forcingSum ((κ:ℝ)*r^2)
      (fun k => residualBudget S r hr hF hell hlo hup + SharedLayerRms.childRowBudget A
        (SourceMeanExecutionRms.finiteBudget N (fun k i => childPayment S e r hr hF hell hlo hup x i (amplitude k i))) k) N

include hG in
/-- The actual completed coupling satisfies the paid-final numerical RMS
bound using only standalone LOWER quantitative IHs and original-data budgets.
The remaining stability/measurability inputs concern deterministic callbacks. -/
theorem numerical_error_bound (hm : 1≤m) (hphysical : r^2*ell≤1/2)
    (x P : Point d) (κ κf : ℝ≥0) (amplitude : ℕ → Fin n → ℝ) (amplitudeF : Fin n → ℝ)
    (hshift : ∀ i, ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (S.radius r (e i)) (main i).shiftVector)
    (hshiftF : ∀ i, ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (S.radius r (e i)) (final i).shiftVector)
    (hstable : ∀ i, FixedTapeStability.ChildStable (main i).program (main i).coefficient G κ)
    (hstableF : ∀ i, FixedTapeStability.ChildStable (final i).program (final i).coefficient G κf)
    (hmeas : ∀ k, k<N → ∀ i, AEStronglyMeasurable (mainDifference (G := G) S e r Ds main final N hr hF hell hlo hup x k i) (actualLaw x))
    (hmeasF : ∀ i, AEStronglyMeasurable (finalDifference (G := G) S e r Ds main final N hr hF hell hlo hup x P i) (actualLaw x))
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
    ∃ hout : MemLp (numericalError (G := G) S e r Ds main final N hr hF hell hlo hup x P) 2 (actualLaw x),
      ‖hout.toLp (numericalError (G := G) S e r Ds main final N hr hF hell hlo hup x P)‖ ≤
        r*((κf:ℝ)*mainBudget S e r N hr hF hell hlo hup x κ amplitude) +
          ∑ i, |samplingFinalWeight S e r i| * childPayment S e r hr hF hell hlo hup x i (amplitudeF i) := by
  obtain ⟨hinit,hinitB⟩ := initializer_bound S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J hphysical x
  obtain ⟨hres,hresB⟩ := row_bound S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J hphysical hm x
  have hc := fun k hk i => main_completed_error_bound (G := G) (hG := hG) S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J
    (by omega) hphysical x k hk i (amplitude k i) (hshift i) (hmem k hk i) (hbound k hk i)
  have hfc := fun i => final_literal_error_bound (G := G) (hG := hG) S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J
    (by omega) hphysical x P i (amplitudeF i) (hshiftF i) (hmemF i) (hboundF i)
  let hcMem := fun k hk i => (hc k hk i).choose
  let hfcMem := fun i => (hfc i).choose
  have hcB (k : ℕ) (hk : k<N) (i : Fin n) :
      ‖(hcMem k hk i).toLp (mainCompletedError (G := G) S e r Ds main final N hr hF hell hlo hup x k i)‖ ≤
        childPayment S e r hr hF hell hlo hup x i (amplitude k i) := by
    apply FreshChildBatchErrorTransfer.norm_toLp_le_of_square_integral _ _ _ _ (Real.sqrt_nonneg _)
    change _ ≤ (childPayment S e r hr hF hell hlo hup x i (amplitude k i))^2
    rw [childPayment_sq]
    exact (hc k hk i).choose_spec
  have hfcB (i : Fin n) :
      ‖(hfcMem i).toLp (finalLiteralError (G := G) S e r Ds main final N hr hF hell hlo hup x P i)‖ ≤
        childPayment S e r hr hF hell hlo hup x i (amplitudeF i) := by
    apply FreshChildBatchErrorTransfer.norm_toLp_le_of_square_integral _ _ _ _ (Real.sqrt_nonneg _)
    change _ ≤ (childPayment S e r hr hF hell hlo hup x i (amplitudeF i))^2
    rw [childPayment_sq]
    exact (hfc i).choose_spec
  have hmainEq (k : ℕ) (hk : k<N) (i : Fin n) :
      SharedLayerRms.childError
        (fun k i z => PrivateSamplingExecutionSchedule.evaluator S e r Ds main final N G (rep x hr) k i (tape S e r Ds main final N z))
        (SharedLayerRms.benchmark (fun j z => ref x hr j (tape S e r Ds main final N z)) A Cmat sigma
          (SourceMeanRetainedRms.finiteReference N (mainReference S e r Ds main final N))
          (fun k i z => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i (tape S e r Ds main final N z))
          (fun i z => PrivateSamplingRetainedRms.initialNoise S e r Ds main final N i (tape S e r Ds main final N z)))
        (fun j z => rep x hr j (tape S e r Ds main final N z)) sigma
        (SourceMeanRetainedRms.finiteReference N (mainReference S e r Ds main final N)) k i =
      mainCompletedError (G := G) S e r Ds main final N hr hF hell hlo hup x k i := by
    funext z
    simp only [SharedLayerRms.childError,SourceMeanRetainedRms.finiteReference,ite_eq_left hk,
      mainCompletedError,stageMainError,mainReference,tape,completed_benchmark_eq]
  have hfinalEq (i : Fin n) :
      (fun z : Ω => PrivateSamplingRetainedRms.finalEvaluator S e r Ds main final N x G P
        (tape S e r Ds main final N z) i
        (SharedLayerRms.benchmark (fun j z => ref x hr j (tape S e r Ds main final N z)) A Cmat sigma
          (SourceMeanRetainedRms.finiteReference N (mainReference S e r Ds main final N))
          (fun k i z => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i (tape S e r Ds main final N z))
          (fun i z => PrivateSamplingRetainedRms.initialNoise S e r Ds main final N i (tape S e r Ds main final N z)) N i z) -
        samplingFinalWidth S r • finalReference S e r Ds main final N i z - rep x hr i (tape S e r Ds main final N z)) =
      finalLiteralError (G := G) S e r Ds main final N hr hF hell hlo hup x P i := by
    funext z
    simp only [tape,completed_benchmark_eq]
    rfl
  obtain ⟨hout,houtB⟩ := PrivateSamplingRetainedRms.retained_output_error_bound S e r Ds main final N
    hF hell hlo hup x hr (actualLaw x) G P (tape S e r Ds main final N) (mainReference S e r Ds main final N)
    κ κf (r^2) (residualBudget S r hr hF hell hlo hup) (sq_nonneg _) (residualBudget_nonneg S r hr hF hell hlo hup)
    (fun k i => childPayment S e r hr hF hell hlo hup x i (amplitude k i))
    (FixedTapeSampling.sampling_matrix_mass_le S e r (by omega) hr.le) hstable
    (by
      intro k hk i
      convert hmeas k hk i using 1
      funext z
      simp only [tape,completed_benchmark_eq]
      rfl)
    hinit hres hresB (by intro k hk i; rw [hmainEq k hk i]; exact hcMem k hk i)
    (by intro k hk i; simpa only [hmainEq k hk i] using hcB k hk i)
    (finalReference S e r Ds main final N) (fun i => childPayment S e r hr hF hell hlo hup x i (amplitudeF i)) hstableF
    (by
      intro i
      convert hmeasF i using 1
      funext z
      simp only [tape,completed_benchmark_eq]
      rfl)
    (by intro i; rw [hfinalEq i]; exact hfcMem i)
    (by intro i; simpa only [hfinalEq i] using hfcB i)
  change MemLp (numericalError (G := G) S e r Ds main final N hr hF hell hlo hup x P) 2 (actualLaw x) at hout
  refine ⟨hout,?_⟩
  change ‖hout.toLp (numericalError (G := G) S e r Ds main final N hr hF hell hlo hup x P)‖ ≤ _ at houtB
  rw [FixedTapeSampling.sampling_final_mass S e r (by omega) hr.le] at houtB
  apply houtB.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hr.le
  apply mul_le_mul_of_nonneg_left _ κf.coe_nonneg
  unfold mainBudget
  exact add_le_add (mul_le_mul_of_nonneg_left hinitB (by positivity)) le_rfl

/-- The original private top-level parent momentum is retained in the joint
law; its literal execution is pointwise independent of that external input. -/
theorem executed_momentum_eq (x P P' : Point d) (z : Ω) :
    executed (G := G) S e r Ds main final N x P z = executed (G := G) S e r Ds main final N x P' z := by
  exact FixedTapeSampling.build_momentum_eq S e r Ds main final N G x P' P z.1.2

/-- The existing full interpreter and the actual reached chronological cut
read the identical physical final residual occurrence. -/
theorem residual_coordinate_eq (ω : Tape d (Host S e r Ds main final N)) :
    PrivateSamplingTapeProjections.coordinates (samplingConfig main final N) ω (.inr (.inr (.inl ()))) =
      (split (terminalCut S e r Ds main final N) ω).2.2.1 := by
  rw [PrivateSamplingTapeProjections.residual_eq (samplingConfig main final N) (fun y : Point d => y)
    (PrivateSamplingExecutionSchedule.inp S e r Ds main final (0 : Point d) 0) ω]
  exact (congrArg (fun st : FinalState (samplingSize main final) n d
      (PrivateSamplingExecutionSchedule.Entry n) .point (PrivateSamplingExecutionSchedule.finisher main final N) => st.tape.2.1)
    (PrivateFinalEvaluatorReadout.terminalState_eq_state S e r Ds main final N (fun y : Point d => y)
      (PrivateSamplingExecutionSchedule.inp S e r Ds main final (0 : Point d) 0) ω)).symm

/-- The separately paid reserve is also the same original unread occurrence. -/
theorem reserve_coordinate_eq (ω : Tape d (Host S e r Ds main final N)) :
    PrivateSamplingTapeProjections.coordinates (samplingConfig main final N) ω (.inr (.inr (.inr ()))) =
      (split (terminalCut S e r Ds main final N) ω).2.2.2.1 := by
  rw [PrivateSamplingTapeProjections.reserve_eq (samplingConfig main final N) (fun y : Point d => y)
    (PrivateSamplingExecutionSchedule.inp S e r Ds main final (0 : Point d) 0) ω]
  exact (congrArg (fun st : FinalState (samplingSize main final) n d
      (PrivateSamplingExecutionSchedule.Entry n) .point (PrivateSamplingExecutionSchedule.finisher main final N) => st.tape.2.2.1)
    (PrivateFinalEvaluatorReadout.terminalState_eq_state S e r Ds main final N (fun y : Point d => y)
      (PrivateSamplingExecutionSchedule.inp S e r Ds main final (0 : Point d) 0) ω)).symm

/-- The numerical target differs from the actual completed reference readout
by exactly the source final-row quadrature defect, with all physical factors. -/
theorem numerical_target_sub_reference (x : Point d) :
    (fun z => numericalTarget S e r Ds main final N hr hF hell hlo hup x z -
      PrivateCompletedReference.output S e r Ds main final N hr hF hell hlo hup x z) =ᵐ[actualLaw x]
        quadratureError S e r Ds main final N hr hF hell hlo hup x := by
  filter_upwards [source_support S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x] with z hz
  change z.1.1.1.1.1=x ∧ z.1.1.1.1.2=(show Point d from z.1.2.2.1) at hz
  unfold numericalTarget PrivateCompletedReference.output PrivateReferenceAssembly.output
    PrivateCompletedLaws.finalObservation CausalTailHistory.unpackExtended CausalTailHistory.unpack
  rw [PrivateCausalLayer.split_afterBatch]
  dsimp only
  rw [PrivateSamplingTapeProjections.position_eq,residual_coordinate_eq,reserve_coordinate_eq,hz.2]
  unfold quadratureError PrivateSamplingReferenceLaw.readout PrivateFinalGaussian.preNoise
  simp only [tape,SamplingFlowLp.sourcePath,SamplingFlowLp.sourceTime_eq S.samplingEnd_pos.le
    (show samplingEnd S.τ ∈ Set.Icc 0 (samplingEnd S.τ) from ⟨S.samplingEnd_pos.le,le_rfl⟩)]
  simp only [smul_add,Finset.sum_add_distrib]
  abel

/-- Actual executed output coupled to the completed reference, retaining its
original parent momentum and entire source tape. -/
def retainedError (x : Point d) (z : Ω) : Point d :=
  executed (G := G) S e r Ds main final N x z.1.1.1.2 z -
    PrivateCompletedReference.output S e r Ds main final N hr hF hell hlo hup x z

/-- Attach the proved original-data final quadrature defect to a numerical
RMS bound on this exact completed coupling. -/
theorem retained_error_of_numerical (hm : 1≤m) (hphysical : r^2*ell≤1/2)
    (x P : Point d) (B : ℝ)
    (hn : MemLp (numericalError (G := G) S e r Ds main final N hr hF hell hlo hup x P) 2 (actualLaw x))
    (hnB : ‖hn.toLp (numericalError (G := G) S e r Ds main final N hr hF hell hlo hup x P)‖ ≤ B) :
    ∃ hout : MemLp (retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x) 2 (actualLaw x),
      ‖hout.toLp (retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x)‖ ≤ B+quadratureBudget S r hr hF hell hlo hup := by
  obtain ⟨hq,hqB⟩ := quadrature_bound S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J hphysical hm x
  have he : retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x =ᵐ[actualLaw x]
      numericalError (G := G) S e r Ds main final N hr hF hell hlo hup x P + quadratureError S e r Ds main final N hr hF hell hlo hup x := by
    filter_upwards [numerical_target_sub_reference S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x] with z hz
    change executed (G := G) S e r Ds main final N x z.1.1.1.2 z -
        PrivateCompletedReference.output S e r Ds main final N hr hF hell hlo hup x z = _
    rw [executed_momentum_eq (G := G) S e r Ds main final N x z.1.1.1.2 P z]
    change _ = (executed (G := G) S e r Ds main final N x P z - numericalTarget S e r Ds main final N hr hF hell hlo hup x z) + _
    rw [← hz]
    exact (sub_add_sub_cancel _ _ _).symm
  let hout := (memLp_congr_ae he).2 (hn.add hq)
  refine ⟨hout,?_⟩
  have heLp := MemLp.toLp_congr hout (hn.add hq) he
  rw [heLp,MemLp.toLp_add hn hq]
  exact (norm_add_le _ _).trans (add_le_add hnB hqB)
include hG in
/-- Complete actual private RMS accuracy join. Its quantitative inputs belong
only to standalone LOWER children; initializer, residual, and endpoint quadrature
payments come from original smooth convex data on the unchanged full source. -/
theorem retained_error_bound (hm : 1≤m) (hphysical : r^2*ell≤1/2)
    (x P : Point d) (κ κf : ℝ≥0) (amplitude : ℕ → Fin n → ℝ) (amplitudeF : Fin n → ℝ)
    (hshift : ∀ i, ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (S.radius r (e i)) (main i).shiftVector)
    (hshiftF : ∀ i, ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (S.radius r (e i)) (final i).shiftVector)
    (hstable : ∀ i, FixedTapeStability.ChildStable (main i).program (main i).coefficient G κ)
    (hstableF : ∀ i, FixedTapeStability.ChildStable (final i).program (final i).coefficient G κf)
    (hmeas : ∀ k, k<N → ∀ i, AEStronglyMeasurable (mainDifference (G := G) S e r Ds main final N hr hF hell hlo hup x k i) (actualLaw x))
    (hmeasF : ∀ i, AEStronglyMeasurable (finalDifference (G := G) S e r Ds main final N hr hF hell hlo hup x P i) (actualLaw x))
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
    ∃ hout : MemLp (retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x) 2 (actualLaw x),
      ‖hout.toLp (retainedError (G := G) S e r Ds main final N hr hF hell hlo hup x)‖ ≤
        (r*((κf:ℝ)*mainBudget S e r N hr hF hell hlo hup x κ amplitude) +
          ∑ i, |samplingFinalWeight S e r i| * childPayment S e r hr hF hell hlo hup x i (amplitudeF i)) +
            quadratureBudget S r hr hF hell hlo hup := by
  obtain ⟨hn,hnB⟩ := numerical_error_bound (G := G) (hG := hG) S e r Ds main final N hr hDs hmass hfinalMass L hL
    hF hell hlo hup Jf J hm hphysical x P κ κf amplitude amplitudeF hshift hshiftF hstable hstableF hmeas hmeasF
    hmem hbound hmemF hboundF
  exact retained_error_of_numerical (G := G) S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J
    hm hphysical x P _ hn hnB
end NumericalJoin


end AcceleratedLogConcave.Oracle.PrivateCompletedRms
