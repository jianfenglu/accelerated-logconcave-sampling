import AcceleratedLogConcave.Oracle.MeanCompletedRms
import AcceleratedLogConcave.Oracle.MeanRmsMeasurability
import AcceleratedLogConcave.Oracle.MeanCompletedQuadrature

/-! Full-build source readouts and automatic measurability for the actual
mean RMS join. The executed oracle is arbitrary measurable G and independent
of the original analytic potential. The private, assembly, flow and entire
body coordinates are read from the same original tape. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.MeanSourceBuildRms
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.AffineGraph
open Numerics.MeanCollocationLp FixedTapeStability
open AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open CanonicalTapeLaw CanonicalTapeMeasurability TailOccurrenceCut TailCut
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable {D m n a h : ℕ} (d : MeanFlowLp.Data (Fin D) m)
  (nodes : Fin n ≃ d.G.MeanNode) (anchors : Fin a ≃ d.G.Anchor)
  (seeds : Fin h ≃ Fin m × d.G.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
  (N : ℕ) (Ds δ t w : ℝ) (privateShift : GaussianSlot sampling.program → ℝ)
  (G : Point D → Point D)
  {Ω : Type*} [MeasurableSpace Ω]
  (fullTape : Ω → Tape D (SourceMeanExecutable.program d.G nodes anchors seeds main final sampling N))
  (P V : Ω → Point D)

/-- The same raw assembly occurrences as the literal prefix. -/
def raw (ω : Ω) (i : Fin (m+1)) : Point D := ((fullTape ω).2.2.2.2.1 i).1
/-- Every literal conditional-flow occurrence, including its source label. -/
def flow (ω : Ω) (i : Fin h) : Point D := ((fullTape ω).2.2.2.2.2.2.1 i).1
/-- Actual embedded private execution, with its complete original source slice. -/
def privateValue (ω : Ω) : Point D :=
  SourceMeanBuildRms.privateResult d.G nodes anchors seeds d.r d.sigma Ds δ t w main final sampling N privateShift G d.x (P ω) (fullTape ω)
/-- Full untouched body tail of the source program. -/
def bodyTape (ω : Ω) :=
  SourceMeanBuildRms.actualTape d.G nodes anchors seeds d.r d.sigma Ds δ t w main final sampling N privateShift (fullTape ω)
/-- The actual prefix store, including the executed private return. -/
def cache (ω : Ω) : Env D (SourceMeanExecutionRms.Ready n m h) :=
  SourceMeanBuildRms.actualEnv d.G nodes anchors seeds d.r d.sigma Ds δ t w main final sampling N privateShift G d.x (P ω) (fullTape ω)
/-- Original analytic seed with the retained lower private reference V. -/
def sourceSeed (ω : Ω) : Seed d :=
  MeanCompletedRms.sourceSeed d nodes anchors seeds Ds δ t w main final sampling P V
    (raw d nodes anchors seeds main final sampling N fullTape)
    (flow d nodes anchors seeds main final sampling N fullTape) ω

local notation "seed" => sourceSeed d nodes anchors seeds main final sampling N Ds δ t w fullTape P V
local notation "bodyT" => bodyTape d nodes anchors seeds main final sampling N Ds δ t w privateShift fullTape
local notation "cacheT" => cache d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape P
local notation "Phi" => (fun i ω => rawReference d (nodes i) (seed ω))
local notation "reply" => (fun i ω => Gibbs.primitiveMean d.F (Phi i ω) (d.G.radius d.r (nodes i)))
local notation "Amat" => (fun i j => d.G.matrix d.r d.sigma (nodes i) (nodes j))
local notation "rho" => RecursiveMeanPublicTable.centerNoise d.r d.G.R Ds
local notation "Cmat" => CovarianceSetup.residualRoot Amat rho (rowBound (m := m) d.r d.sigma δ t w)
local notation "childWidth" => CovarianceSetup.sigma n rho (rowBound (m := m) d.r d.sigma δ t w)
local notation "nu0" => (fun i ω => rho • (show Point D from ((bodyT ω).1 i).1))
variable (Gref : ℕ → Fin n → Ω → Point D)
local notation "noise" => SourceMeanExecutionRms.noise d.G nodes main final sampling N bodyT
local notation "Pmain" => SourceMeanRetainedRms.finiteReference N Gref
local notation "Y" => SharedLayerRms.benchmark Phi Amat Cmat childWidth Pmain noise nu0

omit [MeasurableSpace Ω] in
theorem bodyTape_eq (ω : Ω) : bodyT ω=
    MeanChronologicalExecution.bodyTape d.G nodes anchors seeds main final sampling N (fullTape ω) := rfl

variable (L : PrimitiveLaws D) (hG : Measurable G) (htape : Measurable fullTape)
  (hP : Measurable P) (hV : Measurable V)

include htape in
theorem raw_measurable (i : Fin (m+1)) :
    Measurable (fun ω => raw d nodes anchors seeds main final sampling N fullTape ω i) :=
  ((measurable_pi_apply i).comp htape.snd.snd.snd.snd.fst).fst
include htape in
theorem flow_measurable (i : Fin h) :
    Measurable (fun ω => flow d nodes anchors seeds main final sampling N fullTape ω i) :=
  ((measurable_pi_apply i).comp htape.snd.snd.snd.snd.snd.snd.fst).fst

include htape hP hV in
theorem sourceSeed_measurable : Measurable seed := by
  have hr (i : Fin (m+1)) := raw_measurable d nodes anchors seeds main final sampling N fullTape htape i
  have hz (i : Fin h) := flow_measurable d nodes anchors seeds main final sampling N fullTape htape i
  have ha : Measurable (fun ω => SourceMeanShift.splitValues d.G nodes anchors d.r d.sigma Ds δ t w main final sampling (P ω)
      (raw d nodes anchors seeds main final sampling N fullTape ω) 0) := by
    unfold SourceMeanShift.splitValues MeanExecutablePrefix.assemblyValues
    exact (hP.const_smul (_ : ℝ)).add (Finset.measurable_sum Finset.univ fun j _ => (hr j).const_smul (_ : ℝ))
  have hphase := ((WithLp.prod_continuous_toLp 2 (Point D) (Point D)).measurable.comp
    ((hV.const_smul (backwardEnd d.G.R)).prodMk ha))
  exact hphase.prodMk (Measurable.of_eval fun j => Measurable.of_eval fun k => hz (seeds.symm (j,k)))

include htape hP hV in
theorem reference_measurable (i : Fin n) : Measurable (Phi i) := by
  have hs := sourceSeed_measurable d nodes anchors seeds main final sampling N Ds δ t w fullTape P V htape hP hV
  have hphase : Measurable (fun ω => (d.x,((seed ω).1.ofLp,(seed ω).2))) :=
    measurable_const.prodMk (((WithLp.prod_continuous_ofLp 2 (Point D) (Point D)).measurable.comp hs.fst).prodMk hs.snd)
  have h := (MeanJointReference.continuous_reference d.G d.hF d.hell d.hlo d.hup d.r d.sigma d.hr d.hsigma d.hsmall (nodes i)).measurable.comp hphase
  convert h using 1
  funext ω
  rfl

variable (hDs : 0<Ds) (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
include L htape in
theorem initial_noise_measurable (i : Fin n) : Measurable (nu0 i) := by
  have hb := (measurePreserving_split L (MeanMainBatchCoupling.bodyCut d.G nodes anchors seeds main final sampling N)).measurable.snd.comp htape
  have hn : Measurable (fun ω => (show Point D from ((MeanChronologicalExecution.bodyTape d.G nodes anchors seeds main final sampling N (fullTape ω)).1 i).1)) :=
    ((measurable_pi_apply i).comp hb.fst).fst
  exact hn.const_smul rho

include L htape hDs hmass in
theorem residual_noise_measurable (k : ℕ) (hk : k<N) (i : Fin n) : Measurable (noise k i) := by
  have h := (MeanChronologicalBenchmark.residualNoise_measurable d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass L k hk i).comp htape
  exact h

variable (hGref : ∀ k i,Measurable (Gref k i))
include L htape hP hV hDs hmass hGref in
theorem benchmark_measurable (k : ℕ) (hk : k≤N) (i : Fin n) : Measurable (Y k i) := by
  have hphi := reference_measurable d nodes anchors seeds main final sampling N Ds δ t w fullTape P V htape hP hV i
  cases k with
  | zero => exact hphi.add (initial_noise_measurable d nodes anchors seeds main final sampling N Ds δ t w privateShift fullTape L htape i)
  | succ k =>
    have hp (j : Fin n) : Measurable (Pmain k j) := by
      convert hGref k j using 1
      funext ω
      exact ite_eq_left (show k<N by omega)
    exact (hphi.add (Finset.measurable_sum Finset.univ fun j _ => (hp j).const_smul childWidth |>.const_smul (Amat i j))).add
      (Finset.measurable_sum Finset.univ fun j _ =>
        (residual_noise_measurable d nodes anchors seeds main final sampling N Ds δ t w privateShift fullTape L htape hDs hmass k (by omega) j).const_smul (Cmat i j))

local notation "eval" => SourceMeanExecutionRms.evaluator d.G nodes d.r Ds main final sampling N G bodyT reply
local notation "initial" => (fun i ω => SourceMeanExecutionRms.initial d.G nodes d.r Ds main final sampling N (cacheT ω) (bodyT ω) i)
local notation "direct" => (fun i ω => storedPoint (cacheT ω) (MeanExecutablePrefix.direct i))
local notation "X" => SharedLayerRms.iterate direct Amat Cmat eval noise initial
local notation "childErr" => SharedLayerRms.childError eval Y reply childWidth Pmain
local notation "XE" => (fun i ω =>
  let st := SourceMeanExecutionRms.state d.G nodes anchors d.r d.sigma Ds δ t w main final sampling N G d.x (P ω) (cacheT ω) (bodyT ω)
  storedPoint st.env (st.old i))
local notation "FE" => (fun i ω => SourceMeanExecutionRms.finalEvaluator d.G nodes anchors d.r d.sigma Ds δ t w main final sampling N G d.x (P ω) (cacheT ω) (bodyT ω) i)
local notation "active" => (fun i => nodes.symm (.center d.G i))
local notation "width" => RecursiveMeanPublicTable.finalWidth d.G.R d.sigma
local notation "wf" => Numerics.GaussLegendre.weight m
local notation "Uprivate" => privateValue d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape P

include L hG htape hP hV hDs hmass hGref in
/-- The actual main callback difference is measurable without an analytic
measurability condition on the separately specified potential. -/
theorem main_difference_measurable (k : ℕ) (hk : k<N) (i : Fin n) :
    Measurable (fun ω => eval k i ω (X k i ω)-eval k i ω (Y k i ω)) := by
  exact MeanRmsMeasurability.main_difference_measurable d.G nodes anchors seeds main final sampling N
    d.r d.sigma Ds δ t w d.hr hDs hmass L G hG fullTape htape privateShift
    (fun _ => d.x) P measurable_const hP reply k hk i (Y k i)
    (benchmark_measurable d nodes anchors seeds main final sampling N Ds δ t w privateShift fullTape P V Gref
      L htape hP hV hDs hmass hGref k hk.le i)

include L hG htape hP hV hDs hmass hGref in
/-- The actual final callback difference retains its full lower tape and
original designated input at both measurable candidate centers. -/
theorem final_difference_measurable (i : Fin m) :
    Measurable (fun ω => FE i ω (XE (active i) ω)-FE i ω (Y N (active i) ω)) := by
  exact MeanRmsMeasurability.final_difference_measurable d.G nodes anchors seeds main final sampling N
    d.r d.sigma Ds δ t w d.hr hDs hmass L G hG fullTape htape privateShift
    (fun _ => d.x) P measurable_const hP i (Y N (active i))
    (benchmark_measurable d nodes anchors seeds main final sampling N Ds δ t w privateShift fullTape P V Gref
      L htape hP hV hDs hmass hGref N le_rfl (active i))

/-- Literal complete source execution on the original tape. -/
def output (ω : Ω) : Point D := RetainedMeanFinalBatch.childPoint (run
  (SourceMeanExecutable.build d.G nodes anchors seeds d.r d.sigma Ds δ t w main final sampling N privateShift).program G
  ⟨SourceMeanExecutable.table d.G nodes anchors d.r d.sigma Ds δ t w main final sampling,d.x,P ω⟩ Env.empty (fullTape ω))

/-- The explicit physical reference including the actual retained final
child outputs. This readout has the same units as the executed program. -/
def referenceReadout (Pref : Fin m → Ω → Point D) : Ω → Point D :=
  MeanCompletedRms.referenceReadout d nodes anchors seeds Ds δ t w main final sampling P Uprivate V
    (raw d nodes anchors seeds main final sampling N fullTape)
    (flow d nodes anchors seeds main final sampling N fullTape) Pref

variable (μ : Measure Ω)
  (Pref : Fin m → Ω → Point D)
include L hG htape hP hV hDs hmass hGref in
/-- Full literal-source RMS bound with automatic callback measurability and
original-data initializer, residual and quadrature payments. The remaining
error inputs are exclusively lower private and child errors. -/
theorem output_error_bound
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (h₀ : ℝ) (hmesh : MeshConditions d h₀) (hhalf : contraction d h₀≤1/2)
    (hpsi : d.G.psi≤d.G.R^4) (κ κf : ℝ≥0) (aRow : ℝ) (ha : 0≤aRow)
    (Eprivate : ℝ) (hanchor : MemLp (MeanCompletedRms.anchorError d Uprivate V) 2 μ)
    (hanchorBound : ‖hanchor.toLp _‖≤Eprivate)
    (ε : ℕ → Fin n → ℝ) (hrow : ∀ i,∑ j,|Amat i j|≤aRow)
    (hstable : ∀ i,ChildStable (main i).program (main i).coefficient G κ)
    (hchild : ∀ k,k<N → ∀ i,MemLp (childErr k i) 2 μ)
    (hchildBound : ∀ k (hk : k<N) i,‖(hchild k hk i).toLp _‖≤ε k i)
    (εf : Fin m → ℝ)
    (hfinalStable : ∀ i,ChildStable (final i).program (final i).coefficient G κf)
    (hfinalChild : ∀ i,MemLp (fun ω => FE i ω (Y N (active i) ω)-width • Pref i ω-reply (active i) ω) 2 μ)
    (hfinalBound : ∀ i,‖(hfinalChild i).toLp _‖≤εf i) :
    ∃ hout : MemLp (fun ω => output d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape P ω-
      referenceReadout d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape P V Pref ω) 2 μ,
      ‖hout.toLp _‖≤(∑ i,|wf i|)*((κf:ℝ)*MeanCompletedRms.sourceMainBudget d nodes h₀ N κ aRow Eprivate ε)+
        ∑ i,|wf i| *εf i+MeanOriginalBounds.quadratureBudget d := by
  have hb := MeanCompletedRms.source_output_error_bound d nodes anchors seeds Ds δ t w main final sampling μ P Uprivate V
    (raw d nodes anchors seeds main final sampling N fullTape)
    (flow d nodes anchors seeds main final sampling N fullTape) N G bodyT Gref Pref hp
    h₀ hmesh hhalf hpsi κ κf aRow ha Eprivate hanchor hanchorBound ε hrow hstable
    (fun k hk i => (main_difference_measurable d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape P V Gref
      L hG htape hP hV hDs hmass hGref k hk i).aestronglyMeasurable)
    hchild hchildBound εf hfinalStable
    (fun i => (final_difference_measurable d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape P V Gref
      L hG htape hP hV hDs hmass hGref i).aestronglyMeasurable)
    hfinalChild hfinalBound
  have he : (fun ω => output d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape P ω-
      referenceReadout d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape P V Pref ω)=
    (fun ω => RetainedMeanFinalBatch.childPoint (run
      (SourceMeanExecutable.body (a := a) (h := h) d.G nodes main final sampling N) G
      ⟨SourceMeanExecutable.table d.G nodes anchors d.r d.sigma Ds δ t w main final sampling,d.x,P ω⟩ (cacheT ω) (bodyT ω))-
      referenceReadout d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape P V Pref ω) := by
    funext ω
    exact congrArg (fun z => z-referenceReadout d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape P V Pref ω)
      (SourceMeanBuildRms.build_value d.G nodes anchors seeds d.r d.sigma Ds δ t w main final sampling N privateShift G d.x (P ω) (fullTape ω))
  rw [he]
  exact hb

end AcceleratedLogConcave.Oracle.MeanSourceBuildRms
