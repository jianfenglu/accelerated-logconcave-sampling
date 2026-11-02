import AcceleratedLogConcave.Oracle.MeanSourceBuildRms
import AcceleratedLogConcave.Oracle.MeanSourceSharpRms

/-! Literal full-build RMS guarantee with the intrinsic original initializer.
All source readouts and measurability are reused unchanged from the actual
full-build adapter; the sharper proved payment retains physical scaling. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.MeanSourceSharpBuildRms
open MeanSourceBuildRms
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

variable (hDs : 0<Ds) (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
variable (hGref : ∀ k i,Measurable (Gref k i))
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

variable (μ : Measure Ω)
  (Pref : Fin m → Ω → Point D)
include L hG htape hP hV hDs hmass hGref in
/-- Full literal-source RMS bound with automatic callback measurability and
original-data initializer, residual and quadrature payments. The remaining
error inputs are exclusively lower private and child errors. -/
theorem output_error_bound
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (h₀ : ℝ) (hmesh : MeshConditions d h₀)
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
      ‖hout.toLp _‖≤(∑ i,|wf i|)*((κf:ℝ)*MeanSourceSharpRms.sourceMainBudget d nodes h₀ N κ aRow Eprivate ε)+
        ∑ i,|wf i| *εf i+MeanOriginalBounds.quadratureBudget d := by
  have hb := MeanSourceSharpRms.source_output_error_bound d nodes anchors seeds Ds δ t w main final sampling μ P Uprivate V
    (raw d nodes anchors seeds main final sampling N fullTape)
    (flow d nodes anchors seeds main final sampling N fullTape) N G bodyT Gref Pref hp
    h₀ hmesh hpsi κ κf aRow ha Eprivate hanchor hanchorBound ε hrow hstable
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

end AcceleratedLogConcave.Oracle.MeanSourceSharpBuildRms
