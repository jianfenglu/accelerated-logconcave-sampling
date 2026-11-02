import AcceleratedLogConcave.Oracle.MeanSourceSharpBuildRms
import AcceleratedLogConcave.Oracle.MeanCompletedChildAccuracy
import AcceleratedLogConcave.Oracle.MeanCompletedFinalAccuracy

/-! Literal full-source readout alignment on the constructed completed mean
coupling. The numerical source seed and every lower callback use the same
retained tape, original inputs and returned child references. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.MeanCompletedSourceRms
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.MeanCollocationLp
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer MeanChronologicalCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable {D m n a h : ℕ} (d : MeanFlowLp.Data (Fin D) m)
  (nodes : Fin n ≃ d.G.MeanNode) (anchors : Fin a ≃ d.G.Anchor)
  (seeds : Fin h ≃ Fin m × d.G.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
  (N : ℕ) (Ds δ t w : ℝ) (hDs : 0<Ds)
  (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  {A : Type*} [MeasurableSpace A]
  (x P V : A → Point D) (hx : Measurable x) (hP : Measurable P) (hV : Measurable V)
  (L : PrimitiveLaws D) (hL : L.pointDraw=stdGaussian (Point D))
local instance seedMeasurableEq : MeasurableEq (Seed d) where
  measurableSet_diagonal := by
    have hf : MeasurableSet {z : Seed d × Seed d | z.1.1=z.2.1} :=
      measurableSet_eq_fun measurable_fst.fst measurable_snd.fst
    have hs : MeasurableSet {z : Seed d × Seed d | z.1.2=z.2.2} :=
      measurableSet_eq_fun measurable_fst.snd measurable_snd.snd
    have he : Set.diagonal (Seed d)={z : Seed d × Seed d | z.1.1=z.2.1} ∩ {z : Seed d × Seed d | z.1.2=z.2.2} := by
      ext z
      exact Prod.ext_iff
    rw [he]
    exact hf.inter hs
local notation "position" => (fun a => backwardEnd d.G.R • V a)
local notation "hposition" => hV.const_smul (backwardEnd d.G.R)
local notation "C" => Coarse (d := D) d.G nodes anchors seeds main final sampling N A
local notation "Xmain" => History (d := D) d.G nodes anchors seeds main final sampling N A ×
  Tape D (Host d.G nodes anchors seeds main final sampling N)
local notation "Sample" => Xmain × (Fin m → Point D)
local notation "staticSeed" => MeanChronologicalFinalObservation.benchmarkSeed d.G nodes anchors seeds main final sampling N d.r d.hr x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall d.x

/-- Original full tape retained by the completed kernel. -/
def sourceTape (z : Sample) : Tape D (Host d.G nodes anchors seeds main final sampling N) := z.1.2
/-- The original parent momentum, not a regenerated input. -/
def sourceP (z : Sample) : Point D := P z.1.1.1.1
/-- The lower private reference before its literal backward-end scaling. -/
def sourceV (z : Sample) : Point D := V z.1.1.1.1
/-- Returned main-child references in chronological order. -/
def mainReference (k : ℕ) (i : Fin n) (z : Sample) : Point D :=
  MeanChronologicalBenchmark.returnedReference d.G nodes anchors seeds main final sampling N k i z.1
/-- Returned designated-final references. -/
def finalReference (i : Fin m) (z : Sample) : Point D := z.2 i
local notation "fullTape" => sourceTape d nodes anchors seeds main final sampling N
local notation "Psource" => sourceP d nodes anchors seeds main final sampling N P
local notation "Vsource" => sourceV d nodes anchors seeds main final sampling N V
local notation "Gref" => mainReference d nodes anchors seeds main final sampling N
local notation "Pref" => finalReference d nodes anchors seeds main final sampling N
local notation "actualSeed" => MeanSourceBuildRms.sourceSeed d nodes anchors seeds main final sampling N Ds δ t w fullTape Psource Vsource
local notation "Phi" => (fun i z => rawReference d (nodes i) (actualSeed z))
local notation "staticPhi" => (fun i c => rawReference d (nodes i) (staticSeed c))

omit [MeasurableSpace A] in
/-- The original analytic seed is read from precisely the actual source
prefix and raw private reference; no probabilistic assertion is used here. -/
theorem initial_seed_eq (z : A × Tape D (Host d.G nodes anchors seeds main final sampling N)) :
    staticSeed (MeanChronologicalSupport.initialView d.G nodes anchors seeds main final sampling N z).1 =
      MeanSourceBuildRms.sourceSeed d nodes anchors seeds main final sampling N Ds δ t w
        Prod.snd (P ∘ Prod.fst) (V ∘ Prod.fst) z := by
  dsimp only [MeanChronologicalFinalObservation.benchmarkSeed,MeanJointReference.seed,
    MeanChronologicalHost.phaseInput,MeanChronologicalSupport.initialView,
    MeanSourceBuildRms.sourceSeed,MeanCompletedRms.sourceSeed]
  congr 2
  apply Prod.ext
  · rfl
  · exact (MeanAssemblyJointLaw.literal_assembly_values (a := a) d.G nodes anchors main final sampling
    d.r d.sigma Ds δ t w (P z.1)
    (MeanSourceBuildRms.raw d nodes anchors seeds main final sampling N Prod.snd z) 0).symm

local notation "Amat" => (fun i j => d.G.matrix d.r d.sigma (nodes i) (nodes j))
local notation "rho" => RecursiveMeanPublicTable.centerNoise d.r d.G.R Ds
local notation "Cmat" => CovarianceSetup.residualRoot Amat rho (rowBound (m := m) d.r d.sigma δ t w)
local notation "childWidth" => CovarianceSetup.sigma n rho (rowBound (m := m) d.r d.sigma δ t w)
local notation "bodyT" => MeanChronologicalExecution.bodyTape d.G nodes anchors seeds main final sampling N ∘ fullTape
local notation "reply" => (fun i z => Gibbs.primitiveMean d.F (Phi i z) (d.G.radius d.r (nodes i)))
local notation "noise" => SourceMeanExecutionRms.noise d.G nodes main final sampling N bodyT
local notation "Pmain" => SourceMeanRetainedRms.finiteReference N Gref
local notation "nu0" => (fun i z => rho • (show Point D from ((bodyT z).1 i).1))

/-- The actual finite numerical benchmark, with returned main references and
its main-child width, distinct from the parent output width. -/
def benchmark : ℕ → Fin n → Sample → Point D :=
  SharedLayerRms.benchmark Phi Amat Cmat childWidth Pmain noise nu0
local notation "Y" => benchmark d nodes anchors seeds main final sampling N Ds δ t w P V

include hDs in
omit [MeasurableSpace A] in
/-- Literal source benchmark equals its reconstructed comparison for every
bounded stage, before taking any law or accuracy statement. -/
theorem benchmark_eq_comparison (k : ℕ) (hk : k≤N) (i : Fin n) (z : Sample) :
    Y k i z = Phi i z + rho • MeanChronologicalBenchmark.comparisonNoise d.G nodes anchors seeds main final sampling N
      d.r Ds d.sigma δ t w k hk z.1 i := by
  let phi : Fin n → Xmain → Point D := fun i z =>
    rawReference d (nodes i) (MeanSourceBuildRms.sourceSeed d nodes anchors seeds main final sampling N Ds δ t w
      Prod.snd (fun z : Xmain => P z.1.1.1) (fun z : Xmain => V z.1.1.1) z)
  have hp : SourceMeanRetainedRms.finiteReference N
      (MeanChronologicalBenchmark.returnedReference (d := D) (A := A) d.G nodes anchors seeds main final sampling N)=
      MeanChronologicalBenchmark.returnedReference d.G nodes anchors seeds main final sampling N := by
    funext j l y
    unfold SourceMeanRetainedRms.finiteReference MeanChronologicalBenchmark.returnedReference
    split_ifs <;> rfl
  have hb := MeanChronologicalBenchmark.benchmark_eq_comparisonNoise d.G nodes anchors seeds main final sampling N
    d.r Ds d.sigma δ t w d.hr hDs k hk phi z.1 i
  rw [←hp] at hb
  convert hb using 1
  all_goals cases k <;> rfl

private theorem residual_value {c d : ℕ} {Γ : Ctx} (o : Origin)
    (G : Point d → Point d) (input : Inputs d c) (env : Env d Γ)
    (ω : Tape d (residualDraw (c := c) (Γ := Γ) o)) :
    (run (residualDraw o) G input env ω).value=ω.1 := rfl

omit [MeasurableSpace A] in
/-- The reached body store is exactly the full-build cache, including the
executed private return and every literal assembly/flow/direct row. -/
theorem source_env_eq (privateShift : GaussianSlot sampling.program → ℝ)
    (G : Point D → Point D) (p : Point D)
    (ω : Tape D (Host d.G nodes anchors seeds main final sampling N)) :
    @Eq (Env D (SourceMeanExecutionRms.Ready n m h))
      (fun {_τ} ref => envAt G ⟨table d.G nodes anchors d.r d.sigma Ds δ t w main final sampling,d.x,p⟩
        (MeanMainBatchCoupling.bodyCut d.G nodes anchors seeds main final sampling N) Env.empty
        (split (MeanMainBatchCoupling.bodyCut d.G nodes anchors seeds main final sampling N) ω).1 ref)
      (fun {_τ} ref => SourceMeanBuildRms.actualEnv d.G nodes anchors seeds d.r d.sigma Ds δ t w main final sampling N privateShift G d.x p ω ref) := by
  have hs : table d.G nodes anchors d.r d.sigma Ds δ t w main final sampling
      (prefixSlot (a := a) main final sampling PrefixPublicTable.scaleSlot)=backwardEnd d.G.R := by
    erw [table_prefix,PrefixPublicTable.table_scale]
  dsimp only [MeanMainBatchCoupling.bodyCut,id,envAt,split,SourceMeanBuildRms.actualEnv]
  simp only [evalInstr,residual_value,Fin.eq_zero,MeanExecutablePrefix.run_scaleRow]
  simp only [pointResult]
  simp only [MeanExecutablePrefix.run_assemblyRow]
  simp only [pointResult,hs,prepend_shiftMany,storedPoint,Env.cons_here]
  unfold SourceMeanShift.cache
  let input : Inputs D (size (a := a) main final sampling) := ⟨table d.G nodes anchors d.r d.sigma Ds δ t w main final sampling,d.x,p⟩
  let U := SourceMeanBuildRms.privateResult d.G nodes anchors seeds d.r d.sigma Ds δ t w main final sampling N privateShift G d.x p ω
  let phaseY := backwardEnd d.G.R • U
  let raw : Fin (m+1) → Point D := fun i => (ω.2.2.2.2.1 i).1
  let Avals := SourceMeanShift.splitValues d.G nodes anchors d.r d.sigma Ds δ t w main final sampling p raw
  let Z : Fin h → Point D := fun i => (ω.2.2.2.2.2.2.1 i).1
  let e : Env D (MeanExecutablePrefix.seedCtx (m+1) h [.point,.point]) :=
    Env.prepend Z (Env.prepend Avals (Env.prepend raw
      (Env.prepend (fun _ : Fin 1 => phaseY) (Env.prepend (fun _ : Fin 1 => U) (SourceMeanShift.inputEnv d.x p)))))
  let slots := prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.directSlot
  have hd (i : Fin n) : (run (PrefixDirect.row slots (MeanExecutablePrefix.savedSeed (.there .here))
      (MeanExecutablePrefix.anchorRef d.G anchors seeds) i) G input e (ω.2.2.2.2.2.2.2.1 i)).value=
      d.G.direct d.r d.sigma d.x phaseY (Avals 0) (fun j k => Z (seeds.symm (j,k))) (nodes i) := by
    rw [run_affineRow_ofFn]
    have hx := MeanExecutablePrefix.stored_savedSeed (SourceMeanShift.inputEnv d.x p) U phaseY raw Avals Z (.there .here)
    have ha (k : Fin a) : storedPoint e (MeanExecutablePrefix.anchorRef d.G anchors seeds k)=
        MeanExecutablePrefix.anchorValues d.G anchors seeds phaseY (Avals 0) Z k :=
      MeanExecutablePrefix.stored_anchorRef d.G anchors seeds (SourceMeanShift.inputEnv d.x p) U phaseY raw Avals Z k
    change storedPoint e (MeanExecutablePrefix.savedSeed (.there .here))+
      ∑ k,input.coefficient (slots (PrefixDirect.slot i k)) • storedPoint e (MeanExecutablePrefix.anchorRef d.G anchors seeds k)=_
    change storedPoint e (MeanExecutablePrefix.savedSeed (.there .here))=d.x at hx
    simp only [hx,ha]
    exact MeanExecutablePrefix.directValues_eq_source d.G nodes anchors seeds d.r d.sigma slots input
      (SourceMeanShift.direct_table d.G nodes anchors d.r d.sigma Ds δ t w main final sampling) d.x phaseY (Avals 0) Z i
  change @Eq (Env D (SourceMeanExecutionRms.Ready n m h))
    (fun {_τ} ref => Env.prepend (fun i => (run (PrefixDirect.row slots (MeanExecutablePrefix.savedSeed (.there .here))
      (MeanExecutablePrefix.anchorRef d.G anchors seeds) i) G input e (ω.2.2.2.2.2.2.2.1 i)).value) e ref)
    (fun {_τ} ref => Env.prepend (fun i => d.G.direct d.r d.sigma d.x phaseY (Avals 0) (fun j k => Z (seeds.symm (j,k))) (nodes i)) e ref)
  simp only [hd]

variable (J : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (MeanChronologicalCoupling.data d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass
    (stage d.G nodes anchors seeds main final sampling N k hk.le).1
    (stage_positive d.G nodes anchors seeds main final sampling N k hk)))
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
  (G : Point D → Point D) (hG : Measurable G)
  (Jfinal : DesignatedChildBatchCoupling.Lower L
    (MeanFinalBatchCoupling.data d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hfinalMass))
  (ρ : Measure (A × Tape D (Host d.G nodes anchors seeds main final sampling N)))
local notation "loopKernel" => MeanChronologicalCoupling.kernel d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass L hL x P position hx hP hposition d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w J
local notation "loopLaw" => loopKernel ∘ₘ ρ
local notation "finishKernel" => MeanCompletedCoupling.finishKernel d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs L hL x P position hx hP hposition d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G hG Jfinal
local notation "completedKernel" => MeanCompletedCoupling.kernel d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass L hL x P position hx hP hposition d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G hG J Jfinal
local notation "completedLaw" => completedKernel ∘ₘ ρ

/-- The actual lower main callback error on the complete source sample. -/
def mainError (k : ℕ) (i : Fin n) (z : Sample) : Point D :=
  SourceMeanExecutionRms.evaluator d.G nodes d.r Ds main final sampling N G bodyT reply k i z (Y k i z)-
    reply i z-childWidth • Gref k i z

include hP hV in
/-- The static benchmark phase is the analytic seed on the SAME retained
full original tape, first on the actual finite chronological kernel. -/
theorem loop_seed_ae :
    ∀ᵐ z ∂loopLaw, staticSeed z.1.1 =
      MeanSourceBuildRms.sourceSeed d nodes anchors seeds main final sampling N Ds δ t w
        Prod.snd (fun z : Xmain => P z.1.1.1) (fun z : Xmain => V z.1.1.1) z := by
  exact MeanChronologicalSupport.kernel_readout_ae d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass L hL
    x P position hx hP hposition d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w J
    staticSeed (MeanChronologicalFinalObservation.benchmarkSeed_measurable d.G nodes anchors seeds main final sampling N d.r d.hr x P position
      hx hP hposition d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall d.x)
    (MeanSourceBuildRms.sourceSeed d nodes anchors seeds main final sampling N Ds δ t w Prod.snd (P ∘ Prod.fst) (V ∘ Prod.fst))
    (MeanSourceBuildRms.sourceSeed_measurable d nodes anchors seeds main final sampling N Ds δ t w Prod.snd (P ∘ Prod.fst) (V ∘ Prod.fst)
      measurable_snd (hP.comp measurable_fst) (hV.comp measurable_fst))
    (initial_seed_eq d nodes anchors seeds main final sampling N Ds δ t w x P V) ρ

include hP hV hG in
/-- The final retained augmentation preserves the whole original chronology. -/
theorem chronology_preserving : MeasurePreserving (Prod.fst : Sample → Xmain) completedLaw loopLaw := by
  refine ⟨measurable_fst,?_⟩
  rw [MeanCompletedCoupling.kernel,←Measure.comp_assoc,Measure.map_comp _ _ measurable_fst,←Kernel.fst_eq,
    MeanCompletedCoupling.finishKernel_original,Measure.id_comp]

include hP hV hG in
/-- Appending the literal final batch preserves the entire chronological
sample, hence also the actual analytic seed support. -/
theorem kernel_seed_ae : ∀ᵐ z ∂completedLaw, staticSeed z.1.1.1=actualSeed z := by
  have hp : MeasurePreserving (Prod.fst : Sample → Xmain) completedLaw loopLaw := by
    refine ⟨measurable_fst,?_⟩
    rw [MeanCompletedCoupling.kernel,←Measure.comp_assoc,Measure.map_comp _ _ measurable_fst,←Kernel.fst_eq,
      MeanCompletedCoupling.finishKernel_original,Measure.id_comp]
  exact hp.quasiMeasurePreserving.ae
    (loop_seed_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J ρ)

include hP hV hG in
/-- The completed coupling preserves the complete incoming augmented source. -/
theorem source_preserving : MeasurePreserving
    (MeanCompletedCoupling.original d.G nodes anchors seeds main final sampling N) completedLaw ρ := by
  refine ⟨MeanCompletedCoupling.original_measurable d.G nodes anchors seeds main final sampling N,?_⟩
  rw [Measure.map_comp _ _ (MeanCompletedCoupling.original_measurable d.G nodes anchors seeds main final sampling N),
    MeanCompletedCoupling.kernel_original,Measure.id_comp]

variable (hbaseρ : ∀ᵐ z ∂ρ,x z.1=d.x)

include hP hV hG hbaseρ in
/-- The original center support is retained by the completed full-source kernel. -/
theorem kernel_center_ae : ∀ᵐ z ∂completedLaw,x z.1.1.1.1=d.x :=
  (source_preserving d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ).quasiMeasurePreserving.ae hbaseρ

include hP hV hG hDs hbaseρ in
/-- The source benchmark and static original phase agree on the actual
completed coupling, at every node. -/
theorem kernel_reference_ae : ∀ᵐ z ∂completedLaw, ∀ i,
    Phi i z=MeanChronologicalHost.center d.G nodes anchors seeds main final sampling N x P position
      d.hF d.hell d.hlo d.hup d.r d.sigma d.hr d.hsigma d.hsmall i z.1.1.1 := by
  filter_upwards [kernel_seed_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ,
    kernel_center_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ hbaseρ] with z hz hc
  intro i
  rw [←hz]
  exact (MeanCompletedChildAccuracy.center_eq_rawReference d.G nodes anchors seeds main final sampling N d.r d.hr
    x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall d.x z.1.1.1 hc i).symm

include hP hV hG hDs hbaseρ in
/-- The actual full-source main error is the concrete completed chronology's
lower error. Only the benchmark support is almost everywhere; the executed
callback uses exactly the same transformed full child seed. -/
theorem kernel_mainError_ae (k : ℕ) (hk : k<N) (i : Fin n) :
    mainError d nodes anchors seeds main final sampling N Ds δ t w P V G k i =ᵐ[completedLaw]
      (MeanMainErrorTransport.stageError d.G nodes anchors seeds main final sampling N d.r Ds d.hr
        x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w G k hk i) ∘ Prod.fst := by
  filter_upwards [kernel_reference_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ hbaseρ] with z hz
  unfold mainError
  rw [benchmark_eq_comparison d nodes anchors seeds main final sampling N Ds δ t w hDs P V k hk.le i z]
  dsimp only
  rw [hz i]
  unfold MeanMainErrorTransport.stageError
  have he : SourceMeanExecutionRms.evaluator d.G nodes d.r Ds main final sampling N G bodyT reply k i z
      ((MeanChronologicalHost.center d.G nodes anchors seeds main final sampling N x P position
        d.hF d.hell d.hlo d.hup d.r d.sigma d.hr d.hsigma d.hsmall i z.1.1.1)+
        rho • MeanChronologicalBenchmark.comparisonNoise d.G nodes anchors seeds main final sampling N d.r Ds d.sigma δ t w k hk.le z.1 i)=
    SourceMeanExecutionRms.evaluator d.G nodes d.r Ds main final sampling N G
      (MeanChronologicalExecution.bodyTape d.G nodes anchors seeds main final sampling N) (fun _ _ => 0) k i z.1.2
      ((MeanChronologicalHost.center d.G nodes anchors seeds main final sampling N x P position
        d.hF d.hell d.hlo d.hup d.r d.sigma d.hr d.hsigma d.hsmall i z.1.1.1)+
        rho • MeanChronologicalBenchmark.comparisonNoise d.G nodes anchors seeds main final sampling N d.r Ds d.sigma δ t w k hk.le z.1 i) := by
    have h₁ := MeanCompletedMainReadout.evaluator_eq_run d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass k hk G
      (fun j _ => reply j z) i z.1.2
    have h₂ := MeanCompletedMainReadout.evaluator_eq_run d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass k hk G
      (fun _ _ => 0) i z.1.2
    exact (h₁ _).trans (h₂ _).symm
  rw [he]
  rfl

include hP hV hG in
/-- The actual recorded final comparison remains the finite benchmark
comparison after the final child augmentation. -/
theorem kernel_comparison_ae : ∀ᵐ z ∂completedLaw,
    z.1.1.2.2=MeanChronologicalBenchmark.comparisonNoise d.G nodes anchors seeds main final sampling N
      d.r Ds d.sigma δ t w N le_rfl z.1 := by
  exact (chronology_preserving d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ).quasiMeasurePreserving.ae
    (MeanChronologicalBenchmark.kernel_comparisonNoise_ae d.G nodes anchors seeds main final sampling N d.r Ds d.sigma δ t w d.hr hDs hmass L hL
      x P position hx hP hposition d.hF d.hell d.hlo d.hup d.hsigma d.hsmall J ρ)

variable (privateShift : GaussianSlot sampling.program → ℝ)
local notation "cacheT" => MeanSourceBuildRms.cache d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource
local notation "FE" => (fun i z => SourceMeanExecutionRms.finalEvaluator d.G nodes anchors d.r d.sigma Ds δ t w main final sampling N G d.x (Psource z) (cacheT z) (bodyT z) i)
local notation "width" => RecursiveMeanPublicTable.finalWidth d.G.R d.sigma
local notation "active" => (fun i => nodes.symm (.center d.G i))

omit [MeasurableSpace A] in
/-- The canonical source callback is the full-build callback at every
candidate, with the same original Pi and complete final lower tape. -/
theorem sourceFinalEvaluator_eq (z : Sample) (i : Fin m) (y : Point D) :
    MeanFinalSourceEvaluator.sourceFinalEvaluator d.G nodes anchors seeds main final sampling N d.r Ds G
      ⟨table d.G nodes anchors d.r d.sigma Ds δ t w main final sampling,d.x,Psource z⟩ (fullTape z) i y = FE i z y := by
  have hf := MeanFinalSourceEvaluator.sourceFinalEvaluator_eq_finalEvaluator d.G nodes anchors seeds main final sampling N
    d.r d.sigma Ds δ t w G d.x (Psource z) (fullTape z) i y
  rw [source_env_eq d nodes anchors seeds main final sampling N Ds δ t w privateShift G (Psource z) (fullTape z)] at hf
  exact hf

/-- The actual final source callback error, using its returned final reference. -/
def finalError (i : Fin m) (z : Sample) : Point D :=
  FE i z (Y N (active i) z)-width • Pref i z-reply (active i) z

omit [MeasurableSpace A] in
/-- Exact canonical source form of the completed paid-final lower error. -/
theorem completed_finalError_eq (i : Fin m) (z : Sample) (hz : x z.1.1.1.1=d.x) :
    MeanCompletedFinalAccuracy.finalError d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs
      x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G i z =
    FE i z (MeanBenchmarkMoments.finalCenter d i (staticSeed z.1.1.1)+rho • z.1.1.2.2 (active i))-
      (MeanBenchmarkMoments.finalMean d i (staticSeed z.1.1.1)+width • Pref i z) := by
  have hf := MeanFinalSourceEvaluator.sourceError_eq_sourceFinalEvaluator d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hfinalMass G
    (MeanChronologicalFinalObservation.sourceInput d.G nodes anchors seeds main final sampling N d.r Ds x P d.sigma δ t w)
    (MeanChronologicalFinalProjection.finalCoarse d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs x P position
      d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall d.x hfinalMass)
    (MeanChronologicalFinalProjection.finalComparison d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hfinalMass)
    (MeanBenchmarkMoments.finalCenter d) (MeanBenchmarkMoments.finalMean d) width z.1.1 z.1.2 z.2 i
  dsimp only [MeanChronologicalFinalObservation.sourceInput] at hf
  rw [hz] at hf
  change MeanCompletedFinalAccuracy.finalError d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs
      x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G i z =
    MeanFinalSourceEvaluator.sourceFinalEvaluator d.G nodes anchors seeds main final sampling N d.r Ds G
      ⟨table d.G nodes anchors d.r d.sigma Ds δ t w main final sampling,d.x,Psource z⟩ (fullTape z) i
      (MeanBenchmarkMoments.finalCenter d i (staticSeed z.1.1.1)+rho • z.1.1.2.2 (active i))-
        (MeanBenchmarkMoments.finalMean d i (staticSeed z.1.1.1)+width • Pref i z) at hf
  rw [sourceFinalEvaluator_eq d nodes anchors seeds main final sampling N Ds δ t w P G privateShift z i] at hf
  exact hf

include hP hV hG hbaseρ in
/-- Actual final callback error equals the completed lower error on its
constructed support, without identifying the true iterate with a benchmark. -/
theorem kernel_finalError_ae (i : Fin m) :
    finalError d nodes anchors seeds main final sampling N Ds δ t w P V G privateShift i =ᵐ[completedLaw]
      MeanCompletedFinalAccuracy.finalError d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs
        x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G i := by
  filter_upwards [kernel_seed_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ,
    kernel_comparison_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ,
    kernel_center_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ hbaseρ] with z hs hc hxz
  rw [completed_finalError_eq d nodes anchors seeds main final sampling N Ds δ t w hDs x P V hfinalMass G privateShift i z hxz]
  unfold finalError
  rw [benchmark_eq_comparison d nodes anchors seeds main final sampling N Ds δ t w hDs P V N le_rfl (active i) z]
  dsimp only
  rw [←hs,←congrFun hc (active i)]
  have he : rawReference d (nodes (active i)) (staticSeed z.1.1.1)=MeanBenchmarkMoments.finalCenter d i (staticSeed z.1.1.1) := by
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  unfold MeanBenchmarkMoments.finalMean
  simp only [Equiv.apply_symm_apply,MeanGeometry.center_radius]
  abel

local notation "pairs" => MeanCompletedAugmentedLaws.retainedAugmentedPairs d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs
  x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G
local notation "wf" => Numerics.GaussLegendre.weight m

omit [MeasurableSpace A] in
/-- The canonical final observation keeps the actual full-build cached Pi. -/
theorem storedPi_eq_cache (z : Sample) (i : Fin m) :
    MeanChronologicalFinalObservation.storedPi d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs
      x P d.sigma δ t w hfinalMass G
      (z.1.1,(split (MeanFinalBatchCoupling.batchCut d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hfinalMass) z.1.2).1) i=
    storedPoint (cacheT z) (MeanExecutablePrefix.designated i) := by
  unfold MeanChronologicalFinalObservation.storedPi MeanFinalBatchCoupling.storedPi
  change storedPoint (envAt G ⟨table d.G nodes anchors d.r d.sigma Ds δ t w main final sampling,x z.1.1.1.1,Psource z⟩
    (MeanFinalBatchCoupling.finishFocus d.G nodes anchors seeds main final sampling N).cut Env.empty
    (split (MeanFinalBatchCoupling.finishFocus d.G nodes anchors seeds main final sampling N).cut (fullTape z)).1)
    ((MeanFinalBatchCoupling.finishFocus d.G nodes anchors seeds main final sampling N).saved (MeanExecutablePrefix.designated i))=_
  rw [MeanFinalAssemblyReadout.final_designated_literal]
  dsimp only [MeanSourceBuildRms.cache,SourceMeanBuildRms.actualEnv]
  rw [SourceMeanShift.cache_designated]
  rfl

/-- The literal paid-final numerical target on the full source program. -/
def paidTarget (z : Sample) : Point D := d.sigma • Psource z+
  ∑ i,wf i • (reply (active i) z+width • (Pref i z-storedPoint (cacheT z) (MeanExecutablePrefix.designated i)))

include hP hV hG in
/-- Its numerical paid target is the completed coupling's actual target on
its source support, with every original Pi retained literally. -/
theorem kernel_paidTarget_ae : paidTarget d nodes anchors seeds main final sampling N Ds δ t w P V G privateShift =ᵐ[completedLaw]
    MeanCompletedQuadrature.numericalTarget d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs
      x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G := by
  filter_upwards [kernel_seed_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ] with z hs
  unfold paidTarget MeanCompletedQuadrature.numericalTarget
  rw [MeanCompletedReconstruction.retainedPairs_readout]
  dsimp only
  rw [←hs]
  apply congrArg (fun y => d.sigma • Psource z+y)
  apply Finset.sum_congr rfl
  intro i _
  rw [storedPi_eq_cache d nodes anchors seeds main final sampling N Ds δ t w hDs x P hfinalMass G privateShift z i]
  rw [Equiv.apply_symm_apply]
  rfl

include hP hV hG in
/-- The full-build physical reference equals primitive mean plus sigma times
the actual normalized completed reference. The exact quadrature defects
cancel; no new reference or accuracy law is assumed. -/
theorem kernel_referenceReadout_ae (hm : 0<m) (ht : 0<t) (q : ℝ) :
    MeanSourceBuildRms.referenceReadout d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource Vsource Pref =ᵐ[completedLaw]
      (fun z => Gibbs.primitiveMean d.F d.x d.r+d.sigma • MeanCompletedReference.readout d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs
        x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G hm ht q z) := by
  filter_upwards [kernel_seed_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ,
    kernel_paidTarget_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ privateShift,
    MeanCompletedQuadrature.kernel_target_sub_reference d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass L hL
      x P position hx hP hposition d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G hG J Jfinal hm ht q ρ] with z hs hp hq
  have hd := MeanCompletedRms.paid_target_sub_reference d nodes anchors seeds Ds δ t w main final sampling Psource
    (MeanSourceBuildRms.privateValue d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource) Vsource
    (MeanSourceBuildRms.raw d nodes anchors seeds main final sampling N fullTape)
    (MeanSourceBuildRms.flow d nodes anchors seeds main final sampling N fullTape) Pref z
  change paidTarget d nodes anchors seeds main final sampling N Ds δ t w P V G privateShift z-
    MeanSourceBuildRms.referenceReadout d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource Vsource Pref z =
      MeanOriginalBounds.quadratureError d (actualSeed z) at hd
  rw [MeanCompletedReconstruction.retainedPairs_readout] at hq
  dsimp only at hq
  rw [hs,←hp] at hq
  exact sub_right_injective (hd.trans hq.symm)

/-- The genuinely lower private-anchor error on the original incoming law. -/
def incomingAnchorError (z : A × Tape D (Host d.G nodes anchors seeds main final sampling N)) : Point D :=
  backwardEnd d.G.R • (SourceMeanBuildRms.privateResult d.G nodes anchors seeds d.r d.sigma Ds δ t w main final sampling N
    privateShift G d.x (P z.1) z.2-V z.1)

variable [IsProbabilityMeasure ρ]
  (μ : Measure (Coarse (d := D) d.G nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
  (hbaseμ : ∀ᵐ c ∂μ,x c.1=d.x)
  (ha : 0<rowBound (m := m) d.r d.sigma δ t w)
  (hA : ∀ i,∑ j,|d.G.matrix d.r d.sigma (nodes i) (nodes j)|≤rowBound (m := m) d.r d.sigma δ t w)
  (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut d.G nodes anchors seeds main final sampling N))=
    μ.prod (tapeLaw L (body (a := a) (h := h) d.G nodes main final sampling N)))
  (hincoming : μ.map (MeanCompletedAugmentedLaws.incomingAugmented d.G nodes anchors seeds main final sampling N d.r d.hr x P (fun a => backwardEnd d.G.R • V a)
      d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall d.x)=
    ((stdGaussian (Point D)).prod (seedMeasure d)).prod (Measure.pi fun _ : Fin m => stdGaussian (Point D)))

include hP hV hG ha hA hsplit hincoming in
/-- The literal full-build analytic seed has the original common source law
on the actual completed kernel. All source support is supplied internally. -/
theorem source_seed_preserving : MeasurePreserving actualSeed completedLaw (seedMeasure d) := by
  have hp := MeanCompletedQuadrature.kernel_seed_preserving d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass L hL
    x P position hx hP hposition d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G hG J Jfinal
    ha hA ρ μ hsplit hincoming
  have he : (fun z : Sample => (MeanCompletedAugmentedLaws.retainedAugmentedPairs d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs
        x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G z).1.2) =ᵐ[completedLaw] actualSeed := by
    filter_upwards [kernel_seed_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ] with z hz
    rw [MeanCompletedReconstruction.retainedPairs_readout]
    exact hz
  refine ⟨MeanSourceBuildRms.sourceSeed_measurable d nodes anchors seeds main final sampling N Ds δ t w fullTape Psource Vsource
    measurable_fst.snd (hP.comp measurable_fst.fst.fst.fst) (hV.comp measurable_fst.fst.fst.fst),?_⟩
  exact (Measure.map_congr he.symm).trans hp.map_eq

include hP hV hG ha hA hsplit hincoming hbaseρ hbaseμ in
/-- The completed actual main error is paid by the LOWER full-source child
accuracy and the original-data node moment, at bounded stages only. -/
theorem main_error_bound (k : ℕ) (hk : k<N) (i : Fin n)
    (amplitude h₀ : ℝ) (hmesh : MeshConditions d h₀) (hhalf : contraction d h₀≤1/2)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (d.G.radius d.r (nodes i)) (main i).shiftVector)
    (hfiber : ∀ y : Point D,MemLp (FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
      (Gibbs.primitiveMean d.F y (d.G.radius d.r (nodes i))) childWidth) 2 ((J k hk).joint i y))
    (hbound : ∀ y : Point D,(∫ z,‖FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
      (Gibbs.primitiveMean d.F y (d.G.radius d.r (nodes i))) childWidth z‖^2 ∂(J k hk).joint i y)≤
        (amplitude*Gibbs.primitiveScale d.F y)^2) :
    ∃ hi : MemLp (mainError d nodes anchors seeds main final sampling N Ds δ t w P V G k i) 2 completedLaw,
      (∫ z,‖mainError d nodes anchors seeds main final sampling N Ds δ t w P V G k i z‖^2 ∂completedLaw)≤
        amplitude^2*MeanAllNodeMoments.scaleSquareBudget d h₀ ∧
      ‖hi.toLp _‖≤Real.sqrt (amplitude^2*MeanAllNodeMoments.scaleSquareBudget d h₀) := by
  have hseed := MeanCompletedChildAccuracy.seed_preserving_of_incoming d.G nodes anchors seeds main final sampling N d.r d.hr
    x P position hx hP hposition d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall d.x μ hincoming
  obtain ⟨hi,hI,hN⟩ := MeanCompletedChildAccuracy.completed_main_error_bound d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass
    L hL x P position hx hP hposition d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x μ
    hbaseμ hseed J G hG ha hA ρ hsplit hfinalMass Jfinal k hk i amplitude h₀ hmesh hhalf hshift hfiber hbound
  have he := kernel_mainError_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ hbaseρ k hk i
  let ho := hi.ae_eq he.symm
  refine ⟨ho,?_,?_⟩
  · exact (integral_congr_ae (he.fun_comp fun v => ‖v‖^2)).trans_le hI
  · have hLp : ho.toLp _=hi.toLp _ := Lp.ext (ho.coeFn_toLp.trans (he.trans hi.coeFn_toLp.symm))
    rw [hLp]
    exact hN

include hP hV hG ha hA hsplit hincoming hbaseρ in
/-- Actual completed final callback payment from the LOWER retained
original-designated full-seed child coupling. -/
theorem final_error_bound (i : Fin m) (amplitude : ℝ)
    (hshift : ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (d.r*d.G.R) (final i).shiftVector)
    (hfiber : ∀ y : Point D,MemLp (DesignatedChildRunShift.lowerError (final i).program G (final i).coefficient y
      (Gibbs.primitiveMean d.F y (d.r*d.G.R)) width) 2 (Jfinal.joint i y))
    (hbound : ∀ y : Point D,(∫ z,‖DesignatedChildRunShift.lowerError (final i).program G (final i).coefficient y
      (Gibbs.primitiveMean d.F y (d.r*d.G.R)) width z‖^2 ∂Jfinal.joint i y)≤
        (amplitude*Gibbs.primitiveScale d.F y)^2) :
    ∃ hi : MemLp (finalError d nodes anchors seeds main final sampling N Ds δ t w P V G privateShift i) 2 completedLaw,
      (∫ z,‖finalError d nodes anchors seeds main final sampling N Ds δ t w P V G privateShift i z‖^2 ∂completedLaw)≤
        amplitude^2*MeanBenchmarkMoments.finalScaleSquareBudget d ∧
      ‖hi.toLp _‖≤Real.sqrt (amplitude^2*MeanBenchmarkMoments.finalScaleSquareBudget d) := by
  obtain ⟨hi,hI,hN⟩ := MeanCompletedFinalAccuracy.completed_final_error_bound d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass
    L hL x P position hx hP hposition d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G hG J Jfinal
    ha hA ρ μ hsplit hincoming i amplitude hshift hfiber hbound
  have he := kernel_finalError_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ hbaseρ privateShift i
  let ho := hi.ae_eq he.symm
  refine ⟨ho,?_,?_⟩
  · exact (integral_congr_ae (he.fun_comp fun v => ‖v‖^2)).trans_le hI
  · have hLp : ho.toLp _=hi.toLp _ := Lp.ext (ho.coeFn_toLp.trans (he.trans hi.coeFn_toLp.symm))
    rw [hLp]
    exact hN

/-- Source node-moment average of the genuinely lower main amplitudes. -/
def mainPayment (h₀ : ℝ) (amplitude : ℕ → Fin n → ℝ) (k : ℕ) (i : Fin n) : ℝ :=
  Real.sqrt (amplitude k i^2*MeanAllNodeMoments.scaleSquareBudget d h₀)
/-- Source final-center moment average of the genuinely lower final amplitudes. -/
def finalPayment (amplitude : Fin m → ℝ) (i : Fin m) : ℝ :=
  Real.sqrt (amplitude i^2*MeanBenchmarkMoments.finalScaleSquareBudget d)
/-- The actual finite source RMS payment, with intrinsic initializer and
all final-child occurrences retained. -/
def outputBudget (h₀ : ℝ) (κ κf : ℝ≥0) (aRow Eprivate : ℝ)
    (amplitude : ℕ → Fin n → ℝ) (amplitudeFinal : Fin m → ℝ) : ℝ :=
  (∑ i,|GaussLegendre.weight m i|)*((κf:ℝ)*MeanSourceSharpRms.sourceMainBudget d nodes h₀ N κ aRow Eprivate
    (mainPayment d h₀ amplitude))+
    ∑ i,|GaussLegendre.weight m i| *finalPayment d amplitudeFinal i+MeanOriginalBounds.quadratureBudget d

include hP hV hG ha hA hsplit hincoming hbaseρ hbaseμ in
/-- Actual complete source-program error on the constructed completed
coupling, to its physical retained reference. Source law, original numerical
defects, callback measurability and all lower-child averaging are proved
internally. Only genuinely LOWER errors and deterministic child guards remain. -/
theorem output_error_bound (hm : 0<m) (ht : 0<t) (q : ℝ)
    (h₀ : ℝ) (hmesh : MeshConditions d h₀) (hhalf : contraction d h₀≤1/2)
    (hpsi : d.G.psi≤d.G.R^4) (κ κf : ℝ≥0)
    (Eprivate : ℝ)
    (hanchor : MemLp (incomingAnchorError d nodes anchors seeds main final sampling N Ds δ t w P V G privateShift) 2 ρ)
    (hanchorBound : ‖hanchor.toLp _‖≤Eprivate)
    (amplitude : ℕ → Fin n → ℝ) (amplitudeFinal : Fin m → ℝ)
    (hstable : ∀ i,FixedTapeStability.ChildStable (main i).program (main i).coefficient G κ)
    (hfinalStable : ∀ i,FixedTapeStability.ChildStable (final i).program (final i).coefficient G κf)
    (hshift : ∀ i,ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (d.G.radius d.r (nodes i)) (main i).shiftVector)
    (hfinalShift : ∀ i,ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (d.r*d.G.R) (final i).shiftVector)
    (hfiber : ∀ k (hk : k<N) i y,MemLp (FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
      (Gibbs.primitiveMean d.F y (d.G.radius d.r (nodes i))) childWidth) 2 ((J k hk).joint i y))
    (hbound : ∀ k (hk : k<N) i y,(∫ z,‖FreshChildRunShift.lowerError (main i).program G (main i).coefficient y
      (Gibbs.primitiveMean d.F y (d.G.radius d.r (nodes i))) childWidth z‖^2 ∂(J k hk).joint i y)≤
        (amplitude k i*Gibbs.primitiveScale d.F y)^2)
    (hfinalFiber : ∀ i y,MemLp (DesignatedChildRunShift.lowerError (final i).program G (final i).coefficient y
      (Gibbs.primitiveMean d.F y (d.r*d.G.R)) width) 2 (Jfinal.joint i y))
    (hfinalBound : ∀ i y,(∫ z,‖DesignatedChildRunShift.lowerError (final i).program G (final i).coefficient y
      (Gibbs.primitiveMean d.F y (d.r*d.G.R)) width z‖^2 ∂Jfinal.joint i y)≤
        (amplitudeFinal i*Gibbs.primitiveScale d.F y)^2) :
    ∃ hout : MemLp (fun z => MeanSourceBuildRms.output d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource z-
      (Gibbs.primitiveMean d.F d.x d.r+d.sigma • MeanCompletedReference.readout d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs
        x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G hm ht q z)) 2 completedLaw,
      ‖hout.toLp _‖≤outputBudget d nodes N h₀ κ κf (rowBound (m := m) d.r d.sigma δ t w) Eprivate amplitude amplitudeFinal := by
  have hsource := source_preserving d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ
  have heanchor : (incomingAnchorError d nodes anchors seeds main final sampling N Ds δ t w P V G privateShift ∘
      MeanCompletedCoupling.original d.G nodes anchors seeds main final sampling N)=
      MeanCompletedRms.anchorError d
        (MeanSourceBuildRms.privateValue d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource) Vsource := by
    funext z
    rfl
  let hcomp := hanchor.comp_measurePreserving hsource
  let hanchorFull := heanchor ▸ hcomp
  have heanchorAE : (incomingAnchorError d nodes anchors seeds main final sampling N Ds δ t w P V G privateShift ∘
      MeanCompletedCoupling.original d.G nodes anchors seeds main final sampling N) =ᵐ[completedLaw]
      MeanCompletedRms.anchorError d
        (MeanSourceBuildRms.privateValue d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource) Vsource :=
    Filter.Eventually.of_forall (congrFun heanchor)
  have hanchorFullB : ‖hanchorFull.toLp _‖≤Eprivate := by
    have hLp : hanchorFull.toLp _=hcomp.toLp _ := Lp.ext (hanchorFull.coeFn_toLp.trans
      (heanchorAE.symm.trans hcomp.coeFn_toLp.symm))
    rw [hLp]
    change ‖Lp.compMeasurePreserving _ hsource (hanchor.toLp _)‖≤_
    rw [Lp.norm_compMeasurePreserving]
    exact hanchorBound
  let ε := mainPayment d h₀ amplitude
  let εf := finalPayment d amplitudeFinal
  let eval := SourceMeanExecutionRms.evaluator d.G nodes d.r Ds main final sampling N G bodyT reply
  have hmainData (k : ℕ) (hk : k<N) (i : Fin n) := main_error_bound d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ hbaseρ μ hbaseμ ha hA hsplit hincoming
    k hk i (amplitude k i) h₀ hmesh hhalf (hshift i) (hfiber k hk i) (hbound k hk i)
  have hfinalData (i : Fin m) := final_error_bound d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ hbaseρ privateShift μ ha hA hsplit hincoming
    i (amplitudeFinal i) (hfinalShift i) (hfinalFiber i) (hfinalBound i)
  have he (k : ℕ) (hk : k<N) (i : Fin n) : SharedLayerRms.childError eval Y reply childWidth Pmain k i=
      mainError d nodes anchors seeds main final sampling N Ds δ t w P V G k i := by
    funext z
    simp only [SharedLayerRms.childError,mainError,SourceMeanRetainedRms.finiteReference,ite_eq_left hk,eval]
  let hchild (k : ℕ) (hk : k<N) (i : Fin n) : MemLp (SharedLayerRms.childError eval Y reply childWidth Pmain k i) 2 completedLaw :=
    (he k hk i).symm ▸ (hmainData k hk i).choose
  have hchildB (k : ℕ) (hk : k<N) (i : Fin n) : ‖(hchild k hk i).toLp _‖≤ε k i := by
    simpa only [he k hk i,ε,mainPayment] using (hmainData k hk i).choose_spec.2
  let hfinal (i : Fin m) := (hfinalData i).choose
  have hfinalB (i : Fin m) : ‖(hfinal i).toLp _‖≤εf i := (hfinalData i).choose_spec.2
  obtain ⟨ho,hoB⟩ := MeanSourceSharpBuildRms.output_error_bound d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource Vsource Gref
    L hG measurable_fst.snd (hP.comp measurable_fst.fst.fst.fst) (hV.comp measurable_fst.fst.fst.fst) hDs hmass
    (fun k i => (MeanChronologicalBenchmark.returnedReference_measurable (d := D) (A := A) d.G nodes anchors seeds main final sampling N k i).comp measurable_fst)
    completedLaw Pref
    (source_seed_preserving d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ μ ha hA hsplit hincoming)
    h₀ hmesh hpsi κ κf (rowBound (m := m) d.r d.sigma δ t w) ha.le Eprivate hanchorFull hanchorFullB ε hA hstable hchild hchildB εf hfinalStable hfinal hfinalB
  have href := kernel_referenceReadout_ae d nodes anchors seeds main final sampling N Ds δ t w hDs hmass x P V hx hP hV L hL J hfinalMass G hG Jfinal ρ privateShift hm ht q
  have he : (fun z => MeanSourceBuildRms.output d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource z-
      MeanSourceBuildRms.referenceReadout d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource Vsource Pref z) =ᵐ[completedLaw]
    (fun z => MeanSourceBuildRms.output d nodes anchors seeds main final sampling N Ds δ t w privateShift G fullTape Psource z-
      (Gibbs.primitiveMean d.F d.x d.r+d.sigma • MeanCompletedReference.readout d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs
        x P position d.hF d.hell d.hlo d.hup d.sigma d.hsigma d.hsmall δ t w d.x hfinalMass G hm ht q z)) := by
    filter_upwards [href] with z hz
    rw [hz]
  let hout := ho.ae_eq he
  refine ⟨hout,?_⟩
  have hLp : hout.toLp _=ho.toLp _ := Lp.ext (hout.coeFn_toLp.trans (he.symm.trans ho.coeFn_toLp.symm))
  rw [hLp]
  exact hoB

end AcceleratedLogConcave.Oracle.MeanCompletedSourceRms
