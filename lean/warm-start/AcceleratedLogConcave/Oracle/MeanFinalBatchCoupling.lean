import AcceleratedLogConcave.Oracle.DesignatedChildBatchCoupling
import AcceleratedLogConcave.Oracle.DesignatedChildRunShift
import AcceleratedLogConcave.Oracle.MeanMainBatchCoupling
import AcceleratedLogConcave.Oracle.PrivateCausalLayer

/-! Literal source-mean active-final occurrences. Their designated Pi values
are the existing incoming assembly references. The conditional uses their
same completed seed and retains the whole original source sample, past, and
entire correction suffix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanFinalBatchCoupling
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open SourceMeanExecutable RecursiveMeanProgram RecursiveMeanContinuation
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability PrivateCausalLayer
local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

section Occurrence
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
    (N : ℕ)
local notation "c" => (fun i => (main i).size)
local notation "p" => (fun i => (main i).program)
local notation "en" => (fun i => (main i).enumeration)
local notation "F" => SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling
local notation "host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling N

/-- After all original main layers, also N=0; the source prefix is retained. -/
def finishFocus : FinishFocus F host := by
  let f := atFinish c p (mainSlot (a := a) main final sampling) en layerOrigin
    mainDesignated residualOrigin (mainAuxiliary main) F N batchRef
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (MeanExecutablePrefix.direct i)))
    (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))
  refine ⟨f.ctx,f.old,f.direct,f.saved,?_⟩
  have hb : TailCut (F f.old f.direct f.saved)
      (body (a := a) (h := h) M nodes main final sampling N) := by
    unfold body NonterminalMeanBlock.code initializeCenters
    exact .batch _ _ _ (.batch _ _ _ f.cut)
  exact TailCut.trans hb (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)
local notation "foc" => finishFocus M nodes anchors seeds main final sampling N

def data (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
    (hmass : ∀ i, CovarianceSetup.shiftSq (final i).shiftVector ≤ Ds^2) :
    DesignatedChildBatchCoupling.Data m (size (a := a) main final sampling) (foc).ctx where
  child := final
  slot := finalSlot (a := a) main final sampling
  old i := (foc).old (nodes.symm (.center M i))
  designated i := (foc).saved (MeanExecutablePrefix.designated i)
  auxiliary := finalAuxiliary final
  rho _ := RecursiveMeanPublicTable.centerNoise r M.R Ds
  radius _ := r*M.R
  Ds := Ds
  rho_nonneg _ := (RecursiveExecutableDomain.center_noise_pos M r Ds hr hDs).le
  radius_pos _ := mul_pos hr M.R_pos
  Ds_pos := hDs
  shift_budget := hmass
  small _ := RecursiveExecutableDomain.final_noise_separation M r Ds hr hDs

variable (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
    (hmass : ∀ i, CovarianceSetup.shiftSq (final i).shiftVector ≤ Ds^2)
local notation "B" => data M nodes anchors seeds main final sampling N r Ds hr hDs hmass

/-- The literal final arithmetic still reads original P and the same Pi. -/
def suffix : Prog (size (a := a) main final sampling) (replyCtx m (foc).ctx) .point :=
  (RetainedMeanCorrection.code (RefMap.shiftMany m ((foc).saved (MeanExecutablePrefix.saved .here)))
    batchRef (fun i => RefMap.shiftMany m ((foc).saved (MeanExecutablePrefix.designated i)))).lower
      (correctionSlot (a := a) main final sampling) (fun r => r)
      (RefMap.shiftMany m ((foc).saved (MeanExecutablePrefix.saved .here)))
      (RefMap.shiftMany m ((foc).saved (MeanExecutablePrefix.saved .here)))

def batchCut : TailCut (.batch finalOrigin (DesignatedChildBatchCoupling.program B)
    (suffix M nodes anchors seeds main final sampling N)) host := (foc).cut

theorem data_table (σ δ t w : ℝ) (i : Fin m) :
    SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling ∘ ((B).slot i) =
      matrixTable (CovarianceSetup.childRoot ((B).rho i) ((B).radius i) ((B).child i).shiftVector)
        ((B).child i).coefficient := by
  funext j
  exact SourceMeanExecutable.table_final M nodes anchors r σ Ds δ t w main final sampling i j

local notation "cut" => batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d (afterBatch cut)
variable {A H : Type*} [MeasurableSpace A] [MeasurableSpace H]
  (G : Point d → Point d) (hG : Measurable G)
  (input : A → Inputs d (size (a := a) main final sampling))
  (hc : ∀ j, Measurable (fun a => (input a).coefficient j))
  (hx : Measurable (fun a => (input a).center))
  (hP : Measurable (fun a => (input a).momentum))

/-- The existing designated value in the ACTUAL prefix interpreter store. -/
def storedPi (i : Fin m) (z : A × Prefix d cut) : Point d :=
  storedPoint (envAt G (input z.1) cut Env.empty z.2) ((B).designated i)

include hG hc hx hP in
theorem storedPi_measurable (i : Fin m) : Measurable
    (storedPi M nodes anchors seeds main final sampling N r Ds hr hDs hmass G input i) := by
  have he : OperationalMeasurability.EnvPathMeasurable (fun _ : A × Prefix d cut =>
      (Env.empty : Env d [])) := by intro ty ref; cases ref
  exact envAt_pathMeasurable G hG cut
    (fun z : A × Prefix d cut => input z.1) (fun _ => Env.empty)
    Prod.snd (fun j => (hc j).comp measurable_fst) (hx.comp measurable_fst)
    (hP.comp measurable_fst) he measurable_snd ((B).designated i)

variable (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  (J : DesignatedChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass))
  (coarse : A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass) → H) (hcoarse : Measurable coarse)
  (center : Fin m → H → Point d) (hcenter : ∀ i, Measurable (center i))
  (comparison : Fin m → A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass) → Point d)
  (hcomparison : ∀ i, Measurable (comparison i))

/-- Extract full literal final tapes and the actual stored Pi; never redraw Pi. -/
def observation (z : A × Prefix d (afterBatch cut)) :
    H × (∀ i, DesignatedChildBatchCoupling.Raw d B i) :=
  let parts := batchParts (d := d) cut z.2
  let old := (z.1,parts.1)
  (coarse old,fun i => (comparison i old,
    (storedPi M nodes anchors seeds main final sampling N r Ds hr hDs hmass G input i old,parts.2 i)))

include hG hc hx hP hcoarse hcomparison in
theorem observation_measurable : Measurable
    (observation M nodes anchors seeds main final sampling N r Ds hr hDs hmass G input coarse comparison) := by
  have hp : Measurable (fun z : A × Prefix d (afterBatch cut) => batchParts cut z.2) :=
    (measurable_batchParts (d := d) cut).comp measurable_snd
  have ho := measurable_fst.prodMk hp.fst
  exact (hcoarse.comp ho).prodMk (Measurable.of_eval fun i =>
    ((hcomparison i).comp ho).prodMk
      (((storedPi_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass
        G hG input hc hx hP i).comp ho).prodMk ((measurable_pi_apply i).comp hp.snd)))

def referenceConditional : Kernel (A × Prefix d (afterBatch cut)) (Fin m → Point d) :=
  (DesignatedChildBatchCoupling.referenceBatch L hL B J center hcenter).comap
    (observation M nodes anchors seeds main final sampling N r Ds hr hDs hmass G input coarse comparison)
    (observation_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      G hG input hc hx hP coarse hcoarse comparison hcomparison)
instance referenceConditional_markov : IsMarkovKernel
    (referenceConditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      G hG input hc hx hP L hL J coarse hcoarse center hcenter comparison hcomparison) := by
  unfold referenceConditional
  infer_instance

/-- Actual original full source tape and all accumulated history are kept. -/
def kernel : Kernel (A × Tape d host) ((A × Tape d host) × (Fin m → Point d)) :=
  CausalTailHistory.onTape L (afterBatch cut)
    (referenceConditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      G hG input hc hx hP L hL J coarse hcoarse center hcenter comparison hcomparison)
instance kernel_markov : IsMarkovKernel
    (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      G hG input hc hx hP L hL J coarse hcoarse center hcenter comparison hcomparison) := by
  unfold kernel
  infer_instance

theorem original_preserved :
    (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      G hG input hc hx hP L hL J coarse hcoarse center hcenter comparison hcomparison).fst = Kernel.id :=
  CausalTailHistory.onTape_original L (afterBatch cut) _

/-- The ENTIRE actual correction continuation remains a separate product,
even when old history and the consumed prefix are correlated. -/
theorem whole_suffix (oldLaw : Measure (A × Tape d host))
    (μ : Measure (A × Prefix d cut)) [SFinite μ]
    (hsplit : oldLaw.map (CausalTailHistory.unpack cut) = μ.prod
      (tapeLaw L (.batch finalOrigin (DesignatedChildBatchCoupling.program B)
        (suffix M nodes anchors seeds main final sampling N)))) :
    ((kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      G hG input hc hx hP L hL J coarse hcoarse center hcenter comparison hcomparison) ∘ₘ oldLaw).map
      (CausalTailHistory.unpackExtended (afterBatch cut)) =
      ((advancedLaw L cut μ) ⊗ₘ
        (referenceConditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass
          G hG input hc hx hP L hL J coarse hcoarse center hcenter comparison hcomparison)).prod
        (tapeLaw L (suffix M nodes anchors seeds main final sampling N)) := by
  exact CausalTailHistory.whole_suffix_fresh_of_split L (afterBatch cut) oldLaw
    (advancedLaw L cut μ) (advanced_split_of_split L cut oldLaw μ hsplit) _
end Occurrence

section Recursive
open MeanMainBatchCoupling RecursiveExecutable
variable {m n a h ns d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
    (snodes : Fin ns ≃ mesh.Source m)
    (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4) (scale r σ q : ℝ)
    (K : ℝ) (hDs : 0 < Ds) (hpsi : M.psi ≤ M.R^4)
    (inventory Hs : ℕ) (hcount : n+ns ≤ inventory) (hK : (1/2:ℝ)<K)
    (hHs : 8*K+4 ≤ (Hs:ℝ))
    (hbudget : sourceShiftBase layers inventory ^ (Hs+1) ≤ Ds)
    (hr : 0 < r) (hqK : q ≤ K)
local notation "mc" => recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q
local notation "fc" => recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q
local notation "sc" => recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q

/-- Actual q−t active-final children. All covariance and shift-domain guards
come from the source geometry and the public support-height budget. -/
def recursiveData :=
  data M nodes anchors seeds mc fc sc layers r Ds hr hDs
    (fun i => (recursive_final_shift M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
      scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hqK i).2)
local notation "BR" => recursiveData M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
  scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hqK

/-- Lower full-seed couplings at the literal smaller mean calls; no current
parent accuracy or final retained-reference law is assumed. -/
def recursiveLower (L : PrimitiveLaws d)
    (joint : ∀ i : Fin m, Kernel (Point d) ((Point d × Tape d (recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q i).program) × Point d))
    (hmarkov : ∀ i, IsMarkovKernel (joint i))
    (hsource : ∀ i, (joint i).fst = Kernel.const (Point d)
      (DesignatedChildRetainedCoupling.sourceLaw L (recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q i).program)) :
    DesignatedChildBatchCoupling.Lower L BR := ⟨joint,hmarkov,hsource⟩

/-- The exact source reference kernel of precision q−t, with positive literal
radius/width and the inherited curvature-radius domain, identifies each
retained pair in the constructive batch. Gaussian reference marginals need
not be supplied separately. -/
theorem recursive_paired_law (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d))
    (joint : ∀ i : Fin m, Kernel (Point d) ((Point d × Tape d (recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q i).program) × Point d))
    (hmarkov : ∀ i, IsMarkovKernel (joint i))
    (hsource : ∀ i, (joint i).fst = Kernel.const (Point d)
      (DesignatedChildRetainedCoupling.sourceLaw L (recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q i).program))
    {potential : Point d → ℝ} {ell : ℝ}
    (hF : ContDiff ℝ 2 potential) (hell : 0 ≤ ell)
    (hlo : ∀ z b, 0 ≤ fderiv ℝ (fderiv ℝ potential) z b b)
    (hup : ∀ z b, fderiv ℝ (fderiv ℝ potential) z b b ≤ ell*‖b‖^2)
    (hm : 0 < m) (hσ : 0 < σ) (hcurvature : r^2*ell ≤ 1/2)
    {H : Type*} [MeasurableSpace H]
    (center : Fin m → H → Point d) (hcenter : ∀ i, Measurable (center i))
    (hretained : ∀ i x, (joint i x).map (fun z => (z.1.1,z.2)) =
      stdGaussian (Point d) ⊗ₘ
        (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-t)).kernel.comap
          (fun v => (finalParameters M r σ ell hr hσ hell hcurvature x,v)) measurable_prodMk_left)
    (h : H) :
    (DesignatedChildBatchCoupling.pairedBatch L hL BR
      (recursiveLower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K
        hDs hpsi inventory Hs hcount hK hHs hbudget hr hqK L joint hmarkov hsource)
      center hcenter).comap (fun w => (h,w)) measurable_prodMk_left ∘ₘ
      Measure.pi (DesignatedChildBatchCoupling.rawLaw L BR) =
    Measure.pi (fun i : Fin m => stdGaussian (Point d) ⊗ₘ
      (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-t)).kernel.comap
        (fun v => (finalParameters M r σ ell hr hσ hell hcurvature (center i h),v)) measurable_prodMk_left) := by
  rw [DesignatedChildBatchCoupling.pairedBatch_law]
  congr 1
  funext i
  exact hretained i (center i h)
end Recursive

end AcceleratedLogConcave.Oracle.MeanFinalBatchCoupling
