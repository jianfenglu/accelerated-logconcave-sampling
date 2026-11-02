import AcceleratedLogConcave.Oracle.SourceMeanExecutionRms
import AcceleratedLogConcave.Oracle.GeneralMainFocus
import AcceleratedLogConcave.Oracle.TailCutExecution
import AcceleratedLogConcave.Oracle.PrivateRecursiveBatchBudget
import AcceleratedLogConcave.Oracle.FreshChildBatchErrorTransfer

/-! Concrete mean-main batch occurrences in the full original source mean
program, followed by the source-specialized recursive lower children. These
are the fresh main calls; retained designated active-final calls require their
own joint assembly law and are deliberately not identified with freshChild. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanMainBatchCoupling
open Numerics.AffineGraph TapeLowering NoisyLayer AffineLowering
open SourceMeanExecutable RecursiveMeanProgram RecursiveMeanContinuation
open TailOccurrenceCut TailCut GeneralMainFocus
open CanonicalTapeLaw CanonicalTapeMeasurability
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1000000

local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

section Occurrence
variable {m n a h : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
    (N k : ℕ) (hk : k<N)
local notation "c" => (fun i => (main i).size)
local notation "p" => (fun i => (main i).program)
local notation "en" => (fun i => (main i).enumeration)
local notation "slots" => (mainSlot (a := a) main final sampling)
local notation "F" => SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling
local notation "loop" => iterateThen c p slots en layerOrigin mainDesignated residualOrigin (mainAuxiliary main) F
local notation "host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling N

/-- Full incoming source prefix: original input reads, private call, literal
assembly, flow seeds and direct rows. No earlier occurrence is discarded. -/
def bodyCut : TailCut (body (a := a) (h := h) M nodes main final sampling N) host := by
  unfold SourceMeanExecutable.program incoming MeanExecutablePrefix.code MeanGaussianSetup.setup
  exact .step _ _ _ (.step _ _ _ (.batch _ _ _ (.batch _ _ _
    (.batch _ _ _ (.batch _ _ _ (.batch _ _ _ (.batch _ _ _ .here)))))))

/-- The actual bounded mean-main occurrence after initialization and k
complete layers, inside the entire original source mean program. -/
def focus : Focus c p slots en layerOrigin mainDesignated residualOrigin (mainAuxiliary main) F host := by
  let f := GeneralMainFocus.focus c p slots en layerOrigin mainDesignated residualOrigin
    (mainAuxiliary main) F N k hk batchRef
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (MeanExecutablePrefix.direct i)))
    (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))
  have hb : TailCut (loop (f.remainingAfter+1) f.old f.direct f.saved)
      (body (a := a) (h := h) M nodes main final sampling N) := by
    unfold body NonterminalMeanBlock.code initializeCenters
    exact .batch _ _ _ (.batch _ _ _ f.cut)
  exact ⟨f.remainingAfter,f.ctx,f.old,f.direct,f.saved,
    TailCut.trans hb (bodyCut M nodes anchors seeds main final sampling N)⟩

local notation "foc" => focus M nodes anchors seeds main final sampling N k hk

theorem focus_remaining : (foc).remainingAfter = N-1-k :=
  GeneralMainFocus.remaining_eq c p slots en layerOrigin mainDesignated residualOrigin
    (mainAuxiliary main) F N k hk batchRef
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (MeanExecutablePrefix.direct i)))
    (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))

def child (i : Fin n) : Prog (SourceMeanExecutable.size (a := a) main final sampling) (foc).ctx .point :=
  freshChild (main i).program (main i).enumeration (slots ∘ childSlot c p i) ((foc).old i)
    (mainDesignated (foc).remainingAfter i) (mainAuxiliary main (foc).remainingAfter i)

/-- Complete actual current residual/row batches and every later layer/final. -/
def next : Prog (SourceMeanExecutable.size (a := a) main final sampling) (replyCtx n (foc).ctx) .point :=
  .batch [] (fun j => residualDraw (residualOrigin (foc).remainingAfter j))
    (.batch [] (noisyRow (fun j l => slots (aSlot c p j l))
      (fun j l => slots (residualSlot c p j l)) (foc).direct)
      (loop (foc).remainingAfter batchRef
        (fun j => preserveDirect ((foc).direct j)) (fun q => preserveDirect ((foc).saved q))))

def batchCut : TailCut (.batch (layerOrigin (foc).remainingAfter)
    (child M nodes anchors seeds main final sampling N k hk)
    (next M nodes anchors seeds main final sampling N k hk)) host := (foc).cut

/-- Exact source table slots and original chronological occurrence origins. -/
def data (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
    (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2) :
    FreshChildBatchCoupling.Data n (SourceMeanExecutable.size (a := a) main final sampling) (foc).ctx where
  child := main
  slot i := slots ∘ childSlot c p i
  old := (foc).old
  designated := mainDesignated (foc).remainingAfter
  auxiliary := mainAuxiliary main (foc).remainingAfter
  rho _ := RecursiveMeanPublicTable.centerNoise r M.R Ds
  radius i := M.radius r (nodes i)
  Ds := Ds
  rho_nonneg _ := (RecursiveExecutableDomain.center_noise_pos M r Ds hr hDs).le
  radius_pos i := M.radius_pos r hr (nodes i)
  Ds_pos := hDs
  shift_budget := hmass
  small i := RecursiveExecutableDomain.mean_noise_separation M r Ds hr hDs (nodes i)

theorem data_program (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
    (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2) (i : Fin n) :
    FreshChildBatchCoupling.program
      (data M nodes anchors seeds main final sampling N k hk r Ds hr hDs hmass) i =
      freshChild (main i).program (main i).enumeration (slots ∘ childSlot c p i)
        ((foc).old i) (mainDesignated (foc).remainingAfter i)
        (mainAuxiliary main (foc).remainingAfter i) := rfl

/-- The original public table already supplies the exact child covariance
root and original lower coefficients; no table-match premise is added. -/
theorem data_table (r σ Ds δ t w : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
    (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2) (i : Fin n) :
    table M nodes anchors r σ Ds δ t w main final sampling ∘
      (data M nodes anchors seeds main final sampling N k hk r Ds hr hDs hmass).slot i =
      matrixTable (CovarianceSetup.childRoot (RecursiveMeanPublicTable.centerNoise r M.R Ds)
        (M.radius r (nodes i)) (main i).shiftVector) (main i).coefficient := by
  funext j
  change table M nodes anchors r σ Ds δ t w main final sampling (slots (childSlot c p i j)) = _
  rw [table_main]
  simp only [mainTable, RecursiveMeanPublicTable.sourceLayerTable, layerTable_child]

end Occurrence

section ReferenceDomain
variable {m n d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)

/-- Every actual main inventory radius is at most the parent's physical radius. -/
theorem radius_le (r : ℝ) (hr : 0 ≤ r) (i : M.MeanNode) : M.radius r i ≤ r := by
  have hs (z : ℝ) : Real.sqrt (1-z^2) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1-z^2 ≤ 1 by nlinarith [sq_nonneg z])
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩
  · exact le_rfl
  · exact mul_le_of_le_one_right hr (M.R_le_half.trans (by norm_num))
  · exact mul_le_of_le_one_right hr (hs _)
  · exact (mul_le_of_le_one_right (mul_nonneg hr (Real.sqrt_nonneg _)) (hs _)).trans
      (mul_le_of_le_one_right hr (M.matrix_sqrt_variance_le_one ρ))
  · exact mul_le_of_le_one_right hr (hs _)

theorem radius_curvature (r ell : ℝ) (hr : 0 < r) (hell : 0 ≤ ell)
    (hcurvature : r^2*ell ≤ 1/2) (i : M.MeanNode) : (M.radius r i)^2*ell ≤ 1/2 :=
  (mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (M.radius_pos r hr i).le hr.le).2 (radius_le M r hr.le i)) hell).trans hcurvature

/-- Actual main-child parameters, with positive literal width and applicable
curvature domain, including terminal lower precisions. -/
def mainParameters (r σ Ds δ t w ell : ℝ) (hr : 0 < r) (hσ : 0 < σ) (hDs : 0 < Ds)
    (hδ : 0 < δ) (hell : 0 ≤ ell) (hcurvature : r^2*ell ≤ 1/2) (i : Fin n) (x : Point d) :
    Conditional.SourceParameters (Point d) ell :=
  ⟨(x,M.radius r (nodes i),RecursiveMeanPublicTable.mainWidth n r M.R Ds
      (rowBound (m := m) r σ δ t w)), M.radius_pos r hr (nodes i),
    RecursiveExecutableDomain.mean_main_width_pos M nodes r σ Ds δ t w hr hσ hDs hδ,
    radius_curvature M r ell hr hell hcurvature (nodes i)⟩

def finalParameters (r σ ell : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hell : 0 ≤ ell) (hcurvature : r^2*ell ≤ 1/2) (x : Point d) :
    Conditional.SourceParameters (Point d) ell :=
  ⟨(x,r*M.R,RecursiveMeanPublicTable.finalWidth M.R σ), mul_pos hr M.R_pos,
    RecursiveExecutableDomain.mean_final_width_pos M σ hσ,
    by
      have hb : r*M.R ≤ r := mul_le_of_le_one_right hr.le (M.R_le_half.trans (by norm_num))
      exact (mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (mul_pos hr M.R_pos).le hr.le).2 hb) hell).trans hcurvature⟩

end ReferenceDomain

section Recursive
open RecursiveExecutable
variable {m n a h ns : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
    (snodes : Fin ns ≃ mesh.Source m)
    (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4) (scale r σ q : ℝ)

def recursiveMain : Fin n → ExecutableData := fun i =>
  mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale
    (M.radius r (nodes i))
    (RecursiveMeanPublicTable.mainWidth n r M.R Ds (rowBound (m := m) r σ δ t w)) (q-1/4)

def recursiveFinal : Fin m → ExecutableData := fun _ =>
  mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale
    (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t)

def recursivePrivate : ExecutableData :=
  SamplingExecutable.build (privateGeometry M mesh) snodes r Ds
    (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q)
    (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers

local notation "mc" => recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q
local notation "fc" => recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q
local notation "sc" => recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q

/-- The host occurrence is the actual nonterminal mean program. The four
recursive families and every precision/radius/width agree definitionally. -/
theorem recursive_eq_build (hq : (1/2:ℝ)<q) :
    mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale r σ q =
      SourceMeanExecutable.build M nodes anchors seeds r σ Ds δ t w mc fc sc layers
        (SamplingExecutable.weights (privateGeometry M mesh) snodes r Ds
          (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q)
          (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q)
          layers (-2*M.R/backwardEnd M.R)) := by
  unfold mean
  rw [meanCore, dite_eq_right (not_le.mpr hq)]
  rfl

theorem recursive_program (hq : (1/2:ℝ)<q) :
    HEq (mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale r σ q).program
      (SourceMeanExecutable.program M nodes anchors seeds mc fc sc layers) := by
  rw [recursive_eq_build M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q hq]
  rfl

variable (K : ℝ) (hDs : 0 < Ds) (hpsi : M.psi ≤ M.R^4)
  (inventory Hs : ℕ) (hcount : n+ns ≤ inventory) (hK : (1/2:ℝ)<K)
  (hHs : 8*K+4 ≤ (Hs:ℝ))
  (hbudget : sourceShiftBase layers inventory ^ (Hs+1) ≤ Ds)
  (hr : 0 < r) (hqK : q ≤ K)

include hDs hpsi hcount hK hHs hbudget hqK hr in
theorem recursive_main_shift (i : Fin n) :
    ChildAbsorption.QueryShift (mc i).program (mc i).enumeration (mc i).coefficient
      (M.radius r (nodes i)) (mc i).shiftVector ∧
      CovarianceSetup.shiftSq (mc i).shiftVector ≤ Ds^2 :=
  PrivateRecursiveBatchBudget.lower_queryShift_and_mass M nodes anchors seeds mesh snodes
    Ds δ t w layers ht htq scale K hDs hpsi inventory Hs hcount hK hHs hbudget _ _ _
    (M.radius_pos r hr (nodes i)) (by linarith)

include hDs hpsi hcount hK hHs hbudget hqK hr ht in
theorem recursive_final_shift (i : Fin m) :
    ChildAbsorption.QueryShift (fc i).program (fc i).enumeration (fc i).coefficient
      (r*M.R) (fc i).shiftVector ∧
      CovarianceSetup.shiftSq (fc i).shiftVector ≤ Ds^2 :=
  PrivateRecursiveBatchBudget.lower_queryShift_and_mass M nodes anchors seeds mesh snodes
    Ds δ t w layers ht htq scale K hDs hpsi inventory Hs hcount hK hHs hbudget _ _ _
    (mul_pos hr M.R_pos) (by linarith)

/-- Concrete actual recursive mean-main batch, without supplier domain or
shift-mass fields. Its slots route into the full original host table. -/
def recursiveData (k : ℕ) (hk : k<layers) :=
  data M nodes anchors seeds mc fc sc layers k hk r Ds hr hDs
    (fun i => (recursive_main_shift M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
      scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hqK i).2)

variable (k : ℕ) (hk : k<layers)
local notation "Brec" => recursiveData M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
  scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hqK k hk

variable {d : ℕ} (L : PrimitiveLaws d) {F : Point d → ℝ} {ell : ℝ}
  (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell * ‖v‖^2)
  (hm : 0 < m) (hσ : 0 < σ) (hδ : 0 < δ) (hcurvature : r^2*ell ≤ 1/2)

/-- Lower retained-reference IHs at actual q−1/4 and physical parameters
construct the mean-main conditional, with its Gaussian marginal proved by
the actual recursive reference invariant. -/
def recursiveLower
    (joint : ∀ i, Kernel (Point d) ((Point d × Tape d (mc i).program) × Point d))
    (hmarkov : ∀ i, IsMarkovKernel (joint i))
    (hsource : ∀ i, (joint i).fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw L (mc i).program))
    (hretained : ∀ i x, (joint i x).map (fun z => (z.1.1,z.2)) = stdGaussian (Point d) ⊗ₘ
      (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-1/4)).kernel.comap
        (fun v => (mainParameters M nodes r σ Ds δ t w ell hr hσ hDs hδ hell hcurvature i x,v))
        measurable_prodMk_left) : FreshChildBatchCoupling.Lower L Brec :=
  FreshChildBatchCoupling.Lower.ofRecursiveReference L Brec hF hell hlo hup M hm t ht
    (fun _ => q-1/4)
    (fun i x => mainParameters M nodes r σ Ds δ t w ell hr hσ hDs hδ hell hcurvature i x)
    joint hmarkov hsource hretained

/-- Full reference vector law of the literal source mean-main batch. Supplying
recursiveLower above requires only the lower full-seed retained-reference IH. -/
theorem recursive_reference_invariant
    (hL : L.pointDraw = stdGaussian (Point d)) (J : FreshChildBatchCoupling.Lower L Brec)
    {H : Type*} [MeasurableSpace H]
    (center : Fin n → H → Point d) (hc : ∀ i, Measurable (center i)) (z : H) :
    (FreshChildBatchCoupling.referenceBatch L hL Brec J center hc).comap
      (fun raw => (z,raw)) measurable_prodMk_left ∘ₘ
        Measure.pi (FreshChildBatchCoupling.rawLaw L Brec) =
      Measure.pi (fun _ : Fin n => stdGaussian (Point d)) :=
  FreshChildBatchCoupling.referenceBatch_invariant L hL Brec J center hc z

/-- Direct source theorem from lower retained joint identities, with no
Gaussian batch certificate supplied by the caller. -/
theorem recursive_lower_reference_invariant
    (joint : ∀ i, Kernel (Point d) ((Point d × Tape d (mc i).program) × Point d))
    (hmarkov : ∀ i, IsMarkovKernel (joint i))
    (hsource : ∀ i, (joint i).fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw L (mc i).program))
    (hretained : ∀ i x, (joint i x).map (fun z => (z.1.1,z.2)) = stdGaussian (Point d) ⊗ₘ
      (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-1/4)).kernel.comap
        (fun v => (mainParameters M nodes r σ Ds δ t w ell hr hσ hDs hδ hell hcurvature i x,v))
        measurable_prodMk_left)
    (hL : L.pointDraw = stdGaussian (Point d)) {H : Type*} [MeasurableSpace H]
    (center : Fin n → H → Point d) (hc : ∀ i, Measurable (center i)) (z : H) :
    let J := recursiveLower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q
      K hDs hpsi inventory Hs hcount hK hHs hbudget hr hqK k hk L hF hell hlo hup hm hσ hδ hcurvature
      joint hmarkov hsource hretained
    (FreshChildBatchCoupling.referenceBatch L hL Brec J center hc).comap
      (fun raw => (z,raw)) measurable_prodMk_left ∘ₘ
        Measure.pi (FreshChildBatchCoupling.rawLaw L Brec) =
      Measure.pi (fun _ : Fin n => stdGaussian (Point d)) := by
  exact FreshChildBatchCoupling.referenceBatch_invariant L hL Brec _ center hc z

end Recursive

end AcceleratedLogConcave.Oracle.MeanMainBatchCoupling
