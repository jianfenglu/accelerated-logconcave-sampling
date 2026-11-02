import AcceleratedLogConcave.Oracle.MeanChronologicalFinish
import AcceleratedLogConcave.Oracle.RecursiveReachableRows

/-! Actual source specialization of finite mean-main chronology. Main calls
have the prescribed precision q−1/4, their covariance domains follow from the
original support-height budget, and Gaussian reference invariance follows from
standalone LOWER retained-reference identities at the original potential. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanRecursiveChronologicalCoupling
open Numerics.AffineGraph TapeLowering CanonicalTapeMeasurability CanonicalTapeLaw
open RecursiveExecutable SourceMeanExecutable MeanChronologicalCoupling TailOccurrenceCut TailCut
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {d m n a h ns : ℕ}
  (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
  (snodes : Fin ns ≃ mesh.Source m)
  (Ds δ t w : ℝ) (layers : ℕ) (ht : 0<t) (htq : t ≤ 1/4)
  (scale r σ q K : ℝ) (hDs : 0<Ds) (hpsi : M.psi ≤ M.R^4)
  (inventory Hs : ℕ) (hcount : n+ns ≤ inventory) (hK : (1/2:ℝ)<K)
  (hHs : 8*K+4 ≤ (Hs:ℝ)) (hbudget : sourceShiftBase layers inventory^(Hs+1) ≤ Ds)
  (hr : 0<r) (hq : q ≤ K)

include hDs hpsi hcount hK hHs hbudget hr hq in
theorem mainMass (i : Fin n) : CovarianceSetup.shiftSq ((MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) i).shiftVector ≤ Ds^2 :=
  (MeanMainBatchCoupling.recursive_main_shift M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
    scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq i).2

variable (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
  {F : Point d → ℝ} {ell : ℝ} (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z v,0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (hm : 0<m) (hσ : 0<σ) (hδ : 0<δ) (hcurvature : r^2*ell ≤ 1/2)
  (joint : ∀ i,Kernel (Point d) ((Point d × Tape d ((MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) i).program) × Point d))
  (hmarkov : ∀ i,IsMarkovKernel (joint i))
  (hsource : ∀ i,(joint i).fst=Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L ((MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) i).program))
  (hretained : ∀ i y,(joint i y).map (fun z => (z.1.1,z.2))=stdGaussian (Point d) ⊗ₘ
    (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-1/4)).kernel.comap
      (fun v => (MeanMainBatchCoupling.mainParameters M nodes r σ Ds δ t w ell hr hσ hDs hδ hell hcurvature i y,v))
      measurable_prodMk_left)

def mainLower (k : ℕ) (hk : k<layers) :=
  FreshChildBatchCoupling.Lower.ofRecursiveReference L
    (data M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers r Ds hr hDs (mainMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq) (stage M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers k hk.le).1 (stage_positive M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers k hk))
    hF hell hlo hup M hm t ht (fun _ => q-1/4)
    (fun i y => MeanMainBatchCoupling.mainParameters M nodes r σ Ds δ t w ell hr hσ hDs hδ hell hcurvature i y)
    joint hmarkov hsource hretained

local instance sourcePrefixSpace : MeasurableSpace
    (Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers)) := prefixSpace d _

variable {A : Type*} [MeasurableSpace A]
  (x P referencePosition : A → Point d) (hx : Measurable x) (hP : Measurable P)
  (hreference : Measurable referencePosition)

/-- The actual finite mean-main kernel. All supplier fields are constructed
from the original source program and lower retained-reference IHs. -/
def kernel := MeanChronologicalCoupling.kernel M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers r Ds hr hDs (mainMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq) L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hcurvature δ t w (mainLower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hF hell hlo hup hm hσ hδ hcurvature joint hmarkov hsource hretained)

instance kernel_markov : IsMarkovKernel (kernel M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hL hF hell hlo hup hm hσ hδ hcurvature joint hmarkov hsource hretained x P referencePosition hx hP hreference) := by
  unfold kernel
  infer_instance

theorem kernel_original : (kernel M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hL hF hell hlo hup hm hσ hδ hcurvature joint hmarkov hsource hretained x P referencePosition hx hP hreference).map (original M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers)=Kernel.id :=
  MeanChronologicalCoupling.kernel_original M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers r Ds hr hDs (mainMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq) L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hcurvature δ t w (mainLower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hF hell hlo hup hm hσ hδ hcurvature joint hmarkov hsource hretained)

include hr hσ ht mesh snodes Ds layers in
/-- The row bound is paid by the original prescribed backward partition. -/
theorem actual_rows (hm2 : 2 ≤ m) (hδ1 : δ ≤ 1) (hpsieq : M.psi=δ^(4*t))
    (hhalf : δ^w ≤ 1/2)
    (hback : M.backward=actualKernelInterval M.R (δ^w) M.R_pos M.R_le_half (Real.rpow_pos_of_pos hδ w))
    (i : Fin n) : ∑ j,|M.matrix r σ (nodes i) (nodes j)| ≤ rowBound (m := m) r σ δ t w := by
  let C : RecursiveCall.Source m n ns := ⟨M,nodes,mesh,snodes,Ds,δ,t,w,layers⟩
  rw [nodes.sum_comp (fun j => |M.matrix r σ (nodes i) j|)]
  exact C.matrix_row_le_source_bound hm2 r σ hr.le hσ hδ hδ1 ht.le hpsieq hhalf hback (nodes i)

include hr hσ hδ in
theorem row_pos : 0<rowBound (m := m) r σ δ t w := by
  unfold rowBound
  have hfirst : 0  ≤  256*(m:ℝ)^5*(r/σ) := by positivity
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg hfirst (Real.rpow_pos_of_pos hδ _).le) (by positivity)

/-- The actual terminal paid-final cut, with full original source retained.
No row bound or reference marginal is supplied as a separate certificate. -/
theorem kernel_terminal_laws
    (hm2 : 2 ≤ m) (hδ1 : δ ≤ 1) (hpsieq : M.psi=δ^(4*t)) (hhalf : δ^w ≤ 1/2)
    (hback : M.backward=actualKernelInterval M.R (δ^w) M.R_pos M.R_le_half (Real.rpow_pos_of_pos hδ w))
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers))) [IsProbabilityMeasure ρ]
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers))) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers))) :
    let s := terminalCursor M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers
    let cut := terminalCut M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers
    let : MeasurableSpace (Prefix d cut) := prefixSpace d _
    ∃ (ν : Measure (History (d := d) M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers A × Prefix d cut)),IsProbabilityMeasure ν ∧
      (kernel M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hL hF hell hlo hup hm hσ hδ hcurvature joint hmarkov hsource hretained x P referencePosition hx hP hreference ∘ₘ ρ).map (CausalTailHistory.unpack cut)=
        ν.prod (tapeLaw L (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) s.old s.direct s.saved)) ∧
      ν.map (fun z => (z.1.1,z.1.2.2))=μ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) :=
  MeanChronologicalFinish.kernel_terminalCut_laws M nodes anchors seeds (MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q) (MeanMainBatchCoupling.recursivePrivate M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers r Ds hr hDs (mainMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq) L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hcurvature δ t w (mainLower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r σ q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hF hell hlo hup hm hσ hδ hcurvature joint hmarkov hsource hretained)
    (row_pos (m := m) δ t w r σ hr hσ hδ)
    (actual_rows M nodes mesh snodes Ds δ t w layers ht r σ hr hσ hδ hm2 hδ1 hpsieq hhalf hback) ρ μ hsplit

end AcceleratedLogConcave.Oracle.MeanRecursiveChronologicalCoupling
