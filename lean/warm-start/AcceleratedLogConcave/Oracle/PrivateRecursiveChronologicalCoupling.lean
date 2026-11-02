import AcceleratedLogConcave.Oracle.PrivateChronologicalFinish
import AcceleratedLogConcave.Oracle.PrivateRecursiveFinalCoupling

/-! Source specialization of the constructed finite private chronology.
Actual lower programs have precision q−1/4. All occurrence covariance and shift
guards are paid by the original public source budget. The only probabilistic
inputs are standalone LOWER retained couplings at the original potential. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateRecursiveChronologicalCoupling
open Numerics.AffineGraph TapeLowering CanonicalTapeMeasurability CanonicalTapeLaw
open RecursiveExecutable PrivateRecursiveBatchBudget PrivateChronologicalCoupling
open TailOccurrenceCut TailCut

local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

variable {d m n a h ns : ℕ}
  (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
  (snodes : Fin ns ≃ mesh.Source m)
  (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4)
  (scale r q K : ℝ) (hDs : 0 < Ds) (hpsi : M.psi ≤ M.R^4)
  (inventory Hs : ℕ) (hcount : n+ns ≤ inventory) (hK : (1/2:ℝ) < K)
  (hHs : 8*K+4 ≤ (Hs:ℝ))
  (hbudget : sourceShiftBase layers inventory ^ (Hs+1) ≤ Ds)
  (hr : 0 < r) (hq : q ≤ K)


include hDs hpsi hcount hK hHs hbudget hr hq in
theorem mainMass (i : Fin ns) : CovarianceSetup.shiftSq ((PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) i).shiftVector ≤ Ds^2 :=
  (main_queryShift_and_mass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
    scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq i).2

include hDs hpsi hcount hK hHs hbudget hr hq in
theorem finalMass (i : Fin ns) : CovarianceSetup.shiftSq ((PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) i).shiftVector ≤ Ds^2 :=
  (final_queryShift_and_mass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
    scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq i).2


variable (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} {ell : ℝ}
  (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (hm : 0 < m) (hcurvature : r^2*ell ≤ 1/2)
  (joint : ∀ i, Kernel (Point d) ((Point d × Tape d ((PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) i).program) × Point d))
  (hmarkov : ∀ i, IsMarkovKernel (joint i))
  (hsource : ∀ i, (joint i).fst = Kernel.const (Point d)
    (FreshChildRetainedCoupling.sourceLaw L ((PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) i).program))
  (hretained : ∀ i x, (joint i x).map (fun z => (z.1.1,z.2)) = stdGaussian (Point d) ⊗ₘ
    (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-1/4)).kernel.comap
      (fun v => (mainParameters (privateGeometry M mesh) snodes r Ds ell hm hr hDs hell hcurvature i x,v))
      measurable_prodMk_left)

/-- Lower disintegrations are instantiated at each actually reached main
batch. Gaussian lower-reference invariance is derived, never another IH. -/
def mainLower (k : ℕ) (hk : k<layers) :=
  recursiveLower (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers hr hDs (mainMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq) L hF hell hlo hup
    M hm t ht (fun _ => q-1/4)
    (mainParameters (privateGeometry M mesh) snodes r Ds ell hm hr hDs hell hcurvature)
    joint hmarkov hsource hretained (stage (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers k hk.le).1
    (stage_positive (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers k hk)


/-- The literal source-specialized finite private kernel, jointly in center.
No arbitrary batch conditional, Gaussian law certificate, or parent accuracy
bound is accepted. All original seed coordinates remain in its output. -/
def kernel :=
  PrivateChronologicalCoupling.kernel (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers hr hDs (mainMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq) L hL
    hF hell hlo hup (mainLower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hF hell hlo hup hm hcurvature joint hmarkov hsource hretained)


instance kernel_markov : IsMarkovKernel (kernel M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hL hF hell hlo hup hm hcurvature joint hmarkov hsource hretained) := by
  unfold kernel
  infer_instance

theorem kernel_original (x : Point d) :
    ((kernel M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hL hF hell hlo hup hm hcurvature joint hmarkov hsource hretained) x).map (original (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers) =
      (FreshChildRetainedCoupling.sourceLaw L (Host (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers)).map
        (fun z => ((x,z.1),z.2)) :=
  PrivateChronologicalCoupling.kernel_original (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers hr hDs (mainMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq) L hL
    hF hell hlo hup (mainLower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hF hell hlo hup hm hcurvature joint hmarkov hsource hretained) x

theorem kernel_terminal_laws (x : Point d) :
    let s := terminalCursor (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers
    let cut := terminalCut (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers
    let : MeasurableSpace (Prefix d cut) := prefixSpace d _
    ∃ (μ : Measure (History d layers ns × Prefix d cut)), IsProbabilityMeasure μ ∧
      ((kernel M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hL hF hell hlo hup hm hcurvature joint hmarkov hsource hretained) x).map (CausalTailHistory.unpack cut) =
        μ.prod (tapeLaw L (PrivateSamplingExecutionSchedule.finisher (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers s.old s.direct s.saved)) ∧
      μ.map (fun z => (z.1.1,z.1.2.2)) =
        (PrivateChronologicalLaws.coarseLaw x).prod
          (Measure.pi fun _ : Fin ns => stdGaussian (Point d)) :=
  PrivateChronologicalFinish.kernel_terminalCut_laws (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers hr hDs (mainMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq) L hL
    hF hell hlo hup (mainLower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq L hF hell hlo hup hm hcurvature joint hmarkov hsource hretained) hm x

/-- Actual fresh final lower batch at the reached finite cursor. Its guards
and lower reference parameters use finalWidth and the same precision q−1/4. -/
def finalLower
    (finalJoint : ∀ i, Kernel (Point d) ((Point d × Tape d ((PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) i).program) × Point d))
    (hfinalMarkov : ∀ i, IsMarkovKernel (finalJoint i))
    (hfinalSource : ∀ i, (finalJoint i).fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw L ((PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) i).program))
    (hfinalRetained : ∀ i x, (finalJoint i x).map (fun z => (z.1.1,z.2)) = stdGaussian (Point d) ⊗ₘ
      (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-1/4)).kernel.comap
        (fun v => (finalParameters (privateGeometry M mesh) snodes r ell hr hell hcurvature i x,v)) measurable_prodMk_left) :=
  PrivateRecursiveFinalCoupling.lower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
    scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq
    (terminalCursor (privateGeometry M mesh) snodes r Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q) layers).old L hF hell hlo hup hm hcurvature
    finalJoint hfinalMarkov hfinalSource hfinalRetained
end AcceleratedLogConcave.Oracle.PrivateRecursiveChronologicalCoupling
