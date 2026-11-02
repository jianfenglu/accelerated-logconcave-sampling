import AcceleratedLogConcave.Oracle.PrivateRecursiveBatchBudget
import AcceleratedLogConcave.Oracle.PrivateFinalCoupling

/-! The literal fresh final private batch of the source-specialized executable recursion.
Every final geometric/shift guard is proved from the public source budget. Lower
reference marginals are derived from the lower retained-reference identities
and the actual recursive reference invariant, at the original potential. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateRecursiveFinalCoupling
open Numerics.AffineGraph TapeLowering CanonicalTapeMeasurability CanonicalTapeLaw
open RecursiveExecutable PrivateRecursiveBatchBudget

local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
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
  (hr : 0 < r) (hq : q ≤ K) {Γ : Ctx} (old : Fin ns → Ref Γ .point)

local notation "smain" => main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q
local notation "sfinal" => final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q
local notation "S" => privateGeometry M mesh

/-- All privateData guards are supplied by the actual lower recursive shift
theorem and concrete source geometry; no child-mass hypothesis is accepted. -/
def data :=
  PrivateFinalCoupling.data S snodes r Ds smain sfinal layers hr hDs
    (fun i => (final_queryShift_and_mass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
      scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq i).2) old

local notation "B" => data M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q K
  hDs hpsi inventory Hs hcount hK hHs hbudget hr hq old

@[simp] theorem data_child (i : Fin ns) : (B).child i = sfinal i := rfl

variable (L : PrimitiveLaws d) {F : Point d → ℝ} {ell : ℝ}
  (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell * ‖v‖^2)
  (hm : 0 < m) (hcurvature : r^2*ell ≤ 1/2)

/-- Exact lower retained law is the induction input. The Gaussian batch
invariant is then constructed, with precision q−1/4 and actual positive child
reference parameters, also when that lower precision is terminal. -/
def lower
    (joint : ∀ i, Kernel (Point d) ((Point d × Tape d (sfinal i).program) × Point d))
    (hmarkov : ∀ i, IsMarkovKernel (joint i))
    (hsource : ∀ i, (joint i).fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw L (sfinal i).program))
    (hretained : ∀ i x, (joint i x).map (fun z => (z.1.1,z.2)) = stdGaussian (Point d) ⊗ₘ
      (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-1/4)).kernel.comap
        (fun v => (finalParameters S snodes r ell hr hell hcurvature i x,v))
        measurable_prodMk_left) : FreshChildBatchCoupling.Lower L B :=
  FreshChildBatchCoupling.Lower.ofRecursiveReference L B hF hell hlo hup M hm t ht
    (fun _ => q-1/4)
    (fun i x => finalParameters S snodes r ell hr hell hcurvature i x)
    joint hmarkov hsource hretained

end AcceleratedLogConcave.Oracle.PrivateRecursiveFinalCoupling
