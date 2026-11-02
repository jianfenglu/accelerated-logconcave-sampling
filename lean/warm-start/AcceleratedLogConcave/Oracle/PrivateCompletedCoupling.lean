import AcceleratedLogConcave.Oracle.PrivateChronologicalCoupling
import AcceleratedLogConcave.Oracle.PrivateRecursiveFinalCoupling
import AcceleratedLogConcave.Oracle.PrivateReferenceAssembly

/-! Append the actual fresh final children to the constructed finite private
chronology. The full original standalone seed stays in the state. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateCompletedCoupling
open Numerics.AffineGraph TapeLowering CanonicalTapeLaw CanonicalTapeMeasurability
open TailOccurrenceCut TailCut PrivateChronologicalCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (hfinalMass : ∀ i, CovarianceSetup.shiftSq (final i).shiftVector ≤ Ds^2)
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
local notation "s" => terminalCursor S e r Ds main final N
local notation "cut" => terminalCut S e r Ds main final N
local notation "B" => PrivateFinalCoupling.data S e r Ds main final N hr hDs hfinalMass (terminalCursor S e r Ds main final N).old
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance : MeasurableSpace (Prefix d (PrivateCausalLayer.afterBatch cut)) := prefixSpace d _

variable (Jf : FreshChildBatchCoupling.Lower L
  (PrivateFinalCoupling.data S e r Ds main final N hr hDs hfinalMass (terminalCursor S e r Ds main final N).old))

/-- The actual final conditional reads only consumed history and final tapes. -/
def finalConditional : Kernel
    (History d N n × Prefix d (PrivateCausalLayer.afterBatch cut)) (Fin n → Point d) :=
  PrivateFinalCoupling.referenceConditional S e r Ds main final N hr hDs hfinalMass
    (terminalCursor S e r Ds main final N).old
    ((terminalCursor S e r Ds main final N).saved (RefMap.shiftMany n .here)) cut
    L hL Jf (fun z => z.1.1.1) (by fun_prop)
    (jointPhi S e hF hell hlo hup hr) (fun i => (jointPhi_continuous S e hF hell hlo hup hr i).measurable)
    (fun i z => z.1.2.2 i) (by intro i; fun_prop)

instance finalConditional_markov : IsMarkovKernel
    (finalConditional S e r Ds main final N hr hDs hfinalMass L hL hF hell hlo hup Jf) := by
  unfold finalConditional
  infer_instance

/-- Keep the full original seed and adjoin only the final returned references. -/
def finalKernel : Kernel (History d N n × Tape d (Host S e r Ds main final N))
    ((History d N n × Tape d (Host S e r Ds main final N)) × (Fin n → Point d)) :=
  CausalTailHistory.onTape L (PrivateCausalLayer.afterBatch cut)
    (finalConditional S e r Ds main final N hr hDs hfinalMass L hL hF hell hlo hup Jf)

instance finalKernel_markov : IsMarkovKernel
    (finalKernel S e r Ds main final N hr hDs hfinalMass L hL hF hell hlo hup Jf) := by
  unfold finalKernel
  infer_instance

theorem finalKernel_original :
    (finalKernel S e r Ds main final N hr hDs hfinalMass L hL hF hell hlo hup Jf).fst = Kernel.id := by
  unfold finalKernel
  exact CausalTailHistory.onTape_original L (PrivateCausalLayer.afterBatch cut) _

variable (J : ∀ (k : ℕ) (hk : k<N), FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk)))

/-- Complete finite private reference augmentation, including the paid final
children, jointly measurable in the external center and without redrawing seed. -/
def kernel : Kernel (Point d)
    ((History d N n × Tape d (Host S e r Ds main final N)) × (Fin n → Point d)) :=
  finalKernel S e r Ds main final N hr hDs hfinalMass L hL hF hell hlo hup Jf ∘ₖ
    PrivateChronologicalCoupling.kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J

instance kernel_markov : IsMarkovKernel
    (kernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J) := by
  unfold kernel
  infer_instance

theorem kernel_prior :
    (kernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J).fst =
      PrivateChronologicalCoupling.kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J := by
  rw [Kernel.fst_eq,kernel,Kernel.map_comp,← Kernel.fst_eq,finalKernel_original,Kernel.id_comp]

/-- Complete original parent input and source tape marginal, jointly with
external center, after every main layer and every actual final child. -/
theorem kernel_original (x : Point d) :
    (kernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x).map
      (fun z => original S e r Ds main final N z.1) =
        (FreshChildRetainedCoupling.sourceLaw L (Host S e r Ds main final N)).map
          (fun z => ((x,z.1),z.2)) := by
  have hp := congrArg (fun k => k x)
    (kernel_prior S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J)
  change (kernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x).map
    Prod.fst = _ at hp
  change Measure.map ((original S e r Ds main final N) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (original_measurable S e r Ds main final N) measurable_fst,hp]
  exact PrivateChronologicalCoupling.kernel_original S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x

end AcceleratedLogConcave.Oracle.PrivateCompletedCoupling
