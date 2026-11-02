import AcceleratedLogConcave.Numerics.SmoothKernelFirstBounds
import AcceleratedLogConcave.Conditional.Flow.ExtendedLpDerivatives

/-! Lossless identification of positive ordinary derivatives of the smooth
common-seed kernel with the actual canonical material jets. This closes
derivative bookkeeping, while leaving sharp high-order jet estimates explicit. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- This is the unsubtracted momentum jet. At order zero the kernel still
subtracts its reference value; positive orders need no such subtraction. -/
def commonSeedMomentumJet (d : MeanFlowLp.Data ι m) (j : Fin m) (k : ℕ) (t : ℝ) : H d :=
  kernelPullback d j ((KernelFlowLp.smoothData (kernelData d)).momentumJetLp k t)

theorem hasDerivAt_commonSeedMomentumJet (d : MeanFlowLp.Data ι m) (j : Fin m) (k : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    HasDerivAt (commonSeedMomentumJet d j k) (commonSeedMomentumJet d j (k + 1) t) t :=
  (kernelPullback d j).hasFDerivAt.comp_hasDerivAt t
    ((KernelFlowLp.smoothData (kernelData d)).hasDerivAt_momentumJetLp k ht)

theorem iteratedDeriv_commonSeedMomentumJet (d : MeanFlowLp.Data ι m) (j : Fin m) (n k : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    iteratedDeriv n (commonSeedMomentumJet d j k) t = commonSeedMomentumJet d j (k + n) t := by
  have h := Analysis.iteratedDeriv_eq_of_finite_ladder n
    (fun q => commonSeedMomentumJet d j (k + q)) isOpen_Ioo
    (fun q _ u hu => by
      simpa only [Nat.add_assoc] using hasDerivAt_commonSeedMomentumJet d j (k + q) hu) ht
  simpa only [Nat.add_zero] using h

theorem hasDerivAt_smoothKernel_jet (d : MeanFlowLp.Data ι m) (j : Fin m)
    {t : ℝ} (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    HasDerivAt (smoothKernel d j) (commonSeedMomentumJet d j 1 t) t :=
  (kernelPullback d j).hasFDerivAt.comp_hasDerivAt t
    ((KernelFlowLp.smoothData (kernelData d)).hasDerivAt_kernelLp t ht)

theorem iteratedDeriv_smoothKernel_succ (d : MeanFlowLp.Data ι m) (j : Fin m) (n : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    iteratedDeriv (n + 1) (smoothKernel d j) t = commonSeedMomentumJet d j (n + 1) t := by
  rw [iteratedDeriv_succ']
  have he : deriv (smoothKernel d j) =ᶠ[𝓝 t] commonSeedMomentumJet d j 1 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact (hasDerivAt_smoothKernel_jet d j hu).deriv
  exact ((he.iteratedDeriv n).eq_of_nhds).trans
    (by simpa only [Nat.add_comm] using iteratedDeriv_commonSeedMomentumJet d j n 1 ht)

/-- The exact high-order norm required by the receiver is the canonical
actual jet norm, with no extra pullback constant or dimension loss. -/
theorem norm_iteratedDeriv_smoothKernel_succ (d : MeanFlowLp.Data ι m) (j : Fin m) (n : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    ‖iteratedDeriv (n + 1) (smoothKernel d j) t‖ =
      ‖(KernelFlowLp.smoothData (kernelData d)).momentumJetLp (n + 1) t‖ := by
  rw [iteratedDeriv_smoothKernel_succ d j n ht]
  exact norm_kernelPullback d j ((KernelFlowLp.smoothData (kernelData d)).momentumJetLp (n + 1) t)

/-- Both source endpoints are interior to the enlarged construction slab. -/
theorem norm_iteratedDeriv_smoothKernel_source (d : MeanFlowLp.Data ι m) (j : Fin m) (n : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖iteratedDeriv (n + 1) (smoothKernel d j) t‖ =
      ‖(KernelFlowLp.smoothData (kernelData d)).momentumJetLp (n + 1) t‖ :=
  norm_iteratedDeriv_smoothKernel_succ d j n
    (source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht)

end AcceleratedLogConcave.Numerics.MeanResidualBridge
