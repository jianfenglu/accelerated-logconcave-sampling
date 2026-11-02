import AcceleratedLogConcave.Numerics.SmoothKernel
import AcceleratedLogConcave.Numerics.SmoothKernelBoundary

/-! Common-seed smooth replacement for the actual source kernel. The
construction is smooth on a neighborhood of the entire closed source slab;
it only clips time outside a strictly larger positive-variance slab. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

def SmoothKernelReplacementTarget (d : MeanFlowLp.Data ι m) : Prop :=
  let b := backwardEnd d.G.R
  let δ := (1 - b) / 4
  ∃ K : Fin m → ℝ → H d,
    KernelAgreement d K ∧
    (∀ j, ContDiffOn ℝ (m + 2) (K j) (Ioo (-δ) (b + δ))) ∧
    (∀ j, deriv (K j) 0 = 0) ∧
    (∀ j, K j b = 0)

def smoothKernel (d : MeanFlowLp.Data ι m) (j : Fin m) (t : ℝ) : H d :=
  kernelPullback d j (KernelFlowLp.smoothExtensionLp (kernelData d) t)

theorem smoothKernel_agreement (d : MeanFlowLp.Data ι m) : KernelAgreement d (smoothKernel d) := by
  intro j t ht
  rw [smoothKernel, KernelFlowLp.smoothExtensionLp_eq (kernelData d) ht, kernelLp_eq]

theorem contDiffOn_smoothKernel (d : MeanFlowLp.Data ι m) (j : Fin m) (n : ℕ) :
    ContDiffOn ℝ n (smoothKernel d j)
      (Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :=
  (kernelPullback d j).contDiff.comp_contDiffOn
    (KernelFlowLp.contDiffOn_smoothExtensionLp (kernelData d) n)

/-- The reviewed qualitative replacement target, under the original Data.
This theorem makes no factorial or dimension-sharp derivative-budget claim. -/
theorem smoothKernelReplacementTarget (d : MeanFlowLp.Data ι m) :
    SmoothKernelReplacementTarget d := by
  refine ⟨smoothKernel d, smoothKernel_agreement d, ?_, ?_, ?_⟩
  · intro j
    exact (contDiffOn_smoothKernel d j (m + 2)).mono
      (neighborhood_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one)
  · intro j
    apply kernel_deriv_zero_of_agreement d (smoothKernel_agreement d) j
    have hzero : (0 : ℝ) ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R)) :=
      source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ⟨le_rfl, d.G.backwardEnd_pos.le⟩
    exact ((contDiffOn_smoothKernel d j (m + 2)).contDiffAt
      (isOpen_Ioo.mem_nhds hzero)).differentiableAt (by exact_mod_cast (show m + 2 ≠ 0 by omega))
  · exact kernel_terminal_zero_of_agreement d (smoothKernel_agreement d)

end AcceleratedLogConcave.Numerics.MeanResidualBridge
