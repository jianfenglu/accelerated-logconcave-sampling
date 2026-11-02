import AcceleratedLogConcave.Numerics.MeanResidualBridge

/-! Endpoint adapter for the actual common-space kernel. A smooth
slab-equal replacement inherits the zero derivative at the left endpoint from
one-sided uniqueness. Ordinary differentiability is essential at that point. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

theorem kernel_deriv_zero_of_agreement (d : MeanFlowLp.Data ι m)
    {K : Fin m → ℝ → H d} (hK : KernelAgreement d K)
    (j : Fin m) (hd : DifferentiableAt ℝ (K j) 0) : deriv (K j) 0 = 0 := by
  have hx : (0 : ℝ) ∈ Icc 0 (backwardEnd d.G.R) :=
    ⟨le_rfl, d.G.backwardEnd_pos.le⟩
  have hu := uniqueDiffOn_Icc d.G.backwardEnd_pos 0 hx
  have hh : HasDerivWithinAt (K j) 0 (Icc 0 (backwardEnd d.G.R)) 0 := by
    simpa only [mul_zero, zero_smul] using
      (hasDerivAt_kernelLp d j 0).hasDerivWithinAt.congr_of_mem (hK j) hx
  exact (hd.hasDerivAt.hasDerivWithinAt.derivWithin hu).symm.trans (hh.derivWithin hu)

theorem kernel_terminal_zero_of_agreement (d : MeanFlowLp.Data ι m)
    {K : Fin m → ℝ → H d} (hK : KernelAgreement d K) (j : Fin m) :
    K j (backwardEnd d.G.R) = 0 := by
  rw [hK j _ ⟨d.G.backwardEnd_pos.le, le_rfl⟩]
  exact (kernelBoundary d).2 j

end AcceleratedLogConcave.Numerics.MeanResidualBridge
